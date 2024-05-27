use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Write,
    path::{Path, PathBuf},
};

use compile_util::{make_suggestion, span_to_snippet};
use etrace::{ok_or, some_or};
use must_analysis::Obj;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::{BindingAnnotation, Mutability};
use rustc_hir::{
    def::Res,
    definitions::DefPathDataName,
    intravisit::{self, Visitor as HVisitor},
    ByRef, Expr, ExprKind, ItemKind, Node, PatKind, QPath, StmtKind, UnOp, VariantData,
};
use rustc_index::{bit_set::BitSet, IndexVec};
use rustc_middle::{
    hir::nested_filter,
    mir::{
        visit::{MutatingUseContext, PlaceContext, Visitor as MVisitor},
        AggregateKind, ConstantKind, HasLocalDecls, Local, LocalDecl, Location, Operand, Place,
        PlaceElem, ProjectionElem, Rvalue, Terminator, TerminatorKind,
    },
    ty::{List, Ty, TyCtxt, TyKind, TypeAndMut, TypeckResults},
};
use rustc_session::config::Input;
use rustc_span::{def_id::LocalDefId, source_map::SourceMap, BytePos, Span, Symbol};
use rustfix::Suggestion;
use typed_arena::Arena;

use self::must_analysis::{AbsInt, AbsMem, AccPath};
use crate::*;

#[derive(Debug, Clone)]
pub struct Config {
    pub solutions: Option<may_analysis::Solutions>,
    pub unions: HashSet<String>,
    pub transform: bool,
}

pub fn analyze_path(path: &Path, conf: &Config) {
    analyze_input(compile_util::path_to_input(path), conf)
}

pub fn analyze_str(code: &str, conf: &Config) {
    analyze_input(compile_util::str_to_input(code), conf)
}

fn analyze_input(input: Input, conf: &Config) {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| analyze(tcx, conf)).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>, conf: &Config) {
    let hir = tcx.hir();
    let source_map = tcx.sess.source_map();

    let visitor = ty_finder::TyVisitor::new(tcx);
    let (local_tys, foreign_tys) = visitor.find_foreign_tys(tcx);
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx);
    let pre = may_analysis::pre_analyze(&tss, tcx);
    let solutions = conf
        .solutions
        .clone()
        .unwrap_or_else(|| may_analysis::analyze(&pre, &tss, tcx));
    let may_points_to = may_analysis::post_analyze(pre, solutions, &tss, tcx);

    let mut non_tag_fields = HashMap::new();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        let body_id = match item.kind {
            ItemKind::Fn(_, _, body_id) | ItemKind::Static(_, _, body_id) => body_id,
            _ => continue,
        };
        let body = hir.body(body_id);
        let typeck = tcx.typeck(item_id.owner_id.def_id);
        let mut visitor = FieldVisitor {
            tcx,
            typeck,
            fields: &mut non_tag_fields,
        };
        visitor.visit_body(body);
    }
    let non_tag_fields: HashMap<_, HashSet<_>> = non_tag_fields
        .into_iter()
        .map(|(s, symbols)| {
            let item = hir.expect_item(s);
            let ItemKind::Struct(VariantData::Struct(fs, _), _) = item.kind else { unreachable!() };
            let fields = symbols
                .into_iter()
                .map(|sym| {
                    fs.iter()
                        .enumerate()
                        .find(|(_, f)| f.ident.name == sym)
                        .map(|(i, _)| FieldIdx::from_usize(i))
                        .unwrap()
                })
                .collect();
            (s, fields)
        })
        .collect();

    let mut structs = HashMap::new();
    let mut unions = vec![];
    let mut union_to_struct = HashMap::new();
    let mut ty_graph: HashMap<_, Vec<_>> = HashMap::new();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        let local_def_id = item_id.owner_id.def_id;

        if local_tys.contains(&local_def_id)
            && matches!(item.kind, ItemKind::Struct(_, _) | ItemKind::Union(_, _))
        {
            let adt_def = tcx.adt_def(local_def_id);
            let variant = adt_def.variant(VariantIdx::from_u32(0));
            for (i, field) in variant.fields.iter_enumerated() {
                let ty = field.ty(tcx, List::empty());
                let (ty, mut v) = some_or!(ty_to_proj(ty), continue);
                if local_tys.contains(&ty) {
                    v.push(AccElem::Field(i));
                    ty_graph.entry(ty).or_default().push((local_def_id, v));
                }
            }
        }

        if !matches!(item.kind, ItemKind::Struct(_, _)) {
            continue;
        }
        if foreign_tys.contains(&local_def_id) {
            continue;
        }
        let adt_def = tcx.adt_def(local_def_id);
        let variant = adt_def.variant(VariantIdx::from_u32(0));
        let non_tag_fields = non_tag_fields.get(&local_def_id);
        let mut int_fields: HashSet<_> = variant
            .fields
            .iter_enumerated()
            .filter(|(i, f)| {
                let ty = f.ty(tcx, List::empty());
                (ty.is_integral() || ty.is_bool())
                    && non_tag_fields.map_or(true, |fields| !fields.contains(i))
            })
            .map(|(i, _)| i)
            .collect();
        if let Some(bitfield) = tss.bitfields.get(&local_def_id) {
            int_fields.extend(bitfield.fields.keys());
        }
        if int_fields.is_empty() {
            continue;
        }
        let mut struct_unions = vec![];
        for (i, f) in variant.fields.iter_enumerated() {
            let TyKind::Adt(adt_def, _) = f.ty(tcx, List::empty()).kind() else { continue };
            if !adt_def.is_union() {
                continue;
            }
            let def_id = adt_def.did();
            let name = tcx.def_path(def_id).data.last().unwrap().data.name();
            let DefPathDataName::Named(name) = name else { continue };
            if !name.to_ident_string().starts_with("C2RustUnnamed") {
                continue;
            }
            let u = def_id.expect_local();
            if conf.unions.is_empty()
                || conf
                    .unions
                    .contains(&tcx.def_path(u.to_def_id()).to_string_no_crate_verbose())
            {
                unions.push(u);
                union_to_struct.insert(u, (i, local_def_id));
                struct_unions.push((i, u));
            }
        }
        if !struct_unions.is_empty() {
            let info = StructInfo {
                int_fields,
                unions: struct_unions,
            };
            structs.insert(local_def_id, info);
        }
    }

    if unions.is_empty() {
        println!("No candidates");
        return;
    }
    println!("{} candidates:", unions.len());
    for u in &unions {
        println!("{:?}", u);
    }

    let paths_to_unions: Vec<_> = unions
        .iter()
        .map(|u| {
            let mut ps = HashMap::new();
            find_paths(*u, &mut vec![], &ty_graph, &mut HashSet::new(), &mut ps);
            (*u, ps)
        })
        .collect();

    let mut union_uses: HashMap<_, UnionUse> = HashMap::new();
    let mut aggregates: HashMap<_, _> = HashMap::new();
    let mut field_values: HashMap<FieldAt, BTreeSet<Tag>> = HashMap::new();
    println!("Start analysis");
    for item_id in hir.items() {
        let item = hir.item(item_id);
        let local_def_id = item_id.owner_id.def_id;
        let (body_id, body) = match item.kind {
            ItemKind::Fn(_, _, body_id) => (body_id, tcx.optimized_mir(local_def_id)),
            ItemKind::Static(_, _, body_id) => (body_id, tcx.mir_for_ctfe(local_def_id)),
            _ => continue,
        };
        let hbody = hir.body(body_id);
        let mut visitor = MBodyVisitor::new(tcx, &body.local_decls, &structs, &unions);
        visitor.visit_body(body);
        let mut hvisitor = BitFieldInitVisitor::new(tcx);
        hvisitor.visit_body(hbody);
        if !hvisitor.inits.is_empty() {
            for (local, location) in &visitor.inits {
                let span = body
                    .stmt_at(*location)
                    .either(|stmt| stmt.source_info.span, |term| term.source_info.span);
                let aggregate_span = some_or!(hvisitor.inits.get(&span), continue);
                aggregates.insert(*aggregate_span, (*local, *location));
            }
        }
        if visitor.accesses.is_empty()
            && visitor.struct_accesses.is_empty()
            && visitor.aggregates.is_empty()
        {
            continue;
        }
        for (local, location) in visitor.aggregates.values().flatten() {
            let span = body
                .stmt_at(*location)
                .either(|stmt| stmt.source_info.span, |term| term.source_info.span);
            aggregates.entry(span).or_insert((*local, *location));
        }
        for a in &visitor.accesses {
            union_uses.entry(a.ty).or_default().insert_field(a.field);
        }
        let local_set: HashSet<_> = visitor
            .accesses
            .iter()
            .map(|a| a.local)
            .chain(visitor.struct_accesses.iter().copied())
            .chain(
                visitor
                    .aggregates
                    .values()
                    .flatten()
                    .map(|(local, _)| *local),
            )
            .collect();
        let mut locals = BitSet::new_empty(body.local_decls.len());
        for l in local_set {
            locals.insert(l);
        }
        let mut local_to_unions: HashMap<_, Vec<_>> = HashMap::new();
        for i in locals.iter() {
            let local = &body.local_decls[i];
            let (local_def_id, elems) = some_or!(ty_to_proj(local.ty), continue);
            for (u, paths) in &paths_to_unions {
                let paths = some_or!(paths.get(&local_def_id), continue);
                let local_to_unions = local_to_unions.entry(*u).or_default();
                for p in paths {
                    let mut path: Vec<_> = elems.iter().copied().rev().collect();
                    path.extend(p);
                    local_to_unions.push((i, path));
                }
            }
        }
        println!("{:?}", local_def_id);
        let ctx = must_analysis::AnalysisContext {
            local_def_id,
            tss: &tss,
            may_points_to: &may_points_to,
            no_gc_locals: Some(&locals),
            gc: true,
        };
        let states = must_analysis::analyze_body(body, ctx, tcx);
        for access in visitor.accesses {
            if matches!(
                access.ctx,
                PlaceContext::MutatingUse(MutatingUseContext::Store)
            ) {
                continue;
            }
            let span = body.source_info(access.location).span;
            let tags = compute_tags(access, &states.states, &body.local_decls, tcx);
            for (f, ns) in tags {
                let vts = union_uses
                    .entry(access.ty)
                    .or_default()
                    .get_access_tags_mut(f);
                for n in ns.into_set() {
                    vts.insert(access.field, n, span);
                }
            }
        }
        for (loc, mem) in states.states.iter().chain(states.out_states.iter()) {
            let Location {
                block,
                statement_index,
            } = *loc;
            let span = body.source_info(*loc).span;
            let g = mem.g();
            for (u, paths) in &local_to_unions {
                for (l, path) in paths {
                    let len = path.len();
                    let AccElem::Field(f) = path[len - 1] else { unreachable!() };
                    let objs = g.objs_at(*l, &path[..len - 1]);
                    for obj in objs {
                        let Obj::Struct(fs, _) = obj else { continue };
                        let v: Vec<_> = fs
                            .iter()
                            .filter_map(|(f, obj)| {
                                let Obj::Ptr(loc) = obj else { return None };
                                let obj = g.obj_at_location(loc)?;
                                let Obj::AtAddr(n) = obj else { return None };
                                Some((*f, n.clone()))
                            })
                            .collect();
                        for (f, n) in &v {
                            union_uses.entry(*u).or_default().insert_tags(*f, n.iter());
                            let field_at = FieldAt {
                                func: local_def_id,
                                location: *loc,
                                local: *l,
                                field: *f,
                            };
                            field_values
                                .entry(field_at)
                                .or_default()
                                .extend(n.iter().filter_map(|n| n.try_into().ok()).map(Tag));
                        }
                        if body.basic_blocks[block].statements.len() > statement_index {
                            continue;
                        }
                        let terminator = body.basic_blocks[block].terminator();
                        if hvisitor.set_exprs.contains(&terminator.source_info.span) {
                            continue;
                        }
                        let uv = fs
                            .get(&f)
                            .map(|obj| {
                                let Obj::Struct(fs, _) = obj else { return vec![] };
                                fs.keys().cloned().collect()
                            })
                            .unwrap_or_default();
                        if uv.len() == 1 {
                            let variant = uv[0];
                            for (f, ns) in &v {
                                let vts = union_uses.entry(*u).or_default().get_obj_tags_mut(*f);
                                for n in ns.into_set() {
                                    vts.insert(variant, n, span);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    println!("Analysis done");

    let mut tagged_unions = HashMap::new();
    for (u, uu) in &union_uses {
        let (index_in_struct, struct_local_def_id) = union_to_struct[u];
        let int_fields = &structs[&struct_local_def_id].int_fields;
        if let Some((tag_index, mut variant_tags)) = uu.compute_tags(int_fields) {
            println!("Union {:?}", u);
            println!("Used fields: {:?}", uu.fields);
            println!("Tag field: {:?}", tag_index);
            let mut all_fields = uu.fields.clone();
            let mut all_tags = uu.tags[&tag_index].clone();
            for (variant, tags) in &variant_tags {
                for v in tags {
                    all_tags.remove(v);
                }
                println!("  {:?}: {:?}", variant, tags);
                all_fields.remove(variant);
            }
            let mut empty_tags = vec![];
            if !all_tags.is_empty() {
                println!("  {:?}: {:?}", all_fields, all_tags);
                assert!(all_fields.len() <= 1, "{:?} {:?}", all_fields, all_tags);
                let tags = all_tags.into_iter().collect();
                if let Some(variant) = all_fields.into_iter().next() {
                    variant_tags.insert(variant, tags);
                } else {
                    empty_tags.extend(tags);
                }
            }

            let item = hir.expect_item(*u);
            let name = item.ident.name.to_ident_string();
            let ItemKind::Union(VariantData::Struct(fs, _), _) = item.kind else { unreachable!() };
            let field_name_to_index = fs
                .iter()
                .enumerate()
                .map(|(i, f)| (f.ident.name.to_ident_string(), FieldIdx::from_usize(i)))
                .collect();
            let tu = TaggedUnion {
                local_def_id: *u,
                name,
                variant_tags,
                empty_tags,
                field_name_to_index,
                struct_local_def_id,
                index_in_struct,
                tag_index,
            };
            tagged_unions.insert(*u, tu);
        } else {
            tracing::info!("Union {:?}", u);
            tracing::info!("Used fields: {:?}", uu.fields);
            tracing::info!("Tags: {:?}", uu.tags);
            tracing::info!("Access:");
            for (f, vts) in &uu.access_tags {
                tracing::info!("  Field {:?}", f);
                for (variant, vs) in &vts.tags {
                    tracing::info!("    Variant {:?}", variant);
                    for (n, spans) in vs {
                        tracing::info!("      Tag {}", n);
                        for span in spans {
                            tracing::info!("        {:?}", span);
                        }
                    }
                }
            }
            tracing::info!("Obj:");
            for (f, vts) in &uu.obj_tags {
                tracing::info!("  Field {:?}", f);
                for (variant, vs) in &vts.tags {
                    tracing::info!("    Variant {:?}", variant);
                    for (n, spans) in vs {
                        tracing::info!("      Tag {}", n);
                        for span in spans {
                            tracing::info!("        {:?}", span);
                        }
                    }
                }
            }
        }
    }

    if tagged_unions.is_empty() {
        println!("No tagged union identified");
        return;
    }
    println!("{} tagged unions identified", tagged_unions.len());

    let mut tagged_structs = HashMap::new();
    for (u, tu) in &tagged_unions {
        let s = tu.struct_local_def_id;
        let ts = tagged_structs.entry(s).or_insert_with(|| {
            let item = hir.expect_item(s);
            let name = item.ident.name.to_ident_string();
            let ItemKind::Struct(VariantData::Struct(fs, _), _) = item.kind else { unreachable!() };
            let mut field_names: IndexVec<FieldIdx, _> =
                fs.iter().map(|f| f.ident.name.to_ident_string()).collect();
            if let Some(bitfield) = tss.bitfields.get(&s) {
                for _ in 0..bitfield.fields.len() {
                    let (name, _) = &bitfield.fields[&field_names.next_index()];
                    field_names.push(name.clone());
                }
            }
            TaggedStruct {
                local_def_id: s,
                name,
                tag_index: tu.tag_index,
                field_names,
                unions: vec![],
            }
        });
        assert_eq!(ts.tag_index, tu.tag_index);
        ts.unions.push((*u, tu.index_in_struct));
    }

    let mut suggestions = Suggestions::new(source_map);
    for (s, ts) in &tagged_structs {
        let item = hir.expect_item(*s);
        let ItemKind::Struct(VariantData::Struct(sfs, _), _) = item.kind else { unreachable!() };

        let (field_name, field_ty) = if let Some(field) = sfs.get(ts.tag_index.as_usize()) {
            let span = source_map.span_extend_to_line(field.span);
            suggestions.add(span, "".to_string());

            let field_name = field.ident.name.to_ident_string();
            let field_ty = source_map.span_to_snippet(field.ty.span).unwrap();
            (field_name, field_ty)
        } else {
            let (name, ty) = tss.bitfields[&s].fields[&ts.tag_index].clone();
            let mut lo = item.ident.span.hi() + BytePos(3);
            'l: for f in sfs {
                loop {
                    let span = source_map.span_extend_to_line(f.span.with_lo(lo).with_hi(lo));
                    let code = source_map.span_to_snippet(span).unwrap();
                    if code.contains(&format!("#[bitfield(name = \"{}\"", name)) {
                        suggestions.add(span, "".to_string());
                        break 'l;
                    }
                    lo = span.hi() + BytePos(1);
                    if span.hi() >= f.span.hi() {
                        break;
                    }
                }
            }
            (name, ty)
        };

        let mut set_tag_method = format!(
            "
impl {} {{
    pub fn set_{}(&mut self, v: {}) {{",
            ts.name, field_name, field_ty,
        );
        for (n, (u, i)) in ts.unions.iter().enumerate() {
            let is_first_union = n == 0;
            let tu = &tagged_unions[u];
            let struct_field_name = &ts.field_names[*i];
            let item = hir.expect_item(*u);
            let ItemKind::Union(VariantData::Struct(ufs, _), _) = item.kind else { unreachable!() };
            let tys: Vec<_> = ufs
                .iter()
                .map(|f| source_map.span_to_snippet(f.ty.span).unwrap().to_string())
                .collect();

            write!(
                &mut set_tag_method,
                "
        self.{} = match v {{",
                struct_field_name
            )
            .unwrap();
            let mut new_method = format!(
                "impl {} {{
    pub fn new(t: {}) -> Self {{
        match t {{",
                tu.name, field_ty,
            );
            let mut get_tag_method = format!(
                "impl {} {{
    pub fn {}(self) -> {} {{
        match self.{} {{",
                ts.name, field_name, field_ty, struct_field_name
            );
            let mut field_methods = "".to_string();
            let mut enum_str = format!("pub enum {} {{", tu.name);
            for (field, tags) in &tu.variant_tags {
                let field_name = ufs[field.as_usize()].ident.name.to_ident_string();
                let ty = &tys[field.as_usize()];
                let pattern: String = tags
                    .iter()
                    .map(|tag| format!("{}::{}{}(v)", tu.name, field_name, tag))
                    .intersperse(" | ".to_string())
                    .collect();
                writeln!(
                    &mut field_methods,
                    "impl {} {{
    pub fn get_{}(self) -> {} {{
        if let {} = self {{
            v
        }} else {{
            panic!()
        }}
    }}
}}",
                    tu.name, field_name, ty, pattern,
                )
                .unwrap();
                if tags.len() == 1 {
                    let t = tags[0];
                    writeln!(
                        &mut field_methods,
                        "impl {} {{
    pub fn deref_{}_mut(&mut self) -> *mut {} {{
        if !matches!(self, {}) {{
            let v = unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }};
            *self = Self::{}{}(v);
        }}
        if let {} = self {{
            v as _
        }} else {{
            panic!()
        }}
    }}
}}",
                        tu.name, field_name, ty, pattern, ty, field_name, t, pattern,
                    )
                    .unwrap();
                } else {
                    let mut arms = "".to_string();
                    for t in tags {
                        write!(
                            &mut arms,
                            "
                {} => {}::{}{}(v),",
                            tag_to_string(*t, &field_ty),
                            tu.name,
                            field_name,
                            t
                        )
                        .unwrap();
                    }
                    let default = format!("{}::{}{}(v)", tu.name, field_name, tags[0],);
                    writeln!(
                        &mut field_methods,
                        "impl {} {{
    pub fn deref_{}_mut(&mut self, t: {}) -> *mut {} {{
        if !matches!(self, {}) {{
            let v = unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }};
            *self = match t {{{}
                _ => {},
            }};
        }}
        if let {} = self {{
            v as _
        }} else {{
            panic!()
        }}
    }}
}}",
                        tu.name, field_name, field_ty, ty, pattern, ty, arms, default, pattern,
                    )
                    .unwrap();
                }
                for t in tags {
                    let variant_name = format!("{}{}", field_name, t);
                    write!(
                        &mut set_tag_method,
                        "
            {} => {{
                let v = if let {} = self.{} {{
                    v
                }} else {{
                    unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }}
                }};
                {}::{}(v)
            }}",
                        tag_to_string(*t, &field_ty),
                        pattern,
                        struct_field_name,
                        ty,
                        tu.name,
                        variant_name
                    )
                    .unwrap();
                    write!(
                        &mut new_method,
                        "
            {} => Self::{}(unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }}),",
                        tag_to_string(*t, &field_ty),
                        variant_name,
                        ty
                    )
                    .unwrap();
                    write!(
                        &mut get_tag_method,
                        "
            {}::{}(_) => {},",
                        tu.name,
                        variant_name,
                        tag_to_string(*t, &field_ty),
                    )
                    .unwrap();
                    write!(
                        &mut enum_str,
                        "
    {}({}),",
                        variant_name, ty
                    )
                    .unwrap();
                }
            }
            for t in &tu.empty_tags {
                let variant_name = format!("Empty{}", t);
                write!(
                    &mut set_tag_method,
                    "
            {} => {}::{},",
                    tag_to_string(*t, &field_ty),
                    tu.name,
                    variant_name
                )
                .unwrap();
                write!(
                    &mut new_method,
                    "
            {} => Self::{},",
                    tag_to_string(*t, &field_ty),
                    variant_name,
                )
                .unwrap();
                write!(
                    &mut get_tag_method,
                    "
            {}::{} => {},",
                    tu.name, variant_name, t
                )
                .unwrap();
                write!(
                    &mut enum_str,
                    "
    {},",
                    variant_name
                )
                .unwrap();
            }
            set_tag_method.push_str(
                "
            _ => panic!()
        };",
            );
            new_method.push_str(
                "
            _ => panic!(),
        }
    }
}",
            );
            get_tag_method.push_str(
                "
        }
    }
}",
            );
            enum_str.push_str("\n}");

            let code = format!(
                "{}\n{}\n{}\n{}",
                enum_str,
                new_method,
                field_methods,
                if is_first_union { &get_tag_method } else { "" },
            );
            suggestions.add(item.span, code);
        }

        set_tag_method.push_str(
            "
    }
}",
        );
        let span = item.span.shrink_to_hi();
        suggestions.add(span, set_tag_method);
    }

    for item_id in hir.items() {
        let item = hir.item(item_id);
        let (ItemKind::Fn(_, _, body_id) | ItemKind::Static(_, _, body_id)) = item.kind else {
            continue;
        };
        let hir_body = hir.body(body_id);
        let local_def_id = item_id.owner_id.def_id;
        let typeck = tcx.typeck(local_def_id);
        let mut visitor = HBodyVisitor {
            tcx,
            typeck,
            func: local_def_id,
            aggregates: &aggregates,
            field_values: &field_values,
            structs: &tagged_structs,
            unions: &tagged_unions,
            suggestions: &mut suggestions,
        };
        visitor.visit_body(hir_body);
    }

    let mut suggestions = suggestions.suggestions;
    for (path, suggestions) in &suggestions {
        tracing::info!("{:?}", path);
        for suggestion in suggestions {
            tracing::info!("{:?}", suggestion);
        }
    }

    if conf.transform {
        compile_util::apply_suggestions(&mut suggestions);
    }
}

struct Suggestions<'tcx> {
    suggestions: HashMap<PathBuf, Vec<Suggestion>>,
    source_map: &'tcx SourceMap,
}

impl<'tcx> Suggestions<'tcx> {
    fn new(source_map: &'tcx SourceMap) -> Self {
        Self {
            suggestions: HashMap::new(),
            source_map,
        }
    }

    fn add(&mut self, span: Span, code: String) {
        let snippet = span_to_snippet(span, self.source_map);
        let suggestion = make_suggestion(snippet, code);
        let path = compile_util::span_to_path(span, self.source_map).unwrap();
        self.suggestions.entry(path).or_default().push(suggestion);
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Tag(u32);

impl std::fmt::Debug for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Default)]
struct UnionUse {
    fields: BTreeSet<FieldIdx>,
    tags: BTreeMap<FieldIdx, BTreeSet<Tag>>,
    access_tags: BTreeMap<FieldIdx, VariantTags>,
    obj_tags: BTreeMap<FieldIdx, VariantTags>,
}

impl UnionUse {
    #[inline]
    fn insert_field(&mut self, field: FieldIdx) {
        self.fields.insert(field);
    }

    #[inline]
    fn insert_tags<T: TryInto<u32>, S: IntoIterator<Item = T>>(
        &mut self,
        field: FieldIdx,
        tags: S,
    ) {
        self.tags
            .entry(field)
            .or_default()
            .extend(tags.into_iter().filter_map(|t| t.try_into().ok().map(Tag)));
    }

    #[inline]
    fn get_access_tags_mut(&mut self, field: FieldIdx) -> &mut VariantTags {
        self.access_tags.entry(field).or_default()
    }

    #[inline]
    fn get_obj_tags_mut(&mut self, field: FieldIdx) -> &mut VariantTags {
        self.obj_tags.entry(field).or_default()
    }

    fn compute_tags(
        &self,
        int_fields: &HashSet<FieldIdx>,
    ) -> Option<(FieldIdx, BTreeMap<FieldIdx, Vec<Tag>>)> {
        let fs: HashSet<_> = self
            .access_tags
            .keys()
            .chain(self.obj_tags.keys())
            .copied()
            .collect();
        fs.iter()
            .filter_map(|f| {
                if !int_fields.contains(f) {
                    return None;
                }
                let tags = match (self.access_tags.get(f), self.obj_tags.get(f)) {
                    (Some(ts1), Some(ts2)) => {
                        let mut tags = ts1.compute_tags()?;
                        if !ts2.compute_tags_with(&mut tags) {
                            return None;
                        }
                        tags
                    }
                    (Some(ts), None) | (None, Some(ts)) => ts.compute_tags()?,
                    _ => unreachable!(),
                };
                if tags.len() <= 1 {
                    None
                } else {
                    Some((*f, tags))
                }
            })
            .max_by_key(|(_, tags)| tags.len())
    }
}

#[derive(Debug, Default)]
struct VariantTags {
    tags: BTreeMap<FieldIdx, BTreeMap<Tag, Vec<Span>>>,
}

impl VariantTags {
    #[inline]
    fn insert<T: TryInto<u32>>(&mut self, field: FieldIdx, tag: T, span: Span) {
        let tag = ok_or!(tag.try_into(), return);
        self.tags
            .entry(field)
            .or_default()
            .entry(Tag(tag))
            .or_default()
            .push(span);
    }

    fn compute_tags(&self) -> Option<BTreeMap<FieldIdx, Vec<Tag>>> {
        let mut all_tags = HashSet::new();
        let mut field_tags = BTreeMap::new();
        for (f, tags) in &self.tags {
            if tags.is_empty() {
                continue;
            }
            for t in tags.keys() {
                if !all_tags.insert(*t) {
                    return None;
                }
            }
            field_tags.insert(*f, tags.keys().copied().collect());
        }
        Some(field_tags)
    }

    fn compute_tags_with(&self, field_tags: &mut BTreeMap<FieldIdx, Vec<Tag>>) -> bool {
        let existing_tags: HashSet<_> = field_tags.values().flatten().copied().collect();
        let mut new_tags = HashSet::new();
        for (f, tags) in &self.tags {
            let v: Vec<_> = tags
                .keys()
                .copied()
                .filter(|t| !existing_tags.contains(t))
                .collect();
            if v.is_empty() {
                continue;
            }
            for t in &v {
                if !new_tags.insert(*t) {
                    return false;
                }
            }
            field_tags.entry(*f).or_default().extend(v);
        }
        true
    }
}

#[derive(Debug, Clone, Copy)]
pub enum AccElem {
    Field(FieldIdx),
    Index,
    Deref,
}

fn ty_to_proj(ty: Ty<'_>) -> Option<(LocalDefId, Vec<AccElem>)> {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => {
            let def_id = adt_def.did().as_local()?;
            Some((def_id, vec![]))
        }
        TyKind::Array(ty, _) => {
            let (def_id, mut v) = ty_to_proj(*ty)?;
            v.push(AccElem::Index);
            Some((def_id, v))
        }
        TyKind::Ref(_, ty, _) | TyKind::RawPtr(TypeAndMut { ty, .. }) => {
            let (def_id, mut v) = ty_to_proj(*ty)?;
            v.push(AccElem::Deref);
            Some((def_id, v))
        }
        _ => None,
    }
}

fn find_paths(
    curr: LocalDefId,
    path: &mut Vec<AccElem>,
    graph: &HashMap<LocalDefId, Vec<(LocalDefId, Vec<AccElem>)>>,
    visited: &mut HashSet<LocalDefId>,
    paths: &mut HashMap<LocalDefId, Vec<Vec<AccElem>>>,
) {
    if visited.contains(&curr) {
        return;
    }

    if !path.is_empty() {
        let p = path.iter().copied().rev().collect();
        paths.entry(curr).or_default().push(p);
    }

    visited.insert(curr);
    let succs = some_or!(graph.get(&curr), return);
    for (succ, elems) in succs {
        path.extend(elems);
        find_paths(*succ, path, graph, visited, paths);
        for _ in elems {
            path.pop();
        }
    }
    visited.remove(&curr);
}

fn compute_tags<'tcx, D: HasLocalDecls<'tcx> + ?Sized>(
    access: FieldAccess<'tcx>,
    states: &HashMap<Location, AbsMem>,
    local_decls: &D,
    tcx: TyCtxt<'tcx>,
) -> Vec<(FieldIdx, AbsInt)> {
    let state = some_or!(states.get(&access.location), return vec![]);
    let (path, is_deref) = access.get_path(state, local_decls, tcx);
    let g = state.g();
    let obj = some_or!(g.get_obj(&path, is_deref), return vec![]);
    let Obj::Struct(fields, _) = obj else { return vec![] };
    let mut v: Vec<_> = fields
        .iter()
        .filter_map(|(f, obj)| {
            let Obj::Ptr(loc) = obj else { return None };
            let obj = g.obj_at_location(loc)?;
            let Obj::AtAddr(n) = obj else { return None };
            Some((*f, n.clone()))
        })
        .collect();
    v.sort_by_key(|(f, _)| *f);
    v
}

struct MBodyVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
    structs: &'a HashMap<LocalDefId, StructInfo>,
    unions: &'a Vec<LocalDefId>,
    accesses: Vec<FieldAccess<'tcx>>,
    struct_accesses: HashSet<Local>,
    aggregates: HashMap<LocalDefId, Vec<(Local, Location)>>,
    inits: Vec<(Local, Location)>,
}

impl<'tcx, 'a> MBodyVisitor<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
        structs: &'a HashMap<LocalDefId, StructInfo>,
        unions: &'a Vec<LocalDefId>,
    ) -> Self {
        Self {
            tcx,
            local_decls,
            structs,
            unions,
            accesses: vec![],
            struct_accesses: HashSet::new(),
            aggregates: HashMap::new(),
            inits: vec![],
        }
    }
}

impl<'tcx> MVisitor<'tcx> for MBodyVisitor<'tcx, '_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if place.projection.len() > 0 {
            for i in 0..(place.projection.len() - 1) {
                let ty = Place::ty_from(
                    place.local,
                    &place.projection[..=i],
                    self.local_decls,
                    self.tcx,
                )
                .ty;
                let TyKind::Adt(adt_def, _) = ty.kind() else { continue };
                let def_id = some_or!(adt_def.did().as_local(), continue);
                if self.structs.contains_key(&def_id) {
                    self.struct_accesses.insert(place.local);
                } else if self.unions.contains(&def_id) {
                    let ProjectionElem::Field(f, _) = place.projection[i + 1] else {
                        unreachable!()
                    };
                    let access = FieldAccess {
                        ty: def_id,
                        local: place.local,
                        projection: &place.projection[..=i],
                        field: f,
                        ctx: context,
                        location,
                    };
                    self.accesses.push(access);
                }
            }
        }
        self.super_place(place, context, location);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Aggregate(box AggregateKind::Adt(def_id, _, _, _, _), _) => {
                if let Some(def_id) = def_id.as_local() {
                    if self.structs.contains_key(&def_id) || self.unions.contains(&def_id) {
                        self.aggregates
                            .entry(def_id)
                            .or_default()
                            .push((place.local, location));
                    }
                }
            }
            Rvalue::Use(Operand::Copy(_) | Operand::Move(_)) => {
                let ty = Place::ty(place, self.local_decls, self.tcx).ty;
                if let TyKind::Adt(adt_def, _) = ty.kind() {
                    let def_id = adt_def.did();
                    if let Some(def_id) = def_id.as_local() {
                        if place.projection.is_empty() && self.structs.contains_key(&def_id) {
                            self.inits.push((place.local, location));
                        }
                    }
                }
            }
            _ => {}
        }
        self.super_assign(place, rvalue, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            if let Some(constant) = func.constant() {
                let ConstantKind::Val(_, ty) = constant.literal else { unreachable!() };
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                if def_id.is_local() && self.tcx.impl_of_method(*def_id).is_some() {
                    let ty = args[0].ty(self.local_decls, self.tcx);
                    let TyKind::Ref(_, ty, _) = ty.kind() else { unreachable!() };
                    let TyKind::Adt(adt_def, _) = ty.kind() else { unreachable!() };
                    let local_def_id = adt_def.did().expect_local();
                    if self.structs.contains_key(&local_def_id) {
                        self.struct_accesses.insert(args[0].place().unwrap().local);
                    }
                }
            }
        }
        self.super_terminator(terminator, location);
    }
}

#[derive(Debug, Clone, Copy)]
struct FieldAccess<'tcx> {
    ty: LocalDefId,
    local: Local,
    projection: &'tcx [PlaceElem<'tcx>],
    field: FieldIdx,
    ctx: PlaceContext,
    location: Location,
}

impl<'tcx> FieldAccess<'tcx> {
    fn get_path<D: HasLocalDecls<'tcx> + ?Sized>(
        &self,
        state: &AbsMem,
        local_decls: &D,
        tcx: TyCtxt<'tcx>,
    ) -> (AccPath, bool) {
        assert!(!self.projection.is_empty());
        AccPath::from_local_projection(
            self.local,
            &self.projection[..self.projection.len() - 1],
            state,
            local_decls,
            tcx,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FieldAt {
    func: LocalDefId,
    location: Location,
    local: Local,
    field: FieldIdx,
}

struct StructInfo {
    int_fields: HashSet<FieldIdx>,
    #[allow(unused)]
    unions: Vec<(FieldIdx, LocalDefId)>,
}

struct TaggedStruct {
    #[allow(dead_code)]
    local_def_id: LocalDefId,
    name: String,
    tag_index: FieldIdx,
    field_names: IndexVec<FieldIdx, String>,
    unions: Vec<(LocalDefId, FieldIdx)>,
}

struct TaggedUnion {
    #[allow(dead_code)]
    local_def_id: LocalDefId,
    name: String,
    variant_tags: BTreeMap<FieldIdx, Vec<Tag>>,
    empty_tags: Vec<Tag>,
    field_name_to_index: HashMap<String, FieldIdx>,
    struct_local_def_id: LocalDefId,
    index_in_struct: FieldIdx,
    tag_index: FieldIdx,
}

struct HBodyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    func: LocalDefId,
    aggregates: &'a HashMap<Span, (Local, Location)>,
    field_values: &'a HashMap<FieldAt, BTreeSet<Tag>>,
    structs: &'a HashMap<LocalDefId, TaggedStruct>,
    unions: &'a HashMap<LocalDefId, TaggedUnion>,
    suggestions: &'a mut Suggestions<'tcx>,
}

impl<'tcx> HBodyVisitor<'_, 'tcx> {
    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let source_map = self.tcx.sess.source_map();
        match expr.kind {
            ExprKind::Struct(_, fs, _) => {
                let TyKind::Adt(adt_def, _) = self.typeck.expr_ty(expr).kind() else {
                    unreachable!()
                };
                let def_id = some_or!(adt_def.did().as_local(), return);
                let ts = some_or!(self.structs.get(&def_id), return);

                let tag_expr = fs.get(ts.tag_index.as_usize()).and_then(|field| {
                    let span = source_map.span_extend_to_line(field.span);
                    self.suggestions.add(span, "".to_string());

                    source_map.span_to_snippet(field.expr.span).ok()
                });

                let (local, mut location) = self.aggregates[&expr.span];
                location.statement_index += 1;
                let field_at = FieldAt {
                    func: self.func,
                    location,
                    local,
                    field: ts.tag_index,
                };
                let tags = self.field_values.get(&field_at);

                for (u, i) in &ts.unions {
                    let tu = &self.unions[u];
                    let field_name = &ts.field_names[*i];
                    let expr = fs
                        .iter()
                        .find(|f| &f.ident.name.to_ident_string() == field_name)
                        .unwrap()
                        .expr;
                    let ExprKind::Struct(path, ufs, _) = expr.kind else { unreachable!() };
                    let union_name = source_map.span_to_snippet(path.span()).unwrap();
                    let QPath::Resolved(_, path) = path else { unreachable!() };
                    let Res::Def(_, def_id) = path.res else { unreachable!() };
                    assert_eq!(def_id.expect_local(), *u);
                    assert_eq!(ufs.len(), 1);
                    let name = ufs[0].ident.name.to_ident_string();
                    let span = ufs[0].expr.span;
                    let init = source_map.span_to_snippet(span).unwrap();
                    let v = if let Some(tags) = tags {
                        if tags.len() == 1 {
                            let tag = tags.iter().next().unwrap();
                            let i = tu.field_name_to_index[&name];
                            let tags_from_i = &tu.variant_tags[&i];
                            let tag = if tags_from_i.contains(tag) {
                                *tag
                            } else {
                                tags_from_i[0]
                            };
                            format!("{}::{}{}({})", union_name, name, tag, init)
                        } else {
                            format!("{}::new({})", union_name, tag_expr.as_ref().unwrap())
                        }
                    } else if let Some(tag_expr) = &tag_expr {
                        format!("{}::new({})", union_name, tag_expr)
                    } else {
                        let i = tu.field_name_to_index[&name];
                        let tag = tu.variant_tags[&i][0];
                        format!("{}::{}{}({})", union_name, name, tag, init)
                    };
                    self.suggestions.add(expr.span, v);
                }
            }
            ExprKind::Field(e, field) => {
                let ty = self.typeck.expr_ty(e);
                let TyKind::Adt(adt_def, _) = ty.kind() else { return };
                let did = some_or!(adt_def.did().as_local(), return);

                if let Some(ts) = self.structs.get(&did) {
                    let variant = adt_def.variant(VariantIdx::from_u32(0));
                    if let Some(field_def) = variant.fields.get(ts.tag_index) {
                        if field_def.ident(self.tcx).name == field.name {
                            let (ctx, e2) = get_expr_context(e, self.tcx);
                            match ctx {
                                ExprContext::Value => {
                                    let span = field.span.shrink_to_hi();
                                    self.suggestions.add(span, "()".to_string());
                                }
                                ExprContext::Store(op) => {
                                    assert!(!op);

                                    let span = field.span.shrink_to_lo();
                                    self.suggestions.add(span, "set_".to_string());

                                    let span = field.span.shrink_to_hi();
                                    let span = span.with_hi(span.hi() + BytePos(2));
                                    self.suggestions.add(span, "(".to_string());

                                    let span = e2.span.shrink_to_hi();
                                    self.suggestions.add(span, ")".to_string());
                                }
                                ExprContext::Address => panic!(),
                            }
                        }
                    }
                } else if let Some(tu) = self.unions.get(&did) {
                    let (ctx, _) = get_expr_context(expr, self.tcx);
                    match ctx {
                        ExprContext::Value => {
                            let call = format!("get_{}()", field.name);
                            self.suggestions.add(field.span, call);
                        }
                        ExprContext::Store(_) | ExprContext::Address => {
                            let span = expr.span.shrink_to_lo();
                            self.suggestions.add(span, "(*".to_string());

                            let ItemKind::Union(VariantData::Struct(fs, _), _) =
                                self.tcx.hir().expect_item(did).kind
                            else {
                                unreachable!()
                            };
                            let (i, _) = fs
                                .iter()
                                .enumerate()
                                .find(|(_, f)| f.ident.name == field.name)
                                .unwrap();
                            let tags = &tu.variant_tags[&FieldIdx::from(i)];

                            let call = if tags.len() == 1 {
                                format!("deref_{}_mut())", field.name)
                            } else {
                                let ts = &self.structs[&tu.struct_local_def_id];
                                let field_name = &ts.field_names[ts.tag_index];
                                let ExprKind::Field(e2, _) = e.kind else { unreachable!() };
                                let tag = format!(
                                    "{}.{}",
                                    source_map.span_to_snippet(e2.span).unwrap(),
                                    field_name,
                                );
                                format!("deref_{}_mut({}()))", field.name, tag)
                            };
                            self.suggestions.add(field.span, call);

                            let root = get_root(expr);
                            if let ExprKind::Unary(UnOp::Deref, e) = root.kind {
                                let ty = self.typeck.expr_ty(e);
                                if let TyKind::RawPtr(TypeAndMut {
                                    mutbl: Mutability::Not,
                                    ty,
                                }) = ty.kind()
                                {
                                    let span = e.span.shrink_to_lo();
                                    self.suggestions.add(span, "(".to_string());

                                    let span = e.span.shrink_to_hi();
                                    let cast = format!(" as *mut crate::{:?})", ty);
                                    self.suggestions.add(span, cast);
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

impl<'tcx> HVisitor<'tcx> for HBodyVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }
}

struct BitFieldInitVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    inits: HashMap<Span, Span>,
    set_exprs: HashSet<Span>,
}

impl<'tcx> BitFieldInitVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            inits: HashMap::new(),
            set_exprs: HashSet::new(),
        }
    }

    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let ExprKind::Block(block, _) = expr.kind else { return };
        if block.stmts.len() <= 1 {
            return;
        }
        let StmtKind::Local(local) = block.stmts[0].kind else { return };
        let PatKind::Binding(_, hir_id, ident, _) = local.pat.kind else { return };
        if ident.name.to_ident_string() != "init" {
            return;
        }
        let init = some_or!(local.init, return);
        let ExprKind::Struct(_, _, _) = init.kind else { return };
        let e = some_or!(block.expr, return);
        let ExprKind::Path(QPath::Resolved(_, path)) = e.kind else { return };
        let Res::Local(id) = path.res else { return };
        if hir_id != id {
            return;
        }
        self.inits.insert(e.span, init.span);
        for stmt in block.stmts.iter().skip(1) {
            let StmtKind::Semi(e) = stmt.kind else { continue };
            self.set_exprs.insert(e.span);
        }
    }
}

impl<'tcx> HVisitor<'tcx> for BitFieldInitVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }
}

struct FieldVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    fields: &'a mut HashMap<LocalDefId, HashSet<Symbol>>,
}

impl<'tcx> FieldVisitor<'_, 'tcx> {
    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let ExprKind::Field(e, f) = expr.kind else { return };
        let ty = self.typeck.expr_ty(expr);
        if !ty.is_integral() && !ty.is_bool() {
            return;
        }
        let ty = self.typeck.expr_ty(e);
        let TyKind::Adt(adt_def, _) = ty.kind() else { return };
        if !adt_def.is_struct() {
            return;
        }
        let def_id = some_or!(adt_def.did().as_local(), return);
        if matches!(
            get_expr_context(expr, self.tcx).0,
            ExprContext::Store(true) | ExprContext::Address
        ) {
            self.fields.entry(def_id).or_default().insert(f.name);
        }
    }
}

impl<'tcx> HVisitor<'tcx> for FieldVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }
}

#[derive(Debug, Clone, Copy)]
enum ExprContext {
    Value,
    Address,
    Store(bool),
}

fn get_expr_context<'tcx>(
    expr: &'tcx Expr<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> (ExprContext, &'tcx Expr<'tcx>) {
    let parent = tcx.hir().get_parent(expr.hir_id);
    match parent {
        Node::Expr(e) => match e.kind {
            ExprKind::Assign(l, _, _) | ExprKind::AssignOp(_, l, _) => {
                if expr.hir_id == l.hir_id {
                    (
                        ExprContext::Store(matches!(e.kind, ExprKind::AssignOp(_, _, _))),
                        e,
                    )
                } else {
                    (ExprContext::Value, expr)
                }
            }
            ExprKind::AddrOf(_, _, _) => (ExprContext::Address, e),
            ExprKind::Field(_, _) | ExprKind::DropTemps(_) => get_expr_context(e, tcx),
            ExprKind::MethodCall(method, receiver, _, _) => {
                if expr.hir_id == receiver.hir_id
                    && method.ident.name.to_ident_string() == "as_mut_ptr"
                {
                    (ExprContext::Address, expr)
                } else {
                    (ExprContext::Value, expr)
                }
            }
            _ => (ExprContext::Value, e),
        },
        Node::Local(rustc_hir::Local { pat, .. }) => {
            let PatKind::Binding(BindingAnnotation(by_ref, _), _, _, _) = pat.kind else {
                unreachable!()
            };
            if by_ref == ByRef::Yes {
                (ExprContext::Address, expr)
            } else {
                (ExprContext::Value, expr)
            }
        }
        Node::ExprField(_) | Node::Stmt(_) | Node::Block(_) => (ExprContext::Value, expr),
        _ => unreachable!("{:?}", parent),
    }
}

fn get_root<'tcx>(expr: &'tcx Expr<'tcx>) -> &'tcx Expr<'tcx> {
    let ExprKind::Field(e, _) = expr.kind else { return expr };
    get_root(e)
}

fn tag_to_string(tag: Tag, ty: &str) -> String {
    if ty == "bool" {
        (tag.0 != 0).to_string()
    } else {
        tag.to_string()
    }
}
