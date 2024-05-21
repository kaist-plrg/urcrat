use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Write,
    path::{Path, PathBuf},
};

use etrace::some_or;
use must_analysis::Obj;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::{
    def::Res,
    definitions::DefPathDataName,
    intravisit::{self, Visitor as HVisitor},
    Expr, ExprKind, ItemKind, Node, PatKind, QPath, StmtKind, VariantData,
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
use rustc_span::{def_id::LocalDefId, BytePos, Span};
use rustfix::Suggestion;
use typed_arena::Arena;

use self::must_analysis::{AbsInt, AbsMem, AccPath};
use crate::*;

#[derive(Debug, Clone)]
pub struct Config {
    pub solutions: Option<may_analysis::Solutions>,
    pub unions: HashSet<String>,
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
        let has_int_field = variant
            .fields
            .iter()
            .any(|f| f.ty(tcx, List::empty()).is_integral());
        if !has_int_field && !tss.bitfields.contains_key(&local_def_id) {
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
            structs.insert(local_def_id, struct_unions);
        }
    }

    println!("Candidates:");
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

    let mut fields: HashMap<_, BTreeSet<_>> = HashMap::new();
    let mut tag_values: HashMap<_, BTreeMap<_, BTreeSet<u128>>> = HashMap::new();
    let mut variant_tag_values: HashMap<_, BTreeMap<_, BTreeMap<_, BTreeMap<_, BTreeSet<_>>>>> =
        HashMap::new();
    let mut aggregates: HashMap<_, _> = HashMap::new();
    let mut field_values: HashMap<FieldAt, BTreeSet<u128>> = HashMap::new();
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
        let mut hvisitor = BitFieldInitVisitor {
            tcx,
            inits: HashMap::new(),
        };
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
            fields.entry(a.ty).or_default().insert(a.field);
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
            let tags = compute_tags(access, &states, &body.local_decls, tcx);
            for (f, ns) in tags {
                let vs = variant_tag_values
                    .entry(access.ty)
                    .or_default()
                    .entry(f)
                    .or_default()
                    .entry(access.field)
                    .or_default();
                for n in ns.into_set() {
                    vs.entry(n).or_default().insert(span);
                }
            }
        }
        for (loc, mem) in &states {
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
                            tag_values
                                .entry(*u)
                                .or_default()
                                .entry(*f)
                                .or_default()
                                .extend(n.into_set());
                            let field_at = FieldAt {
                                func: local_def_id,
                                location: *loc,
                                local: *l,
                                field: *f,
                            };
                            field_values
                                .entry(field_at)
                                .or_default()
                                .extend(n.into_set());
                        }
                        if body.basic_blocks[block].statements.len() > statement_index {
                            continue;
                        }
                        if let TerminatorKind::Call {
                            func: Operand::Constant(box constant),
                            ..
                        } = body.basic_blocks[block].terminator().kind
                        {
                            let ConstantKind::Val(_, ty) = constant.literal else { unreachable!() };
                            let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                            if def_id.as_local().is_some()
                                && tcx.impl_of_method(*def_id).is_some()
                                && tcx
                                    .def_path(*def_id)
                                    .data
                                    .last()
                                    .unwrap()
                                    .to_string()
                                    .starts_with("set_")
                            {
                                continue;
                            }
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
                                let vs = variant_tag_values
                                    .entry(*u)
                                    .or_default()
                                    .entry(*f)
                                    .or_default()
                                    .entry(variant)
                                    .or_default();
                                for n in ns.into_set() {
                                    vs.entry(n).or_default().insert(span);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    println!("Analysis done");

    let mut tag_fields = HashMap::new();
    let mut union_variant_tags = HashMap::new();
    for (u, vs) in &variant_tag_values {
        let tag_field = vs
            .iter()
            .filter_map(|(f, vs)| {
                if vs.len() <= 1 {
                    return None;
                }
                let mut tags = HashSet::new();
                for vs in vs.values() {
                    for v in vs.keys() {
                        if !tags.insert(*v) {
                            return None;
                        }
                    }
                }
                Some((*f, vs.len()))
            })
            .max_by_key(|(_, n)| *n);
        if let Some((tag_field, _)) = tag_field {
            println!("Union {:?}", u);
            println!("Fields {:?}", fields[u]);
            tag_fields.insert(*u, tag_field);
            println!("Field: {:?}", tag_field);
            let mut all_tags = tag_values[&u][&tag_field].clone();
            for (variant, vs) in &vs[&tag_field] {
                for v in vs.keys() {
                    all_tags.remove(v);
                }
                let tags: Vec<_> = vs.keys().copied().collect();
                println!("  {}: {:?}", variant.as_u32(), tags);
                union_variant_tags.insert((*u, *variant), tags);
            }
            if !all_tags.is_empty() {
                println!("  *: {:?}", all_tags);
            }
        } else {
            tracing::info!("Union {:?}", u);
            tracing::info!("Fields {:?}", fields[u]);
            tracing::info!("  {:?}", tag_values[u]);
            for (f, vs) in vs {
                tracing::info!("  {}", f.as_u32());
                for (variant, vs) in vs {
                    tracing::info!("    {}", variant.as_u32());
                    for (n, spans) in vs {
                        tracing::info!("      {}", n);
                        for span in spans {
                            tracing::info!("        {:?}", span);
                        }
                    }
                }
            }
        }
    }

    let mut rewrite_structs: HashMap<_, Vec<_>> = HashMap::new();
    for (u, tag_field) in &tag_fields {
        let (i, s) = union_to_struct[&u];
        rewrite_structs
            .entry(s)
            .or_default()
            .push((*u, *tag_field, i));
    }

    let union_field_names: HashMap<_, HashMap<_, _>> = tag_fields
        .keys()
        .map(|u| {
            let ItemKind::Union(VariantData::Struct(fs, _), _) = hir.expect_item(*u).kind else {
                unreachable!()
            };
            let fs = fs
                .iter()
                .enumerate()
                .map(|(i, f)| (f.ident.name.to_ident_string(), FieldIdx::from_usize(i)))
                .collect();
            (*u, fs)
        })
        .collect();
    let struct_field_names: HashMap<_, IndexVec<FieldIdx, _>> = rewrite_structs
        .keys()
        .map(|s| {
            let ItemKind::Struct(VariantData::Struct(fs, _), _) = hir.expect_item(*s).kind else {
                unreachable!()
            };
            let mut fs: IndexVec<FieldIdx, _> =
                fs.iter().map(|f| f.ident.name.to_ident_string()).collect();
            if let Some(bitfield) = tss.bitfields.get(s) {
                for _ in 0..bitfield.fields.len() {
                    let (name, _) = &bitfield.fields[&fs.next_index()];
                    fs.push(name.clone());
                }
            }
            (*s, fs)
        })
        .collect();

    let source_map = tcx.sess.source_map();

    let mut struct_tag_fields = HashMap::new();
    let mut suggestions: HashMap<_, Vec<_>> = HashMap::new();
    for (s, us) in rewrite_structs {
        let fs = us.iter().map(|(_, f, _)| *f).collect::<HashSet<_>>();
        assert_eq!(fs.len(), 1);
        let field_idx = fs.into_iter().next().unwrap();
        struct_tag_fields.insert(s, field_idx);
        let Node::Item(item) = hir.get_if_local(s.to_def_id()).unwrap() else { unreachable!() };
        let file = compile_util::span_to_path(item.span, source_map).unwrap();
        let v = suggestions.entry(file.clone()).or_default();
        let struct_name = item.ident.name.to_ident_string();
        let ItemKind::Struct(VariantData::Struct(sfs, _), _) = item.kind else { unreachable!() };

        let (field_name, field_ty) = if let Some(field) = sfs.get(field_idx.as_usize()) {
            let span = source_map.span_extend_to_line(field.span);
            let snippet = compile_util::span_to_snippet(span, source_map);
            let suggestion = compile_util::make_suggestion(snippet, "".to_string());
            v.push(suggestion);

            let field_name = field.ident.name.to_ident_string();
            let field_ty = source_map.span_to_snippet(field.ty.span).unwrap();
            (field_name, field_ty)
        } else {
            let (name, ty) = tss.bitfields[&s].fields[&field_idx].clone();
            let mut lo = item.ident.span.hi() + BytePos(3);
            'l: for f in sfs {
                loop {
                    let span = source_map.span_extend_to_line(f.span.with_lo(lo).with_hi(lo));
                    let code = source_map.span_to_snippet(span).unwrap();
                    if code.contains(&format!("#[bitfield(name = \"{}\"", name)) {
                        let snippet = compile_util::span_to_snippet(span, source_map);
                        let suggestion = compile_util::make_suggestion(snippet, "".to_string());
                        v.push(suggestion);
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
            struct_name, field_name, field_ty,
        );
        for (n, (u, _, i)) in us.iter().enumerate() {
            let is_first_union = n == 0;
            let struct_field_name = sfs[i.as_usize()].ident.name.to_ident_string();
            let Node::Item(item) = hir.get_if_local(u.to_def_id()).unwrap() else { unreachable!() };
            let union_name = item.ident.name.to_ident_string();
            let ItemKind::Union(VariantData::Struct(ufs, _), _) = item.kind else { unreachable!() };
            let tys: Vec<_> = ufs
                .iter()
                .map(|f| source_map.span_to_snippet(f.ty.span).unwrap().to_string())
                .collect();
            let mut all_fields = fields[&u].clone();
            let mut all_tags = tag_values[&u][&field_idx].clone();
            let mut enum_variants = vec![];
            let mut field_methods = String::new();
            write!(
                &mut set_tag_method,
                "
        self.{} = match v {{",
                struct_field_name
            )
            .unwrap();
            for (field, tags) in &variant_tag_values[&u][&field_idx] {
                all_fields.remove(field);
                for t in tags.keys() {
                    all_tags.remove(t);
                }
                for tag in tags.keys() {
                    enum_variants.push((Some(*field), *tag));
                }
                let field_name = ufs[field.as_usize()].ident.name.to_ident_string();
                let ty = &tys[field.as_usize()];
                let pattern: String = tags
                    .keys()
                    .map(|tag| format!("{}::{}{}(v)", union_name, field_name, tag))
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
                    union_name, field_name, ty, pattern,
                )
                .unwrap();
                if tags.len() == 1 {
                    let (t, _) = tags.iter().next().unwrap();
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
                        union_name, field_name, ty, pattern, ty, field_name, t, pattern,
                    )
                    .unwrap();
                } else {
                    let mut arms = String::new();
                    for t in tags.keys() {
                        write!(
                            &mut arms,
                            "
                {} => {}::{}{}(v),",
                            t, union_name, field_name, t
                        )
                        .unwrap();
                    }
                    writeln!(
                        &mut field_methods,
                        "impl {} {{
    pub fn deref_{}_mut(&mut self, t: {}) -> *mut {} {{
        if !matches!(self, {}) {{
            let v = unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }};
            *self = match t {{{}
                _ => panic!(),
            }};
        }}
        if let {} = self {{
            v as _
        }} else {{
            panic!()
        }}
    }}
}}",
                        union_name, field_name, field_ty, ty, pattern, ty, arms, pattern,
                    )
                    .unwrap();
                }
                for t in tags.keys() {
                    write!(
                        &mut set_tag_method,
                        "
            {} => {{
                let v = if let {} = self.{} {{
                    v
                }} else {{
                    unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }}
                }};
                {}::{}{}(v)
            }}",
                        t, pattern, struct_field_name, ty, union_name, field_name, t,
                    )
                    .unwrap();
                }
            }
            set_tag_method.push_str(
                "
            _ => panic!()
        };",
            );
            if all_fields.is_empty() {
                for tag in all_tags {
                    enum_variants.push((None, tag));
                }
            } else {
                assert_eq!(all_fields.len(), 1);
                assert_eq!(all_tags.len(), 1);
                let field = all_fields.into_iter().next().unwrap();
                let tag = all_tags.into_iter().next().unwrap();
                enum_variants.push((Some(field), tag));
            }
            let mut enum_str = format!("pub enum {} {{", union_name);
            let mut get_tag_method = format!(
                "impl {} {{
    pub fn {}(self) -> {} {{
        match self.{} {{",
                struct_name, field_name, field_ty, struct_field_name
            );
            for (f, t) in enum_variants {
                if let Some(f) = f {
                    let field_name = ufs[f.as_usize()].ident.name.to_ident_string();
                    let ty = &tys[f.as_usize()];
                    let variant_name = format!("{}{}", field_name, t);
                    write!(
                        &mut enum_str,
                        "
    {}({}),",
                        variant_name, ty
                    )
                    .unwrap();
                    write!(
                        &mut get_tag_method,
                        "
            {}::{}(_) => {},",
                        union_name, variant_name, t
                    )
                    .unwrap();
                } else {
                    let variant_name = format!("Empty{}", t);
                    write!(
                        &mut enum_str,
                        "
    {},",
                        variant_name
                    )
                    .unwrap();
                    write!(
                        &mut get_tag_method,
                        "
            {}::{} => {},",
                        union_name, variant_name, t
                    )
                    .unwrap();
                };
            }
            enum_str.push_str("\n}");
            get_tag_method.push_str(
                "
        }
    }
}",
            );
            let snippet = compile_util::span_to_snippet(item.span, source_map);
            let code = format!(
                "{}\n{}\n{}",
                enum_str,
                field_methods,
                if is_first_union { &get_tag_method } else { "" },
            );
            let suggestion = compile_util::make_suggestion(snippet, code);
            v.push(suggestion);
        }

        set_tag_method.push_str(
            "
    }
}",
        );
        let span = item.span.shrink_to_hi();
        let snippet = compile_util::span_to_snippet(span, source_map);
        let suggestion = compile_util::make_suggestion(snippet, set_tag_method);
        v.push(suggestion);
    }

    for item_id in hir.items() {
        let item = hir.item(item_id);
        let (ItemKind::Fn(_, _, body_id) | ItemKind::Static(_, _, body_id)) = item.kind else {
            continue;
        };
        let hir_body = hir.body(body_id);
        let local_def_id = item_id.owner_id.def_id;
        // let mir_body = if matches!(item.kind, ItemKind::Fn(_, _, _)) {
        //     tcx.optimized_mir(local_def_id)
        // } else {
        //     tcx.mir_for_ctfe(local_def_id)
        // };
        let typeck = tcx.typeck(local_def_id);
        let mut visitor = HBodyVisitor {
            tcx,
            // mir_body,
            typeck,
            func: local_def_id,
            structs: &structs,
            struct_tag_fields: &struct_tag_fields,
            struct_field_names: &struct_field_names,
            aggregates: &aggregates,
            field_values: &field_values,
            unions: &unions,
            union_variant_tags: &union_variant_tags,
            union_to_struct: &union_to_struct,
            union_field_names: &union_field_names,
            suggestions: &mut suggestions,
        };
        visitor.visit_body(hir_body);
    }

    for (path, suggestions) in &suggestions {
        tracing::info!("{:?}", path);
        for suggestion in suggestions {
            tracing::info!("{:?}", suggestion);
        }
    }

    compile_util::apply_suggestions(&mut suggestions);
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
    structs: &'a HashMap<LocalDefId, Vec<(FieldIdx, LocalDefId)>>,
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
        structs: &'a HashMap<LocalDefId, Vec<(FieldIdx, LocalDefId)>>,
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

struct HBodyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    // mir_body: &'a rustc_middle::mir::Body<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    func: LocalDefId,
    structs: &'a HashMap<LocalDefId, Vec<(FieldIdx, LocalDefId)>>,
    struct_tag_fields: &'a HashMap<LocalDefId, FieldIdx>,
    struct_field_names: &'a HashMap<LocalDefId, IndexVec<FieldIdx, String>>,
    aggregates: &'a HashMap<Span, (Local, Location)>,
    field_values: &'a HashMap<FieldAt, BTreeSet<u128>>,
    unions: &'a Vec<LocalDefId>,
    union_variant_tags: &'a HashMap<(LocalDefId, FieldIdx), Vec<u128>>,
    union_to_struct: &'a HashMap<LocalDefId, (FieldIdx, LocalDefId)>,
    union_field_names: &'a HashMap<LocalDefId, HashMap<String, FieldIdx>>,
    suggestions: &'a mut HashMap<PathBuf, Vec<Suggestion>>,
}

impl<'tcx> HBodyVisitor<'_, 'tcx> {
    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let source_map = self.tcx.sess.source_map();
        let path = some_or!(compile_util::span_to_path(expr.span, source_map), return);
        let suggestions = self.suggestions.entry(path).or_default();
        match expr.kind {
            ExprKind::Struct(path, fs, _) => {
                let QPath::Resolved(_, path) = path else { return };
                let Res::Def(_, def_id) = path.res else { return };
                let def_id = some_or!(def_id.as_local(), return);
                let tag_field_idx = *some_or!(self.struct_tag_fields.get(&def_id), return);
                let unions = some_or!(self.structs.get(&def_id), return);

                if let Some(field) = fs.get(tag_field_idx.as_usize()) {
                    let span = source_map.span_extend_to_line(field.span);
                    let snippet = compile_util::span_to_snippet(span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, "".to_string());
                    suggestions.push(suggestion);
                }

                let (local, mut location) = self.aggregates[&expr.span];
                location.statement_index += 1;
                let field_at = FieldAt {
                    func: self.func,
                    location,
                    local,
                    field: tag_field_idx,
                };
                let tag = self.field_values.get(&field_at).and_then(|values| {
                    assert!(values.len() <= 1, "{:?}", values);
                    values.iter().next()
                });

                for (i, u) in unions {
                    let field_name = &self.struct_field_names[&def_id][*i];
                    let expr = fs
                        .iter()
                        .find(|f| &f.ident.name.to_ident_string() == field_name)
                        .unwrap()
                        .expr;
                    let snippet = compile_util::span_to_snippet(expr.span, source_map);
                    let ExprKind::Struct(path, ufs, _) = expr.kind else { unreachable!() };
                    let union_name = source_map.span_to_snippet(path.span()).unwrap();
                    let QPath::Resolved(_, path) = path else { unreachable!() };
                    let Res::Def(_, def_id) = path.res else { unreachable!() };
                    assert_eq!(def_id.expect_local(), *u);
                    assert_eq!(ufs.len(), 1);
                    let name = ufs[0].ident.name.to_ident_string();
                    let span = ufs[0].expr.span;
                    let init = source_map.span_to_snippet(span).unwrap();
                    let tag = if let Some(tag) = tag {
                        *tag
                    } else {
                        let i = self.union_field_names[u][&name];
                        let tags = &self.union_variant_tags[&(*u, i)];
                        tags[0]
                    };
                    let v = format!("{}::{}{}({})", union_name, name, tag, init);
                    let suggestion = compile_util::make_suggestion(snippet, v);
                    suggestions.push(suggestion);
                }
            }
            ExprKind::Field(e, field) => {
                let ty = self.typeck.expr_ty(e);
                let TyKind::Adt(adt_def, _) = ty.kind() else { return };
                let did = some_or!(adt_def.did().as_local(), return);

                if let Some(tag_field_idx) = self.struct_tag_fields.get(&did) {
                    let variant = adt_def.variant(VariantIdx::from_u32(0));
                    if let Some(field_def) = variant.fields.get(*tag_field_idx) {
                        if field_def.ident(self.tcx).name == field.name {
                            let (ctx, e2) = get_expr_context(e, self.tcx);
                            match ctx {
                                ExprContext::Value => {
                                    let span = field.span.shrink_to_hi();
                                    let snippet = compile_util::span_to_snippet(span, source_map);
                                    let suggestion =
                                        compile_util::make_suggestion(snippet, "()".to_string());
                                    suggestions.push(suggestion);
                                }
                                ExprContext::Store => {
                                    let span = field.span.shrink_to_lo();
                                    let snippet = compile_util::span_to_snippet(span, source_map);
                                    let suggestion =
                                        compile_util::make_suggestion(snippet, "set_".to_string());
                                    suggestions.push(suggestion);

                                    let span = field.span.shrink_to_hi();
                                    let span = span.with_hi(span.hi() + BytePos(2));
                                    let snippet = compile_util::span_to_snippet(span, source_map);
                                    let suggestion =
                                        compile_util::make_suggestion(snippet, "(".to_string());
                                    suggestions.push(suggestion);

                                    let span = e2.span.shrink_to_hi();
                                    let snippet = compile_util::span_to_snippet(span, source_map);
                                    let suggestion =
                                        compile_util::make_suggestion(snippet, ")".to_string());
                                    suggestions.push(suggestion);
                                }
                                ExprContext::Address => panic!(),
                            }
                        }
                    }
                } else if self.unions.contains(&did) {
                    let (ctx, _) = get_expr_context(expr, self.tcx);
                    match ctx {
                        ExprContext::Value => {
                            let snippet = compile_util::span_to_snippet(field.span, source_map);
                            let call = format!("get_{}()", field.name);
                            let suggestion = compile_util::make_suggestion(snippet, call);
                            suggestions.push(suggestion);
                        }
                        ExprContext::Store | ExprContext::Address => {
                            let span = expr.span.shrink_to_lo();
                            let snippet = compile_util::span_to_snippet(span, source_map);
                            let suggestion =
                                compile_util::make_suggestion(snippet, "(*".to_string());
                            suggestions.push(suggestion);

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
                            let tags = &self.union_variant_tags[&(did, FieldIdx::from(i))];

                            let call = if tags.len() == 1 {
                                format!("deref_{}_mut())", field.name)
                            } else {
                                let (_, s_did) = self.union_to_struct[&did];
                                let field_idx = self.struct_tag_fields[&s_did];
                                let field_name = &self.struct_field_names[&s_did][field_idx];
                                let ExprKind::Field(e2, _) = e.kind else { unreachable!() };
                                let tag = format!(
                                    "{}.{}",
                                    source_map.span_to_snippet(e2.span).unwrap(),
                                    field_name,
                                );
                                format!("deref_{}_mut({}()))", field.name, tag)
                            };
                            let snippet = compile_util::span_to_snippet(field.span, source_map);
                            let suggestion = compile_util::make_suggestion(snippet, call);
                            suggestions.push(suggestion);
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
}

impl<'tcx> BitFieldInitVisitor<'tcx> {
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

#[derive(Debug, Clone, Copy)]
enum ExprContext {
    Value,
    Address,
    Store,
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
                    (ExprContext::Store, e)
                } else {
                    (ExprContext::Value, expr)
                }
            }
            ExprKind::AddrOf(_, _, _) => (ExprContext::Address, e),
            ExprKind::Field(_, _) | ExprKind::DropTemps(_) => get_expr_context(e, tcx),
            _ => (ExprContext::Value, e),
        },
        Node::ExprField(_) | Node::Stmt(_) | Node::Local(_) => (ExprContext::Value, expr),
        _ => unreachable!("{:?}", parent),
    }
}
