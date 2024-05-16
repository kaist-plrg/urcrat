use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::Path,
};

use etrace::some_or;
use relational::Obj;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::{
    def::Res,
    definitions::DefPathDataName,
    intravisit::{self, Visitor as HVisitor},
    Expr, ExprKind, ItemKind, Node, QPath, VariantData,
};
use rustc_index::{bit_set::BitSet, IndexVec};
use rustc_middle::{
    hir::nested_filter,
    mir::{
        visit::{MutatingUseContext, PlaceContext, Visitor as MVisitor},
        AggregateKind, ConstantKind, HasLocalDecls, Local, LocalDecl, Location, Place, PlaceElem,
        ProjectionElem, Rvalue, Terminator, TerminatorKind,
    },
    ty::{List, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_session::config::Input;
use rustc_span::def_id::LocalDefId;
use typed_arena::Arena;

use self::relational::{AbsInt, AbsMem, AccPath};
use crate::*;

#[derive(Debug, Clone)]
pub struct Config {
    pub solutions: Option<points_to::Solutions>,
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
    let pre = points_to::pre_analyze(&tss, tcx);
    let solutions = conf
        .solutions
        .clone()
        .unwrap_or_else(|| points_to::analyze(&pre, &tss, tcx));
    let may_points_to = points_to::post_analyze(pre, solutions, &tss, tcx);

    let mut structs = vec![];
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
                    v.push(AccElem::Field(i.as_u32()));
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
        let mut has_union = false;
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
                has_union = true;
            }
        }
        if has_union {
            structs.push(local_def_id);
        }
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
    for item_id in hir.items() {
        let item = hir.item(item_id);
        let local_def_id = item_id.owner_id.def_id;
        let body = match item.kind {
            ItemKind::Fn(_, _, _) => tcx.optimized_mir(local_def_id),
            ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(local_def_id),
            _ => continue,
        };
        let mut visitor = MBodyVisitor::new(tcx, &body.local_decls, &structs, &unions);
        visitor.visit_body(body);
        if visitor.accesses.is_empty()
            && visitor.struct_accesses.is_empty()
            && visitor.aggregates.is_empty()
        {
            continue;
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
        let ctx = relational::AnalysisContext {
            local_def_id,
            tss: &tss,
            may_points_to: &may_points_to,
            no_gc_locals: Some(&locals),
            gc: true,
        };
        let states = relational::analyze_body(body, ctx, tcx);
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
                    .entry(access.field.as_u32())
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
                        }
                        if body.basic_blocks[block].statements.len() > statement_index {
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

    let mut tag_fields = HashMap::new();
    for (u, vs) in &variant_tag_values {
        println!("Union {:?}", u);
        println!("Fields {:?}", fields[u]);
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
            tag_fields.insert(*u, tag_field);
            println!("Field: {:?}", tag_field);
            let mut all_tags = tag_values[&u][&tag_field].clone();
            for (variant, vs) in &vs[&tag_field] {
                for v in vs.keys() {
                    all_tags.remove(v);
                }
                let tags: Vec<_> = vs.keys().copied().collect();
                println!("  {}: {:?}", variant, tags);
            }
            if !all_tags.is_empty() {
                println!("  *: {:?}", all_tags);
            }
        } else {
            println!("  {:?}", tag_values[u]);
            for (f, vs) in vs {
                println!("  {}", f);
                for (variant, vs) in vs {
                    println!("    {}", variant);
                    for (n, spans) in vs {
                        println!("      {}", n);
                        for span in spans {
                            println!("        {:?}", span);
                        }
                    }
                }
            }
        }
    }

    let mut rewrite_structs: HashMap<_, Vec<_>> = HashMap::new();
    for (u, tag_field) in tag_fields {
        let (i, s) = union_to_struct[&u];
        rewrite_structs
            .entry(s)
            .or_default()
            .push((u, tag_field, i));
    }

    let source_map = tcx.sess.source_map();

    let mut struct_tag_fields = HashMap::new();
    for (s, us) in rewrite_structs {
        let fs = us.iter().map(|(_, f, _)| *f).collect::<HashSet<_>>();
        assert_eq!(fs.len(), 1);
        let field_idx = fs.into_iter().next().unwrap();
        struct_tag_fields.insert(s, field_idx);
        let Node::Item(item) = hir.get_if_local(s.to_def_id()).unwrap() else { unreachable!() };
        let struct_name = item.ident.name.to_ident_string();
        let ItemKind::Struct(VariantData::Struct(sfs, _), _) = item.kind else { unreachable!() };
        let field = &sfs[field_idx as usize];
        let span = source_map.span_extend_to_line(field.span);
        println!("{}", source_map.span_to_snippet(span).unwrap());
        let field_name = field.ident.name.to_ident_string();
        let field_ty = source_map.span_to_snippet(field.ty.span).unwrap();

        for (u, _, i) in us {
            let struct_field_name = sfs[i.as_usize()].ident.name.to_ident_string();
            let Node::Item(item) = hir.get_if_local(u.to_def_id()).unwrap() else { unreachable!() };
            let union_name = item.ident.name.to_ident_string();
            println!("{}", source_map.span_to_snippet(item.span).unwrap());
            let ItemKind::Union(VariantData::Struct(ufs, _), _) = item.kind else { unreachable!() };
            let tys: Vec<_> = ufs
                .iter()
                .map(|f| source_map.span_to_snippet(f.ty.span).unwrap().to_string())
                .collect();
            let mut all_fields = fields[&u].clone();
            let mut all_tags = tag_values[&u][&field_idx].clone();
            let mut enum_variants = vec![];
            let mut field_methods = String::new();
            for (field, tags) in &variant_tag_values[&u][&field_idx] {
                all_fields.remove(&FieldIdx::from_u32(*field));
                for t in tags.keys() {
                    all_tags.remove(t);
                }
                for tag in tags.keys() {
                    enum_variants.push((Some(*field), *tag));
                }
                let field_name = ufs[*field as usize].ident.name.to_ident_string();
                let ty = &tys[*field as usize];
                let pattern: String = tags
                    .keys()
                    .map(|tag| format!("Self::{}{}(v)", field_name, tag))
                    .intersperse("|".to_string())
                    .collect();
                let pattern = if tags.len() == 1 {
                    pattern
                } else {
                    format!("({})", pattern)
                };
                let method = format!(
                    "impl {}{{pub fn get_{}(&mut self)->*mut {}{{let {}=self else{{panic!()}};v as _}}}}",
                    union_name, field_name, ty, pattern,
                );
                field_methods.push_str(&method);
                field_methods.push('\n');
            }
            if all_fields.is_empty() {
                for tag in all_tags {
                    enum_variants.push((None, tag));
                }
            } else {
                assert_eq!(all_fields.len(), 1);
                assert_eq!(all_tags.len(), 1);
                let field = all_fields.into_iter().next().unwrap().as_u32();
                let tag = all_tags.into_iter().next().unwrap();
                enum_variants.push((Some(field), tag));
            }
            let mut enum_str = format!("pub enum {}{{", union_name);
            let mut get_tag_method = format!(
                "impl {}{{pub fn get_{}(self)->{}{{match self.{}{{",
                struct_name, field_name, field_ty, struct_field_name
            );
            for (f, t) in enum_variants {
                if let Some(f) = f {
                    let field_name = ufs[f as usize].ident.name.to_ident_string();
                    let ty = &tys[f as usize];
                    let variant_name = format!("{}{}", field_name, t);
                    enum_str.push_str(&format!("{}({})", variant_name, ty));
                    get_tag_method.push_str(&format!("{}::{}(_)=>{}", union_name, variant_name, t));
                } else {
                    let variant_name = format!("Empty{}", t);
                    enum_str.push_str(&variant_name);
                    get_tag_method.push_str(&format!("{}::{}=>{}", union_name, variant_name, t));
                };
                enum_str.push(',');
                get_tag_method.push(',');
            }
            enum_str.push('}');
            get_tag_method.push_str("}}}");
            println!("{}", enum_str);
            println!("{}", get_tag_method);
            println!("{}", field_methods);
        }
    }

    for item_id in hir.items() {
        let item = hir.item(item_id);
        let (ItemKind::Fn(_, _, body_id) | ItemKind::Static(_, _, body_id)) = item.kind else {
            continue;
        };
        let body = hir.body(body_id);
        let mut visitor = HBodyVisitor {
            tcx,
            struct_tag_fields: &struct_tag_fields,
        };
        visitor.visit_body(body);
    }
}

#[derive(Debug, Clone, Copy)]
pub enum AccElem {
    Field(u32),
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
) -> Vec<(u32, AbsInt)> {
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
    structs: &'a Vec<LocalDefId>,
    unions: &'a Vec<LocalDefId>,
    accesses: Vec<FieldAccess<'tcx>>,
    struct_accesses: HashSet<Local>,
    aggregates: HashMap<LocalDefId, Vec<(Local, Location)>>,
}

impl<'tcx, 'a> MBodyVisitor<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
        structs: &'a Vec<LocalDefId>,
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
                if self.structs.contains(&def_id) {
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
        if let Rvalue::Aggregate(box AggregateKind::Adt(def_id, _, _, _, _), _) = rvalue {
            if let Some(def_id) = def_id.as_local() {
                if self.structs.contains(&def_id) || self.unions.contains(&def_id) {
                    self.aggregates
                        .entry(def_id)
                        .or_default()
                        .push((place.local, location));
                }
            }
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
                    if self.structs.contains(&local_def_id) {
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

struct HBodyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    struct_tag_fields: &'a HashMap<LocalDefId, u32>,
}

impl<'tcx> HBodyVisitor<'_, 'tcx> {
    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Struct(path, _fs, _) => {
                let QPath::Resolved(_, path) = path else { return };
                let Res::Def(_, def_id) = path.res else { return };
                let def_id = some_or!(def_id.as_local(), return);
                let _tag_field_idx = *some_or!(self.struct_tag_fields.get(&def_id), return);
                println!(
                    "{}",
                    self.tcx
                        .sess
                        .source_map()
                        .span_to_snippet(expr.span)
                        .unwrap()
                );
            }
            ExprKind::Field(_, _) => {}
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
