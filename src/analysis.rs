use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::Path,
};

use etrace::some_or;
use relational::Obj;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::{definitions::DefPathDataName, ItemKind};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        visit::{PlaceContext, Visitor},
        AggregateKind, Local, LocalDecl, Location, Place, PlaceElem, ProjectionElem, Rvalue,
    },
    ty::{List, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_session::config::Input;
use rustc_span::def_id::LocalDefId;
use typed_arena::Arena;

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

    let mut unions = vec![];
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
        for f in &variant.fields {
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
            }
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

    let mut tag_values: HashMap<_, BTreeMap<_, BTreeSet<_>>> = HashMap::new();
    let mut variant_tag_values: HashMap<_, BTreeMap<_, BTreeMap<_, BTreeMap<_, Vec<_>>>>> =
        HashMap::new();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        let local_def_id = item_id.owner_id.def_id;
        let body = match item.kind {
            ItemKind::Fn(_, _, _) => tcx.optimized_mir(local_def_id),
            ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(local_def_id),
            _ => continue,
        };
        let mut visitor = BodyVisitor::new(tcx, &body.local_decls, &unions);
        visitor.visit_body(body);
        if visitor.accesses.is_empty() && !visitor.aggregate {
            continue;
        }
        let mut local_to_unions: HashMap<_, Vec<_>> = HashMap::new();
        for (i, local) in body.local_decls.iter_enumerated() {
            let (adt_def, ptr) = match local.ty.kind() {
                TyKind::Adt(adt_def, _) => (adt_def, false),
                TyKind::Ref(_, ty, _) | TyKind::RawPtr(TypeAndMut { ty, .. }) => {
                    let TyKind::Adt(adt_ref, _) = ty.kind() else { continue };
                    (adt_ref, true)
                }
                _ => continue,
            };
            let local_def_id = some_or!(adt_def.did().as_local(), continue);
            for (u, paths) in &paths_to_unions {
                let paths = some_or!(paths.get(&local_def_id), continue);
                let local_to_unions = local_to_unions.entry(*u).or_default();
                for p in paths {
                    let mut path = vec![];
                    if ptr {
                        path.push(AccElem::Deref);
                    }
                    path.extend(p);
                    local_to_unions.push((i, path));
                }
            }
        }
        println!("{:?}", local_def_id);
        let states = relational::analyze_fn(local_def_id, body, &tss, &may_points_to, true, tcx);
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
                                Some((*f, *n))
                            })
                            .collect();
                        for (f, n) in &v {
                            tag_values
                                .entry(*u)
                                .or_default()
                                .entry(*f)
                                .or_default()
                                .insert(*n);
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
                            for (f, n) in &v {
                                variant_tag_values
                                    .entry(*u)
                                    .or_default()
                                    .entry(*f)
                                    .or_default()
                                    .entry(variant)
                                    .or_default()
                                    .entry(*n)
                                    .or_default()
                                    .push(span);
                            }
                        }
                    }
                }
            }
        }
    }

    for (u, vs) in &variant_tag_values {
        println!("Union {:?}", u);
        let tag_field = vs
            .iter()
            .filter_map(|(f, vs)| {
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
        TyKind::RawPtr(TypeAndMut { ty, .. }) => {
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

struct BodyVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
    unions: &'a Vec<LocalDefId>,
    accesses: Vec<FieldAccess<'tcx>>,
    aggregate: bool,
}

impl<'tcx, 'a> BodyVisitor<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
        unions: &'a Vec<LocalDefId>,
    ) -> Self {
        Self {
            tcx,
            local_decls,
            unions,
            accesses: vec![],
            aggregate: false,
        }
    }
}

impl<'tcx> Visitor<'tcx> for BodyVisitor<'tcx, '_> {
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
                if !self.unions.contains(&def_id) {
                    continue;
                }
                let ProjectionElem::Field(f, _) = place.projection[i + 1] else { unreachable!() };
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
        self.super_place(place, context, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Aggregate(box AggregateKind::Adt(def_id, _, _, _, _), _) = rvalue {
            if let Some(def_id) = def_id.as_local() {
                if self.unions.contains(&def_id) {
                    self.aggregate = true;
                }
            }
        }
        self.super_rvalue(rvalue, location);
    }
}

#[allow(unused)]
#[derive(Debug, Clone, Copy)]
struct FieldAccess<'tcx> {
    ty: LocalDefId,
    local: Local,
    projection: &'tcx [PlaceElem<'tcx>],
    field: FieldIdx,
    ctx: PlaceContext,
    location: Location,
}
