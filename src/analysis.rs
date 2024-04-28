use std::{
    collections::{BTreeMap, HashMap, HashSet},
    path::Path,
};

use etrace::some_or;
use relational::{AbsMem, AccPath, Obj};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::{def_id::DefId, definitions::DefPathDataName, ItemKind};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        visit::{PlaceContext, Visitor},
        HasLocalDecls, Local, LocalDecl, Location, Place, PlaceElem, ProjectionElem,
    },
    ty::{List, TyCtxt, TyKind},
};
use rustc_session::config::Input;
use rustc_span::{def_id::LocalDefId, Span};
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
    let foreign_tys = visitor.find_foreign_tys(tcx);
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx);
    let pre = points_to::pre_analyze(&tss, tcx);
    let solutions = conf
        .solutions
        .clone()
        .unwrap_or_else(|| points_to::analyze(&pre, &tss, tcx));
    let may_points_to = points_to::post_analyze(pre, solutions, &tss, tcx);

    for item_id in hir.items() {
        let item = hir.item(item_id);
        if !matches!(item.kind, ItemKind::Struct(_, _)) {
            continue;
        }
        let local_def_id = item_id.owner_id.def_id;
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
        let unions: Vec<_> = variant
            .fields
            .iter()
            .filter_map(|f| {
                let TyKind::Adt(adt_def, _) = f.ty(tcx, List::empty()).kind() else { return None };
                if !adt_def.is_union() {
                    return None;
                }
                let def_id = adt_def.did();
                let name = tcx.def_path(def_id).data.last().unwrap().data.name();
                let DefPathDataName::Named(name) = name else { return None };
                if name.to_ident_string().starts_with("C2RustUnnamed") {
                    Some(def_id.expect_local())
                } else {
                    None
                }
            })
            .collect();
        if !unions.is_empty() {
            println!("{:?} {:?}", local_def_id, unions);
        }
    }

    let mut accesses: HashMap<_, BTreeMap<_, Vec<_>>> = HashMap::new();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if !matches!(item.kind, ItemKind::Fn(_, _, _)) {
            continue;
        }
        let local_def_id = item_id.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let body = tcx.optimized_mir(def_id);
        let mut visitor = PlaceVisitor::new(tcx, conf, &body.local_decls, &foreign_tys);
        visitor.visit_body(body);
        if !visitor.accesses.is_empty() {
            println!("{:?}", local_def_id);
            let states = relational::analyze_fn(local_def_id, &tss, &may_points_to, true, tcx);
            for access in &visitor.accesses {
                let span = body.source_info(access.location).span;
                let tags = compute_tags(*access, &states, &body.local_decls, tcx);
                let aa = AnalyzedAccess {
                    span,
                    ctx: access.ctx,
                    tags,
                };
                accesses
                    .entry(access.ty)
                    .or_default()
                    .entry(access.field)
                    .or_default()
                    .push(aa);
            }
        }
    }

    let source_map = tcx.sess.source_map();
    for (ty, accesses) in accesses {
        println!("[[Type {:?}]]", ty);
        for (f, accesses) in accesses {
            println!("[Field {:?}]", f);
            for aa in accesses {
                let fname = source_map.span_to_filename(aa.span);
                let file_name = fname.prefer_remapped().to_string();
                let file = source_map.get_source_file(&fname).unwrap();
                let (line, _, _) = file.lookup_file_pos_with_col_display(aa.span.lo());
                let tags: String = aa
                    .tags
                    .iter()
                    .map(|(f, t)| format!("{}: {}", f, t))
                    .intersperse(", ".to_string())
                    .collect();
                println!("{}, {:?}, {}:{:?}", tags, aa.ctx, file_name, line);
            }
        }
    }
}

fn compute_tags<'tcx, D: HasLocalDecls<'tcx> + ?Sized>(
    access: FieldAccess<'tcx>,
    states: &HashMap<Location, AbsMem>,
    local_decls: &D,
    tcx: TyCtxt<'tcx>,
) -> Vec<(u32, u128)> {
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
            Some((*f, *n))
        })
        .collect();
    v.sort_by_key(|(f, _)| *f);
    v
}

struct PlaceVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    conf: &'a Config,
    local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
    foreign_tys: &'a HashSet<LocalDefId>,
    accesses: Vec<FieldAccess<'tcx>>,
}

impl<'tcx, 'a> PlaceVisitor<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        conf: &'a Config,
        local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
        foreign_tys: &'a HashSet<LocalDefId>,
    ) -> Self {
        Self {
            tcx,
            conf,
            local_decls,
            foreign_tys,
            accesses: vec![],
        }
    }

    fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }
}

impl<'tcx> Visitor<'tcx> for PlaceVisitor<'tcx, '_> {
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
                if !adt_def.is_union() {
                    continue;
                }
                if !self.conf.unions.is_empty()
                    && !self
                        .conf
                        .unions
                        .contains(&self.def_id_to_string(adt_def.did()))
                {
                    continue;
                }
                let def_id = some_or!(adt_def.did().as_local(), continue);
                if self.foreign_tys.contains(&def_id) {
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
}

#[derive(Debug, Clone, Copy)]
struct FieldAccess<'tcx> {
    #[allow(unused)]
    ty: LocalDefId,
    local: Local,
    projection: &'tcx [PlaceElem<'tcx>],
    #[allow(unused)]
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

struct AnalyzedAccess {
    span: Span,
    ctx: PlaceContext,
    tags: Vec<(u32, u128)>,
}
