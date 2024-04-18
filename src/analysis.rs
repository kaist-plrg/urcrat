use std::{collections::HashSet, path::Path};

use etrace::some_or;
use relational::{AbsMem, AccPath, Obj};
use rustc_abi::FieldIdx;
use rustc_hir::{def_id::DefId, ItemKind};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        visit::{PlaceContext, Visitor},
        Local, LocalDecl, Location, Place, PlaceElem, ProjectionElem,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_session::config::Input;
use rustc_span::def_id::LocalDefId;

use crate::*;

#[derive(Debug, Clone)]
pub struct Config {
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
    let visitor = ty_finder::TyVisitor::new(tcx);
    let foreign_tys = visitor.find_foreign_tys(tcx);
    let may_points_to = points_to::analyze(tcx);

    for item_id in tcx.hir().items() {
        let item = tcx.hir().item(item_id);
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
            let states = relational::analyze_fn(tcx, &may_points_to, local_def_id, true);
            for access in &visitor.accesses {
                let state = &states[&access.location];
                let (path, is_deref) = access.get_path(state);
                let g = state.g();
                let obj = g.get_obj(&path, is_deref);
                println!(
                    "{:?} {:?}",
                    body.source_info(access.location).span,
                    access.ctx
                );
                println!("{:?} {:?}", access.location, body.stmt_at(access.location));
                // println!("{:?}", state);
                if let Some(obj) = obj {
                    let Obj::Compound(fields) = obj else { continue };
                    for (i, obj) in fields {
                        if let Obj::Ptr(loc) = obj {
                            if let Some(obj) = g.obj_at_location(loc) {
                                if let Obj::AtAddr(n) = obj {
                                    println!("{:?}: {}", i, n);
                                } else {
                                    println!("{:?}: loc<{:?}>", i, obj);
                                }
                            } else {
                                println!("{:?}: loc<{:?}>", i, obj);
                            }
                        } else {
                            println!("{:?}: {:?}", i, obj);
                        }
                    }
                } else {
                    println!("None");
                }
            }
        }
    }
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

impl FieldAccess<'_> {
    fn get_path(&self, state: &AbsMem) -> (AccPath, bool) {
        assert!(!self.projection.is_empty());
        AccPath::from_local_projection(
            self.local,
            &self.projection[..self.projection.len() - 1],
            state,
        )
    }
}
