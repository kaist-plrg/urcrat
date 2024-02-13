use std::{collections::HashSet, path::Path};

use etrace::some_or;
use relational::{AbsMem, AccPath, Obj};
use rustc_abi::FieldIdx;
use rustc_hir::ItemKind;
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

use crate::{compile_util, relational, ty_finder};

pub fn analyze_path(path: &Path) {
    analyze_input(compile_util::path_to_input(path))
}

pub fn analyze_str(code: &str) {
    analyze_input(compile_util::str_to_input(code))
}

fn analyze_input(input: Input) {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, analyze).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>) {
    let visitor = ty_finder::TyVisitor::new(tcx);
    let foreign_tys = visitor.find_foreign_tys(tcx);
    let prog_info = relational::ProgInfo::new(tcx);

    for item_id in tcx.hir().items() {
        let item = tcx.hir().item(item_id);
        if !matches!(item.kind, ItemKind::Fn(_, _, _)) {
            continue;
        }
        let local_def_id = item_id.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let body = tcx.optimized_mir(def_id);
        let mut visitor = PlaceVisitor::new(tcx, &body.local_decls, &foreign_tys);
        visitor.visit_body(body);
        if !visitor.accesses.is_empty() {
            println!("{:?}", local_def_id);
            let states = relational::analyze_fn(tcx, &prog_info, local_def_id);
            for access in &visitor.accesses {
                let state = &states[&access.location];
                let (path, is_deref) = access.get_path(state);
                let g = state.g();
                let obj = g.get_obj(&path, is_deref);
                println!("{:?}", access.ctx);
                if let Some(obj) = obj {
                    let Obj::Compound(fields) = obj else { unreachable!() };
                    for (i, obj) in fields {
                        if let Obj::Ptr(loc) = obj {
                            if loc.projection().is_empty() {
                                let node = &g.nodes[loc.root()];
                                if let Some(v) = node.at_addr {
                                    println!("{}: {}", i, v);
                                } else {
                                    println!("{}: loc<{:?}>", i, obj);
                                }
                            } else {
                                println!("{}: loc<{:?}>", i, obj);
                            }
                        } else {
                            println!("{}: {:?}", i, obj);
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
    local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
    foreign_tys: &'a HashSet<LocalDefId>,
    accesses: Vec<FieldAccess<'tcx>>,
}

impl<'tcx, 'a> PlaceVisitor<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
        foreign_tys: &'a HashSet<LocalDefId>,
    ) -> Self {
        Self {
            tcx,
            local_decls,
            foreign_tys,
            accesses: vec![],
        }
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
