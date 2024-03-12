use std::{
    collections::{HashMap, HashSet},
    path::Path,
};

use rustc_hir::{def_id::LocalDefId, ItemKind};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        interpret::{ConstValue, GlobalAlloc, Scalar},
        AggregateKind, ConstantKind, Local, LocalDecl, Location, Operand, Place, PlaceElem, Rvalue,
        Statement, StatementKind, Terminator,
    },
    ty::{IntTy, Ty, TyCtxt, TyKind, UintTy},
};
use rustc_session::config::Input;
use rustc_span::def_id::DefId;

use super::*;
use crate::compile_util;

pub type AnalysisResults = HashMap<Loc, HashSet<Loc>>;

pub fn analyze_path(path: &Path) -> AnalysisResults {
    analyze_input(compile_util::path_to_input(path))
}

pub fn analyze_str(code: &str) -> AnalysisResults {
    analyze_input(compile_util::str_to_input(code))
}

fn analyze_input(input: Input) -> AnalysisResults {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, analyze).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>) -> AnalysisResults {
    let hir = tcx.hir();
    let mut analyzer = Analyzer::new(tcx);
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.name.as_str() == "main" {
            continue;
        }
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let body = match item.kind {
            ItemKind::Fn(_, _, _) => tcx.optimized_mir(def_id),
            ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(def_id),
            _ => continue,
        };
        for (block, bbd) in body.basic_blocks.iter_enumerated() {
            for (statement_index, stmt) in bbd.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                println!("{:?}", stmt);
                analyzer.transfer_stmt(stmt, &body.local_decls, local_def_id, location);
            }
            let terminator = bbd.terminator();
            let location = Location {
                block,
                statement_index: bbd.statements.len(),
            };
            analyzer.transfer_term(terminator, &body.local_decls, local_def_id, location);
        }
    }
    analyzer.solver.solutions()
}

struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    solver: Solver,
}

impl<'tcx> Analyzer<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            solver: Solver::new(),
        }
    }

    fn transfer_stmt(
        &mut self,
        stmt: &Statement<'tcx>,
        local_decls: &IndexVec<Local, LocalDecl<'tcx>>,
        owner: LocalDefId,
        location: Location,
    ) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        let ty = l.ty(local_decls, self.tcx).ty;
        let l = DLoc::from_place(*l, owner);
        match r {
            Rvalue::Use(r) => {
                if let Some(r) = self.transfer_op(r, owner, location) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::Repeat(r, _) => {
                if let Some(r) = self.transfer_op(r, owner, location) {
                    let TyKind::Array(ty, _) = ty.kind() else { unreachable!() };
                    self.transfer_assign(l.push(0), r, *ty);
                }
            }
            Rvalue::Ref(_, _, r) => {
                let r = DLoc::from_place(*r, owner).with_ref(true);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::ThreadLocalRef(r) => {
                let loc = Loc::new_root(LocRoot::Global(r.as_local().unwrap()));
                let r = DLoc::new_ref(loc);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::AddressOf(_, r) => {
                assert!(r.is_indirect_first_projection());
                let r = DLoc::from_place(*r, owner).with_deref(false);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::Len(_) => {}
            Rvalue::Cast(_, r, _) => {
                if let Some(r) = self.transfer_op(r, owner, location) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::BinaryOp(_, _) => {}
            Rvalue::CheckedBinaryOp(_, _) => unreachable!(),
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::UnaryOp(_, _) => {}
            Rvalue::Discriminant(_) => {}
            Rvalue::Aggregate(box kind, fs) => match kind {
                AggregateKind::Array(ty) => {
                    for f in fs.iter() {
                        if let Some(r) = self.transfer_op(f, owner, location) {
                            self.transfer_assign(l.clone().push(0), r, *ty);
                        }
                    }
                }
                AggregateKind::Adt(_, v_idx, _, _, idx) => {
                    let TyKind::Adt(adt_def, generic_args) = ty.kind() else { unreachable!() };
                    let variant = adt_def.variant(*v_idx);
                    for ((i, d), f) in variant.fields.iter_enumerated().zip(fs) {
                        if let Some(r) = self.transfer_op(f, owner, location) {
                            let ty = d.ty(self.tcx, generic_args);
                            let i = if let Some(idx) = idx { *idx } else { i };
                            self.transfer_assign(l.clone().push(i.as_usize()), r, ty);
                        }
                    }
                }
                _ => unreachable!(),
            },
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                let r = DLoc::from_place(*r, owner);
                self.transfer_assign(l, r, ty);
            }
        }
    }

    fn transfer_assign(&mut self, l: DLoc, r: DLoc, ty: Ty<'tcx>) {
        match ty.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Never
            | TyKind::Int(IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I128)
            | TyKind::Uint(UintTy::U8 | UintTy::U16 | UintTy::U32 | UintTy::U128) => {}
            TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Foreign(_)
            | TyKind::RawPtr(_)
            | TyKind::Ref(_, _, _)
            | TyKind::FnDef(_, _)
            | TyKind::FnPtr(_) => {
                self.transfer_assign_single(l, r);
            }
            TyKind::Adt(adt_def, generic_args) => {
                for v in adt_def.variants() {
                    for (i, f) in v.fields.iter_enumerated() {
                        let i = i.as_usize();
                        let ty = f.ty(self.tcx, generic_args);
                        self.transfer_assign(l.clone().push(i), r.clone().push(i), ty);
                    }
                }
            }
            TyKind::Array(ty, _) => {
                self.transfer_assign(l.push(0), r.push(0), *ty);
            }
            TyKind::Tuple(tys) => {
                for (i, ty) in tys.iter().enumerate() {
                    self.transfer_assign(l.clone().push(i), r.clone().push(i), ty);
                }
            }
            _ => unreachable!("{:?}", ty),
        }
    }

    fn transfer_assign_single(&mut self, l: DLoc, r: DLoc) {
        assert!(!l.r#ref);
        match (l.deref, r.r#ref, r.deref) {
            (true, true, _) => unreachable!(),
            (true, false, true) => unreachable!(),
            (true, false, false) => {
                let l_root = l.loc.only_root();
                if let Some(ts) = self.solver.solution(&l_root) {
                    for t in ts.clone() {
                        self.solver
                            .add_edge(r.loc.clone(), t.extend(l.loc.projection.clone()));
                    }
                }
                self.solver.add_to(l_root, r.loc, l.loc.projection);
                self.solver.propagate();
            }
            (false, true, true) => {
                if r.loc.projection.is_empty() {
                    self.solver.add_edge(r.loc, l.loc);
                    self.solver.propagate();
                } else {
                    let r_root = r.loc.only_root();
                    if let Some(ts) = self.solver.solution(&r_root) {
                        for t in ts.clone() {
                            self.solver
                                .add_token(t.extend(r.loc.projection.clone()), l.loc.clone());
                        }
                    }
                    self.solver.add_token_to(r_root, l.loc, r.loc.projection);
                    self.solver.propagate();
                }
            }
            (false, true, false) => {
                self.solver.add_token(r.loc, l.loc);
                self.solver.propagate();
            }
            (false, false, true) => {
                let r_root = r.loc.only_root();
                if let Some(ts) = self.solver.solution(&r_root) {
                    for t in ts.clone() {
                        self.solver
                            .add_edge(t.extend(r.loc.projection.clone()), l.loc.clone());
                    }
                }
                self.solver.add_from(r_root, l.loc, r.loc.projection);
                self.solver.propagate();
            }
            (false, false, false) => {
                self.solver.add_edge(r.loc, l.loc);
                self.solver.propagate();
            }
        }
    }

    fn transfer_op(
        &mut self,
        op: &Operand<'tcx>,
        owner: LocalDefId,
        location: Location,
    ) -> Option<DLoc> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => Some(DLoc::from_place(*place, owner)),
            Operand::Constant(box constant) => match constant.literal {
                ConstantKind::Ty(_) => unreachable!(),
                ConstantKind::Unevaluated(_, _) => None,
                ConstantKind::Val(value, ty) => match value {
                    ConstValue::Scalar(scalar) => match scalar {
                        Scalar::Int(_) => None,
                        Scalar::Ptr(ptr, _) => match self.tcx.global_alloc(ptr.provenance) {
                            GlobalAlloc::Static(def_id) => {
                                let loc = Loc::new_root(LocRoot::Global(def_id.as_local()?));
                                Some(DLoc::new_ref(loc))
                            }
                            GlobalAlloc::Memory(_) => {
                                let loc = Loc::new_root(LocRoot::Alloc(owner, location));
                                Some(DLoc::new_ref(loc))
                            }
                            _ => unreachable!(),
                        },
                    },
                    ConstValue::ZeroSized => {
                        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                        let loc = Loc::new_root(LocRoot::Global(def_id.as_local()?));
                        Some(DLoc::new_ref(loc))
                    }
                    _ => unreachable!(),
                },
            },
        }
    }

    fn transfer_term(
        &mut self,
        term: &Terminator<'tcx>,
        local_decls: &IndexVec<Local, LocalDecl<'tcx>>,
        owner: LocalDefId,
        location: Location,
    ) {
    }

    fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocRoot {
    Global(LocalDefId),
    Local(LocalDefId, Local),
    Alloc(LocalDefId, Location),
}

impl std::fmt::Debug for LocRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocRoot::Global(def_id) => write!(f, "{:?}", def_id),
            LocRoot::Local(def_id, local) => write!(f, "{:?}:{:?}", def_id, local),
            LocRoot::Alloc(def_id, location) => write!(f, "{:?}:{:?}", def_id, location),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Loc {
    root: LocRoot,
    projection: Vec<usize>,
}

impl std::fmt::Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.root)?;
        for i in &self.projection {
            write!(f, ".{}", i)?;
        }
        Ok(())
    }
}

impl Loc {
    #[inline]
    pub fn new(root: LocRoot, projection: Vec<usize>) -> Self {
        Self { root, projection }
    }

    #[inline]
    pub fn new_root(root: LocRoot) -> Self {
        Self::new(root, vec![])
    }

    #[inline]
    pub fn push(mut self, proj: usize) -> Self {
        self.projection.push(proj);
        self
    }

    #[inline]
    pub fn extend<I: IntoIterator<Item = usize>>(mut self, proj: I) -> Self {
        self.projection.extend(proj);
        self
    }

    #[inline]
    fn only_root(&self) -> Self {
        Self::new_root(self.root)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DLoc {
    r#ref: bool,
    deref: bool,
    loc: Loc,
}

impl DLoc {
    #[inline]
    fn new(rf: bool, deref: bool, loc: Loc) -> Self {
        Self {
            r#ref: rf,
            deref,
            loc,
        }
    }

    #[inline]
    fn new_loc(loc: Loc) -> Self {
        Self::new(false, false, loc)
    }

    #[inline]
    fn new_deref(loc: Loc) -> Self {
        Self::new(false, true, loc)
    }

    #[inline]
    fn new_ref(loc: Loc) -> Self {
        Self::new(true, false, loc)
    }

    #[inline]
    fn push(mut self, proj: usize) -> Self {
        self.loc = self.loc.push(proj);
        self
    }

    #[inline]
    fn extend<I: IntoIterator<Item = usize>>(mut self, proj: I) -> Self {
        self.loc = self.loc.extend(proj);
        self
    }

    #[inline]
    fn with_deref(mut self, deref: bool) -> Self {
        self.deref = deref;
        self
    }

    #[inline]
    fn with_ref(mut self, r#ref: bool) -> Self {
        self.r#ref = r#ref;
        self
    }

    fn from_place(place: Place<'_>, owner: LocalDefId) -> Self {
        let root = LocRoot::Local(owner, place.local);
        let projection = place
            .projection
            .iter()
            .filter_map(|proj| match proj {
                PlaceElem::Deref => None,
                PlaceElem::Field(f, _) => Some(f.as_usize()),
                PlaceElem::Index(_) => Some(0),
                _ => unreachable!(),
            })
            .collect();
        let loc = Loc::new(root, projection);
        let deref = place.is_indirect_first_projection();
        Self::new(false, deref, loc)
    }
}
