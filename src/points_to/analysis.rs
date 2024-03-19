use std::{
    collections::{HashMap, HashSet},
    path::Path,
};

use etrace::some_or;
use rustc_abi::VariantIdx;
use rustc_hir::ItemKind;
use rustc_index::IndexVec;
use rustc_middle::{
    hir::place::Place,
    mir::{
        visit::Visitor, BasicBlock, ConstantKind, Local, LocalDecl, Location, Operand, PlaceElem,
        Rvalue, Statement, StatementKind, TerminatorKind,
    },
    ty::{IntTy, Ty, TyCtxt, TyKind, TypeAndMut, UintTy},
};
use rustc_session::config::Input;
use rustc_span::def_id::{DefId, LocalDefId};

use crate::*;

pub type AnalysisResults = ();

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

    let bodies: Vec<_> = hir
        .items()
        .filter_map(|item_id| {
            let item = hir.item(item_id);
            if item.ident.name.as_str() == "main" {
                return None;
            }
            let local_def_id = item.owner_id.def_id;
            let def_id = local_def_id.to_def_id();
            let body = match item.kind {
                ItemKind::Fn(_, _, _) => tcx.optimized_mir(def_id),
                ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(def_id),
                _ => return None,
            };
            Some((local_def_id, body))
        })
        .collect();

    let mut visitor = FnPtrVisitor::new(tcx);
    for (_, body) in &bodies {
        visitor.visit_body(body);
    }
    let fn_ptrs = visitor.fn_ptrs;

    let mut fns = HashMap::new();
    let mut vars = HashMap::new();
    let mut ends = vec![];
    let mut alloc_ends: Vec<usize> = vec![];
    let mut allocs = vec![];
    for (local_def_id, body) in &bodies {
        let ptr = fn_ptrs.contains(local_def_id);
        let mut arg_end = 0;
        let len = ends.len();
        for (local, local_decl) in body.local_decls.iter_enumerated() {
            let index = ends.len();
            compute_ends(local_decl.ty, &mut ends, tcx);
            if ptr && body.arg_count == local.index() {
                arg_end = ends.len();
            }
            if ends.len() > index {
                vars.insert(Var::Local(*local_def_id, local), index);
            }
            if let TyKind::RawPtr(TypeAndMut { ty, .. }) = local_decl.ty.kind() {
                let mut ends = vec![];
                compute_ends(*ty, &mut ends, tcx);
                for (i, end) in ends.into_iter().enumerate() {
                    if alloc_ends.len() > i {
                        alloc_ends[i] = alloc_ends[i].max(end);
                    } else {
                        alloc_ends.push(end);
                    }
                }
            }
        }
        if ptr {
            if len == ends.len() {
                ends.push(len);
            } else {
                ends[len] = if arg_end > len { arg_end - 1 } else { arg_end };
            }
            fns.insert(*local_def_id, len);
        }
        for (bb, bbd) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call { func, .. } = &bbd.terminator().kind else { continue };
            let def_id = operand_to_fn(func).unwrap();
            if is_c_fn(def_id, tcx) {
                allocs.push(Var::Alloc(*local_def_id, bb));
            }
        }
    }
    for alloc in allocs {
        let len = ends.len();
        vars.insert(alloc, len);
        for end in &alloc_ends {
            ends.push(len + *end);
        }
    }
}

struct TyIndices {
    len: usize,
    fields: Vec<usize>,
}

fn foo<'tcx>(ty: Ty<'tcx>, tys: &mut HashMap<Ty<'tcx>, TyIndices>, tcx: TyCtxt<'tcx>) -> usize {
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Slice(_)
        | TyKind::Never
        | TyKind::Int(IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I128)
        | TyKind::Uint(UintTy::U8 | UintTy::U16 | UintTy::U32 | UintTy::U128) => 0,
        TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Foreign(_)
        | TyKind::RawPtr(_)
        | TyKind::Ref(_, _, _)
        | TyKind::FnDef(_, _)
        | TyKind::FnPtr(_) => 1,
        TyKind::Adt(adt_def, generic_args) => {
            if let Some(ty_indices) = tys.get(&ty) {
                ty_indices.len
            } else {
                if adt_def.variants().len() > 1 {
                    assert_eq!(adt_def.variants().len(), 2);
                    assert!(adt_def.variant(VariantIdx::from(0usize)).fields.is_empty());
                }
                let mut len = 0;
                let mut fields = vec![];
                for variant in adt_def.variants() {
                    for field in &variant.fields {
                        fields.push(len);
                        len += foo(field.ty(tcx, generic_args), tys, tcx);
                    }
                }
                let ty_indices = TyIndices { len, fields };
                tys.insert(ty, ty_indices);
                len
            }
        }
        TyKind::Array(ty, _) => foo(*ty, tys, tcx),
        TyKind::Tuple(ts) => {
            if let Some(ty_indices) = tys.get(&ty) {
                ty_indices.len
            } else {
                let mut len = 0;
                let mut fields = vec![];
                for ty in *ts {
                    fields.push(len);
                    len += foo(ty, tys, tcx);
                }
                let ty_indices = TyIndices { len, fields };
                tys.insert(ty, ty_indices);
                len
            }
        }
        _ => unreachable!("{:?}", ty),
    }
}

fn compute_ends<'tcx>(ty: Ty<'tcx>, ends: &mut Vec<usize>, tcx: TyCtxt<'tcx>) {
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Slice(_)
        | TyKind::Never
        | TyKind::Int(IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I128)
        | TyKind::Uint(UintTy::U8 | UintTy::U16 | UintTy::U32 | UintTy::U128) => {}
        TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Foreign(_)
        | TyKind::RawPtr(_)
        | TyKind::Ref(_, _, _)
        | TyKind::FnDef(_, _)
        | TyKind::FnPtr(_) => ends.push(ends.len()),
        TyKind::Adt(adt_def, generic_args) => {
            if adt_def.variants().len() > 1 {
                assert_eq!(adt_def.variants().len(), 2);
                assert!(adt_def.variant(VariantIdx::from(0usize)).fields.is_empty());
            }
            let len = ends.len();
            for variant in adt_def.variants() {
                for field in &variant.fields {
                    compute_ends(field.ty(tcx, generic_args), ends, tcx);
                }
            }
            if ends.len() > len {
                ends[len] = ends.len() - 1;
            }
        }
        TyKind::Array(ty, _) => compute_ends(*ty, ends, tcx),
        TyKind::Tuple(tys) => {
            let len = ends.len();
            for ty in *tys {
                compute_ends(ty, ends, tcx);
            }
            if ends.len() > len {
                ends[len] = ends.len() - 1;
            }
        }
        _ => unreachable!("{:?}", ty),
    }
}

#[derive(Clone, Copy)]
struct Context<'a, 'tcx> {
    locals: &'a IndexVec<Local, LocalDecl<'tcx>>,
    owner: LocalDefId,
    block: BasicBlock,
}

impl<'a, 'tcx> Context<'a, 'tcx> {
    fn new(
        locals: &'a IndexVec<Local, LocalDecl<'tcx>>,
        owner: LocalDefId,
        block: BasicBlock,
    ) -> Self {
        Self {
            locals,
            owner,
            block,
        }
    }
}

struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analyzer<'tcx> {
    fn transfer_stmt(&mut self, stmt: &Statement<'tcx>, ctx: Context<'_, 'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        let ty = l.ty(ctx.locals, self.tcx).ty;
    }
}

// fn place_to_index(place: Place<'_>) -> usize {
//     for proj in place.projection {
//         match proj {
//             PlaceElem::Deref => {}
//             PlaceElem::Field(f, _) => projection = projection.push(f.as_usize()),
//             PlaceElem::Index(_) => projection = projection.push(0),
//             _ => unreachable!(),
//         }
//     }
//     let loc = Loc::new(root, projection);
//     let deref = place.is_indirect_first_projection();
//     Self::new(false, deref, loc)
// }

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Var {
    Local(LocalDefId, Local),
    Alloc(LocalDefId, BasicBlock),
}

impl std::fmt::Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::Local(def_id, local) => write!(f, "{:?}::{:?}", def_id, local),
            Var::Alloc(def_id, bb) => write!(f, "{:?}::{:?}", def_id, bb),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ProjVar {
    var: Var,
    proj: usize,
}

impl std::fmt::Debug for ProjVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}+{}", self.var, self.proj)
    }
}

fn operand_to_fn(operand: &Operand<'_>) -> Option<DefId> {
    let constant = operand.constant()?;
    let ConstantKind::Val(_, ty) = constant.literal else { return None };
    let TyKind::FnDef(def_id, _) = ty.kind() else { return None };
    Some(*def_id)
}

fn is_c_fn(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    for data in tcx.def_path(def_id).data {
        if data.to_string().starts_with("{extern#") {
            return true;
        }
    }
    false
}

struct FnPtrVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    fn_ptrs: HashSet<LocalDefId>,
}

impl<'tcx> FnPtrVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            fn_ptrs: HashSet::new(),
        }
    }

    fn get_function(&self, operand: &Operand<'tcx>) -> Option<LocalDefId> {
        let constant = operand.constant()?;
        let ConstantKind::Val(_, ty) = constant.literal else { return None };
        let TyKind::FnDef(def_id, _) = ty.kind() else { return None };
        let local_def_id = def_id.as_local()?;
        if self.tcx.impl_of_method(*def_id).is_none() && !is_c_fn(*def_id, self.tcx) {
            Some(local_def_id)
        } else {
            None
        }
    }

    fn operand(&mut self, operand: &Operand<'tcx>) {
        let local_def_id = some_or!(self.get_function(operand), return);
        self.fn_ptrs.insert(local_def_id);
    }
}

impl<'tcx> Visitor<'tcx> for FnPtrVisitor<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Use(v)
            | Rvalue::Repeat(v, _)
            | Rvalue::Cast(_, v, _)
            | Rvalue::UnaryOp(_, v) => self.operand(v),
            Rvalue::BinaryOp(_, box (v1, v2)) => {
                self.operand(v1);
                self.operand(v2);
            }
            Rvalue::Aggregate(_, fs) => {
                for f in fs {
                    self.operand(f);
                }
            }
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }
}
