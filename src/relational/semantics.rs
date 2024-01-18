use std::collections::HashSet;

use rustc_abi::FieldIdx;
use rustc_middle::{
    mir::{
        interpret::{ConstValue, Scalar},
        AggregateKind, BinOp, CastKind, ConstantKind, Local, Location, Operand, Place, PlaceElem,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
    },
    ty::{adjustment::PointerCoercion, IntTy, Ty, TyKind, UintTy},
};

use super::*;
use crate::*;

impl<'tcx> Analyzer<'tcx, '_> {
    pub fn transfer_stmt(&self, stmt: &Statement<'tcx>, state: &mut AbsMem) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        if l.projection.is_empty() {
            state.gm().invalidate_symbolic(l.local);
        }
        if l.is_indirect_first_projection() {
            let graph = state.gm();
            let l_id = graph.deref_local_id(l.local);
            for (local, depth) in self.find_may_aliases(l.local) {
                graph.invalidate_deref(local, depth, l_id);
            }
        }
        let (l, l_deref) = AccPath::from_place(*l, state);
        let suffixes = self.get_path_suffixes(&l, l_deref);
        let empty_suffix = || suffixes.iter().all(|s| s.is_empty());
        match r {
            Rvalue::Use(r) => {
                let r = self.transfer_op(r, state);
                state.gm().assign_with_suffixes(&l, l_deref, &r, &suffixes);
            }
            Rvalue::Cast(kind, r, ty) => match kind {
                CastKind::IntToInt => {
                    assert!(empty_suffix());
                    let rty = self.ty(r);
                    let r = self.transfer_op(r, state);
                    if let OpVal::Int(v) = r {
                        let v = match ty.kind() {
                            TyKind::Int(int_ty) => match int_ty {
                                IntTy::Isize => to_isize(v, rty),
                                IntTy::I8 => to_i8(v, rty),
                                IntTy::I16 => to_i16(v, rty),
                                IntTy::I32 => to_i32(v, rty),
                                IntTy::I64 => to_i64(v, rty),
                                IntTy::I128 => to_i128(v, rty),
                            },
                            TyKind::Uint(uint_ty) => match uint_ty {
                                UintTy::Usize => to_usize(v, rty),
                                UintTy::U8 => to_u8(v, rty),
                                UintTy::U16 => to_u16(v, rty),
                                UintTy::U32 => to_u32(v, rty),
                                UintTy::U64 => to_u64(v, rty),
                                UintTy::U128 => to_u128(v, rty),
                            },
                            _ => unreachable!(),
                        };
                        state.gm().assign(&l, l_deref, &OpVal::Int(v));
                    } else if matches!(ty.kind(), TyKind::Uint(UintTy::Usize)) {
                        state.gm().assign(&l, l_deref, &r);
                    } else {
                        state.gm().assign(&l, l_deref, &OpVal::Other);
                    }
                }
                CastKind::PointerCoercion(coercion) => {
                    if *coercion == PointerCoercion::MutToConstPointer {
                        let r = self.transfer_op(r, state);
                        state.gm().assign_with_suffixes(&l, l_deref, &r, &suffixes);
                    } else {
                        state
                            .gm()
                            .assign_with_suffixes(&l, l_deref, &OpVal::Other, &suffixes);
                    }
                }
                _ => {
                    state
                        .gm()
                        .assign_with_suffixes(&l, l_deref, &OpVal::Other, &suffixes);
                }
            },
            Rvalue::Repeat(r, len) => {
                let r = self.transfer_op(r, state);
                let len = len.try_to_scalar_int().unwrap().try_to_u64().unwrap();
                for i in 0..len {
                    let l = l.extended(&[AccElem::Int(i as _)]);
                    let suffixes = self.get_path_suffixes(&l, l_deref);
                    state.gm().assign_with_suffixes(&l, l_deref, &r, &suffixes);
                }
            }
            Rvalue::Ref(_, _, r) => {
                assert!(empty_suffix());
                assert!(!l_deref);
                let (r, r_deref) = AccPath::from_place(*r, state);
                state.gm().x_eq_ref_y(&l, &r, r_deref);
            }
            Rvalue::ThreadLocalRef(_) => {
                assert!(empty_suffix());
                state.gm().assign(&l, l_deref, &OpVal::Other);
            }
            Rvalue::AddressOf(_, r) => {
                assert!(empty_suffix());
                assert_eq!(r.projection.len(), 1);
                let (path, is_deref) = AccPath::from_place(*r, state);
                assert!(is_deref);
                let v = OpVal::Place(path, false);
                state.gm().assign(&l, l_deref, &v);
            }
            Rvalue::Len(_) => unreachable!(),
            Rvalue::BinaryOp(op, box (r1, r2)) => {
                assert!(empty_suffix());
                let ty = self.ty(r1);
                let r1 = self.transfer_op(r1, state);
                let r2 = self.transfer_op(r2, state);
                if let (OpVal::Int(v1), OpVal::Int(v2)) = (r1, r2) {
                    let v = match op {
                        BinOp::Add => v1 + v2,
                        BinOp::Sub => v1 - v2,
                        BinOp::Mul => v1 * v2,
                        BinOp::Div => div(v1, v2, ty),
                        BinOp::Rem => rem(v1, v2, ty),
                        BinOp::BitXor => v1 ^ v2,
                        BinOp::BitAnd => v1 & v2,
                        BinOp::BitOr => v1 | v2,
                        BinOp::Shl => shl(v1, v2, ty),
                        BinOp::Shr => shr(v1, v2, ty),
                        BinOp::Eq => (v1 == v2) as u128,
                        BinOp::Lt => lt(v1, v2, ty),
                        BinOp::Le => le(v1, v2, ty),
                        BinOp::Ne => (v1 != v2) as u128,
                        BinOp::Ge => ge(v1, v2, ty),
                        BinOp::Gt => gt(v1, v2, ty),
                        _ => unreachable!(),
                    };
                    state.gm().assign(&l, l_deref, &OpVal::Int(v));
                } else {
                    state.gm().assign(&l, l_deref, &OpVal::Other);
                }
            }
            Rvalue::CheckedBinaryOp(_, _) => unreachable!(),
            Rvalue::UnaryOp(op, r) => {
                assert!(empty_suffix());
                let ty = self.ty(r);
                let r = self.transfer_op(r, state);
                if let OpVal::Int(v) = r {
                    let v = match op {
                        UnOp::Not => !v,
                        UnOp::Neg => neg(v, ty),
                    };
                    state.gm().assign(&l, l_deref, &OpVal::Int(v));
                } else {
                    state.gm().assign(&l, l_deref, &OpVal::Other);
                }
            }
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::Discriminant(_) => {
                assert!(empty_suffix());
                state.gm().assign(&l, l_deref, &OpVal::Other);
            }
            Rvalue::Aggregate(box kind, rs) => {
                let idx = if let AggregateKind::Adt(_, _, _, _, idx) = kind {
                    idx.as_ref()
                } else {
                    None
                };
                if let Some(field) = idx {
                    assert_eq!(rs.len(), 1);
                    let op = &rs[FieldIdx::from_usize(0)];
                    let v = self.transfer_op(op, state);
                    let l = l.extended(&[AccElem::Int(field.index())]);
                    let suffixes = self.get_path_suffixes(&l, l_deref);
                    state.gm().assign_with_suffixes(&l, l_deref, &v, &suffixes);
                } else {
                    for (field, op) in rs.iter_enumerated() {
                        let v = self.transfer_op(op, state);
                        let l = l.extended(&[AccElem::Int(field.index())]);
                        let suffixes = self.get_path_suffixes(&l, l_deref);
                        state.gm().assign_with_suffixes(&l, l_deref, &v, &suffixes);
                    }
                }
            }
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                assert!(empty_suffix());
                assert!(r.projection.is_empty());
                let (path, is_deref) = AccPath::from_place(*r, state);
                assert!(!is_deref);
                let v = OpVal::Place(path, false);
                state.gm().assign(&l, l_deref, &v);
            }
        }
    }

    fn transfer_op(&self, op: &Operand<'_>, state: &AbsMem) -> OpVal {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let (path, is_deref) = AccPath::from_place(*place, state);
                let int_opt = if is_deref {
                    state.g().get_deref_x_as_int(&path)
                } else {
                    state.g().get_x_as_int(&path)
                };
                if let Some(i) = int_opt {
                    OpVal::Int(i)
                } else {
                    OpVal::Place(path, is_deref)
                }
            }
            Operand::Constant(box constant) => match constant.literal {
                ConstantKind::Ty(_) => unreachable!(),
                ConstantKind::Unevaluated(_, _) => OpVal::Other,
                ConstantKind::Val(value, ty) => match value {
                    ConstValue::Scalar(scalar) => match scalar {
                        Scalar::Int(i) => match ty.kind() {
                            TyKind::Int(int_ty) => {
                                let v = match int_ty {
                                    IntTy::Isize => i.try_to_i64().unwrap() as _,
                                    IntTy::I8 => i.try_to_i8().unwrap() as _,
                                    IntTy::I16 => i.try_to_i16().unwrap() as _,
                                    IntTy::I32 => i.try_to_i32().unwrap() as _,
                                    IntTy::I64 => i.try_to_i64().unwrap() as _,
                                    IntTy::I128 => i.try_to_i128().unwrap() as _,
                                };
                                OpVal::Int(v)
                            }
                            TyKind::Uint(uint_ty) => {
                                let v = match uint_ty {
                                    UintTy::Usize => i.try_to_u64().unwrap() as _,
                                    UintTy::U8 => i.try_to_u8().unwrap() as _,
                                    UintTy::U16 => i.try_to_u16().unwrap() as _,
                                    UintTy::U32 => i.try_to_u32().unwrap() as _,
                                    UintTy::U64 => i.try_to_u64().unwrap() as _,
                                    UintTy::U128 => i.try_to_u128().unwrap(),
                                };
                                OpVal::Int(v)
                            }
                            _ => OpVal::Other,
                        },
                        Scalar::Ptr(_, _) => OpVal::Other,
                    },
                    ConstValue::ZeroSized => OpVal::Other,
                    ConstValue::Slice { .. } => unreachable!(),
                    ConstValue::ByRef { .. } => unreachable!(),
                },
            },
        }
    }

    pub fn transfer_term(
        &self,
        term: &Terminator<'tcx>,
        state: &AbsMem,
    ) -> Vec<(Location, AbsMem)> {
        match &term.kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Assert { target, .. }
            | TerminatorKind::InlineAsm {
                destination: Some(target),
                ..
            } => {
                let location = Location {
                    block: *target,
                    statement_index: 0,
                };
                vec![(location, state.clone())]
            }
            TerminatorKind::Return
            | TerminatorKind::InlineAsm {
                destination: None, ..
            }
            | TerminatorKind::Call { target: None, .. } => vec![],
            TerminatorKind::SwitchInt { discr, targets } => match self.transfer_op(discr, state) {
                OpVal::Place(discr, is_deref) => targets
                    .iter()
                    .map(|(v, target)| {
                        let location = Location {
                            block: target,
                            statement_index: 0,
                        };
                        let mut state = state.clone();
                        state.gm().filter_x_int(&discr, is_deref, v);
                        (location, state)
                    })
                    .chain(std::iter::once((
                        Location {
                            block: targets.otherwise(),
                            statement_index: 0,
                        },
                        state.clone(),
                    )))
                    .collect(),
                OpVal::Int(i) => {
                    let target_opt = targets.iter().find(|(v, _)| i == *v);
                    let target = if let Some((_, target)) = target_opt {
                        target
                    } else {
                        targets.otherwise()
                    };
                    let location = Location {
                        block: target,
                        statement_index: 0,
                    };
                    vec![(location, state.clone())]
                }
                OpVal::Other => targets
                    .all_targets()
                    .iter()
                    .map(|target| {
                        let location = Location {
                            block: *target,
                            statement_index: 0,
                        };
                        (location, state.clone())
                    })
                    .collect(),
            },
            TerminatorKind::Call {
                func: _func,
                args: _args,
                destination: _destination,
                target: Some(_),
                ..
            } => {
                todo!()
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum OpVal {
    Place(AccPath, bool),
    Int(u128),
    Other,
}

impl OpVal {
    #[inline]
    pub fn extended(&self, proj: &[AccElem]) -> Self {
        let mut new = self.clone();
        new.extend_projection(proj);
        new
    }

    #[inline]
    fn extend_projection(&mut self, proj: &[AccElem]) {
        match self {
            OpVal::Place(path, _) => path.extend_projection(proj),
            OpVal::Int(_) => assert!(proj.is_empty()),
            OpVal::Other => {}
        }
    }
}

#[derive(Debug, Clone)]
pub struct AccPath {
    pub local: Local,
    pub projection: Vec<AccElem>,
}

impl AccPath {
    #[inline]
    pub fn new(local: Local, projection: Vec<AccElem>) -> Self {
        Self { local, projection }
    }

    fn from_place(place: Place<'_>, state: &AbsMem) -> (Self, bool) {
        let root = place.local;
        let projections = place
            .projection
            .iter()
            .filter_map(|e| AccElem::from_elem(e, state))
            .collect();
        let is_deref = place.is_indirect_first_projection();
        (AccPath::new(root, projections), is_deref)
    }

    #[inline]
    pub fn extended(&self, proj: &[AccElem]) -> Self {
        let mut new = self.clone();
        new.extend_projection(proj);
        new
    }

    #[inline]
    fn extend_projection(&mut self, proj: &[AccElem]) {
        self.projection.extend(proj.to_owned());
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum AccElem {
    Int(usize),
    Symbolic(HashSet<Local>),
}

impl std::fmt::Debug for AccElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccElem::Int(i) => write!(f, "{}", i),
            AccElem::Symbolic(s) => write!(f, "{:?}", s),
        }
    }
}

impl AccElem {
    fn from_elem(proj: PlaceElem<'_>, state: &AbsMem) -> Option<Self> {
        match proj {
            ProjectionElem::Deref => None,
            ProjectionElem::Field(i, _) => Some(AccElem::Int(i.index())),
            ProjectionElem::Index(local) => {
                let path = AccPath::new(local, vec![]);
                if let Some(i) = state.g().get_x_as_int(&path) {
                    Some(AccElem::Int(i as usize))
                } else {
                    Some(AccElem::Symbolic(state.g().find_aliases(local)))
                }
            }
            ProjectionElem::ConstantIndex { .. } => unreachable!(),
            ProjectionElem::Subslice { .. } => unreachable!(),
            ProjectionElem::Downcast(_, _) => unreachable!(),
            ProjectionElem::OpaqueCast(_) => unreachable!(),
        }
    }
}

macro_rules! create_div_fn {
    ($name:ident, $op:tt) => {
        fn $name(n: u128, m: u128, ty: Ty<'_>) -> u128 {
            match ty.kind() {
                TyKind::Int(int_ty) => {
                    match int_ty {
                        IntTy::Isize => (n as isize $op m as isize) as u128,
                        IntTy::I8 => (n as i8 $op m as i8) as u128,
                        IntTy::I16 => (n as i16 $op m as i16) as u128,
                        IntTy::I32 => (n as i32 $op m as i32) as u128,
                        IntTy::I64 => (n as i64 $op m as i64) as u128,
                        IntTy::I128 => (n as i128 $op m as i128) as u128,
                    }
                }
                TyKind::Uint(uint_ty) => {
                    match uint_ty {
                        UintTy::Usize => (n as usize $op m as usize) as u128,
                        UintTy::U8 => (n as u8 $op m as u8) as u128,
                        UintTy::U16 => (n as u16 $op m as u16) as u128,
                        UintTy::U32 => (n as u32 $op m as u32) as u128,
                        UintTy::U64 => (n as u64 $op m as u64) as u128,
                        UintTy::U128 => n $op m,
                    }
                }
                _ => panic!(),
            }
        }
    }
}

create_div_fn!(div, /);
create_div_fn!(rem, %);

macro_rules! create_shift_fn {
    ($name:ident, $op:tt) => {
        fn $name(n: u128, m: u128, ty: Ty<'_>) -> u128 {
            match ty.kind() {
                TyKind::Int(int_ty) => {
                    match int_ty {
                        IntTy::Isize => ((n as isize) $op m) as u128,
                        IntTy::I8 => ((n as i8) $op m) as u128,
                        IntTy::I16 => ((n as i16) $op m) as u128,
                        IntTy::I32 => ((n as i32) $op m) as u128,
                        IntTy::I64 => ((n as i64) $op m) as u128,
                        IntTy::I128 => ((n as i128) $op m) as u128,
                    }
                }
                TyKind::Uint(uint_ty) => {
                    match uint_ty {
                        UintTy::Usize => ((n as usize) $op m) as u128,
                        UintTy::U8 => ((n as u8) $op m) as u128,
                        UintTy::U16 => ((n as u16) $op m) as u128,
                        UintTy::U32 => ((n as u32) $op m) as u128,
                        UintTy::U64 => ((n as u64) $op m) as u128,
                        UintTy::U128 => n $op m,
                    }
                }
                _ => panic!(),
            }
        }
    }
}

create_shift_fn!(shl, <<);
create_shift_fn!(shr, >>);

macro_rules! create_cmp_fn {
    ($name:ident, $op:tt) => {
        fn $name(n: u128, m: u128, ty: Ty<'_>) -> u128 {
            match ty.kind() {
                TyKind::Int(int_ty) => {
                    match int_ty {
                        IntTy::Isize => ((n as isize) $op m as isize) as u128,
                        IntTy::I8 => ((n as i8) $op m as i8) as u128,
                        IntTy::I16 => ((n as i16) $op m as i16) as u128,
                        IntTy::I32 => ((n as i32) $op m as i32) as u128,
                        IntTy::I64 => ((n as i64) $op m as i64) as u128,
                        IntTy::I128 => ((n as i128) $op m as i128) as u128,
                    }
                }
                TyKind::Uint(uint_ty) => {
                    match uint_ty {
                        UintTy::Usize => ((n as usize) $op m as usize) as u128,
                        UintTy::U8 => ((n as u8) $op m as u8) as u128,
                        UintTy::U16 => ((n as u16) $op m as u16) as u128,
                        UintTy::U32 => ((n as u32) $op m as u32) as u128,
                        UintTy::U64 => ((n as u64) $op m as u64) as u128,
                        UintTy::U128 => (n $op m) as u128,
                    }
                }
                TyKind::Bool => ((n != 0) $op (m != 0)) as u128,
                _ => panic!(),
            }
        }
    }
}

create_cmp_fn!(lt, <);
create_cmp_fn!(le, <=);
create_cmp_fn!(ge, >=);
create_cmp_fn!(gt, >);

macro_rules! create_cast_fn {
    ($name:ident, $typ:ty) => {
        fn $name(n: u128, ty: Ty<'_>) -> u128 {
            #[allow(trivial_numeric_casts)]
            match ty.kind() {
                TyKind::Int(int_ty) => match int_ty {
                    IntTy::Isize => (n as isize) as $typ as u128,
                    IntTy::I8 => (n as i8) as $typ as u128,
                    IntTy::I16 => (n as i16) as $typ as u128,
                    IntTy::I32 => (n as i32) as $typ as u128,
                    IntTy::I64 => (n as i64) as $typ as u128,
                    IntTy::I128 => (n as i128) as $typ as u128,
                },
                TyKind::Uint(uint_ty) => match uint_ty {
                    UintTy::Usize => (n as usize) as $typ as u128,
                    UintTy::U8 => (n as u8) as $typ as u128,
                    UintTy::U16 => (n as u16) as $typ as u128,
                    UintTy::U32 => (n as u32) as $typ as u128,
                    UintTy::U64 => (n as u64) as $typ as u128,
                    UintTy::U128 => n as $typ as u128,
                },
                _ => panic!(),
            }
        }
    };
}

create_cast_fn!(to_i8, i8);
create_cast_fn!(to_i16, i16);
create_cast_fn!(to_i32, i32);
create_cast_fn!(to_i64, i64);
create_cast_fn!(to_i128, i128);
create_cast_fn!(to_isize, isize);
create_cast_fn!(to_u8, u8);
create_cast_fn!(to_u16, u16);
create_cast_fn!(to_u32, u32);
create_cast_fn!(to_u64, u64);
create_cast_fn!(to_u128, u128);
create_cast_fn!(to_usize, usize);

fn neg(n: u128, ty: Ty<'_>) -> u128 {
    match ty.kind() {
        TyKind::Int(int_ty) => match int_ty {
            IntTy::Isize => -(n as isize) as u128,
            IntTy::I8 => -(n as i8) as u128,
            IntTy::I16 => -(n as i16) as u128,
            IntTy::I32 => -(n as i32) as u128,
            IntTy::I64 => -(n as i64) as u128,
            IntTy::I128 => -(n as i128) as u128,
        },
        _ => panic!(),
    }
}
