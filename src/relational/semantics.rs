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

impl<'tcx> Analyzer<'tcx> {
    pub fn transfer_stmt(&self, stmt: &Statement<'tcx>, state: &mut AbsMem) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        let (l, l_deref) = AccPath::from_place(*l, state);
        let suffixes = self.get_path_suffixes(&l);
        match r {
            Rvalue::Use(r) => {
                let r = self.transfer_op(r, state);
                state.gm().assign_with_suffixes(&l, l_deref, &r, &suffixes);
            }
            Rvalue::Cast(kind, r, ty) => match kind {
                CastKind::IntToInt => {
                    assert!(suffixes.is_empty());
                    let r = self.transfer_op(r, state);
                    if let OpVal::Int(v) = r {
                        let v = match ty.kind() {
                            TyKind::Int(int_ty) => match int_ty {
                                IntTy::Isize => v.cast_to_i64(),
                                IntTy::I8 => v.cast_to_i8(),
                                IntTy::I16 => v.cast_to_i16(),
                                IntTy::I32 => v.cast_to_i32(),
                                IntTy::I64 => v.cast_to_i64(),
                                IntTy::I128 => v.cast_to_i128(),
                            },
                            TyKind::Uint(uint_ty) => match uint_ty {
                                UintTy::Usize => v.cast_to_u64(),
                                UintTy::U8 => v.cast_to_u8(),
                                UintTy::U16 => v.cast_to_u16(),
                                UintTy::U32 => v.cast_to_u32(),
                                UintTy::U64 => v.cast_to_u64(),
                                UintTy::U128 => v.cast_to_u128(),
                            },
                            _ => unreachable!(),
                        };
                        state.gm().assign(&l, l_deref, &OpVal::Int(v));
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
                    state.gm().assign_with_suffixes(&l, l_deref, &r, &suffixes);
                }
            }
            Rvalue::Ref(_, _, r) => {
                assert!(suffixes.is_empty());
                assert!(!l_deref);
                let (path, is_deref) = AccPath::from_place(*r, state);
                if is_deref {
                    state.gm().x_eq_ref_deref_y(&l, &path);
                } else {
                    state.gm().x_eq_ref_y(&l, &path);
                }
            }
            Rvalue::ThreadLocalRef(_) => {
                assert!(suffixes.is_empty());
                state.gm().assign(&l, l_deref, &OpVal::Other);
            }
            Rvalue::AddressOf(_, r) => {
                assert!(suffixes.is_empty());
                assert_eq!(r.projection.len(), 1);
                let (path, is_deref) = AccPath::from_place(*r, state);
                assert!(is_deref);
                let v = OpVal::Place(path, false);
                state.gm().assign(&l, l_deref, &v);
            }
            Rvalue::Len(_) => unreachable!(),
            Rvalue::BinaryOp(op, box (r1, r2)) => {
                assert!(suffixes.is_empty());
                let r1 = self.transfer_op(r1, state);
                let r2 = self.transfer_op(r2, state);
                if let (OpVal::Int(v1), OpVal::Int(v2)) = (r1, r2) {
                    let v = match op {
                        BinOp::Add => v1.add(v2),
                        BinOp::Sub => v1.sub(v2),
                        BinOp::Mul => v1.mul(v2),
                        BinOp::Div => v1.div(v2),
                        BinOp::Rem => v1.rem(v2),
                        BinOp::BitXor => v1.bit_xor(v2),
                        BinOp::BitAnd => v1.bit_and(v2),
                        BinOp::BitOr => v1.bit_or(v2),
                        BinOp::Shl => v1.shl(v2),
                        BinOp::Shr => v1.shr(v2),
                        BinOp::Eq => v1.eq(v2),
                        BinOp::Lt => v1.lt(v2),
                        BinOp::Le => v1.le(v2),
                        BinOp::Ne => v1.ne(v2),
                        BinOp::Ge => v1.ge(v2),
                        BinOp::Gt => v1.gt(v2),
                        _ => unreachable!(),
                    };
                    state.gm().assign(&l, l_deref, &OpVal::Int(v));
                } else {
                    state.gm().assign(&l, l_deref, &OpVal::Other);
                }
            }
            Rvalue::CheckedBinaryOp(_, _) => unreachable!(),
            Rvalue::UnaryOp(op, r) => {
                assert!(suffixes.is_empty());
                let r = self.transfer_op(r, state);
                if let OpVal::Int(v) = r {
                    let v = match op {
                        UnOp::Not => v.not(),
                        UnOp::Neg => v.neg(),
                    };
                    state.gm().assign(&l, l_deref, &OpVal::Int(v));
                } else {
                    state.gm().assign(&l, l_deref, &OpVal::Other);
                }
            }
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::Discriminant(_) => {
                assert!(suffixes.is_empty());
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
                    state.gm().assign_with_suffixes(&l, l_deref, &v, &suffixes);
                } else {
                    for (field, op) in rs.iter_enumerated() {
                        let v = self.transfer_op(op, state);
                        let l = l.extended(&[AccElem::Int(field.index())]);
                        state.gm().assign_with_suffixes(&l, l_deref, &v, &suffixes);
                    }
                }
            }
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                assert!(suffixes.is_empty());
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
                                    IntTy::I128 => i.try_to_i128().unwrap(),
                                };
                                OpVal::Int(Int::Signed(v))
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
                                OpVal::Int(Int::Unsigned(v))
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
            TerminatorKind::SwitchInt { discr, targets } => {
                let ty = self.ty(discr);
                match self.transfer_op(discr, state) {
                    OpVal::Place(discr, is_deref) => targets
                        .iter()
                        .map(|(v, target)| {
                            let location = Location {
                                block: target,
                                statement_index: 0,
                            };
                            let v = Int::from_u128(v, ty);
                            let mut state = state.clone();
                            if is_deref {
                                state.gm().filter_deref_x_int(&discr, v);
                            } else {
                                state.gm().filter_x_int(&discr, v);
                            }
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
                        let target_opt = targets.iter().find(|(v, _)| i == Int::from_u128(*v, ty));
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
                }
            }
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

    fn get_path_suffixes(&self, path: &AccPath) -> Vec<Vec<AccElem>> {
        let ty = &self.local_tys[path.local.index()];
        let mut suffixes = get_path_suffixes(ty, &path.projection);
        for suffix in &mut suffixes {
            suffix.reverse();
        }
        suffixes
    }
}

fn get_path_suffixes(ty: &TyStructure, proj: &[AccElem]) -> Vec<Vec<AccElem>> {
    match ty {
        TyStructure::Adt(tys) => {
            if let Some(elem) = proj.get(0) {
                let AccElem::Int(n) = elem else { unreachable!() };
                let mut suffixes = get_path_suffixes(&tys[*n], &proj[1..]);
                for suffix in &mut suffixes {
                    suffix.push(AccElem::Int(*n));
                }
                suffixes
            } else {
                tys.iter()
                    .enumerate()
                    .flat_map(|(i, ty)| {
                        let mut suffixes = get_path_suffixes(ty, &proj[1..]);
                        for suffix in &mut suffixes {
                            suffix.push(AccElem::Int(i));
                        }
                        suffixes
                    })
                    .collect()
            }
        }
        TyStructure::Array(box ty, len) => {
            if let Some(elem) = proj.get(0) {
                if let AccElem::Int(n) = elem {
                    assert!(n < len);
                }
                let mut suffixes = get_path_suffixes(ty, &proj[1..]);
                for suffix in &mut suffixes {
                    suffix.push(elem.clone());
                }
                suffixes
            } else {
                (0..*len)
                    .flat_map(|i| {
                        let mut suffixes = get_path_suffixes(ty, &proj[1..]);
                        for suffix in &mut suffixes {
                            suffix.push(AccElem::Int(i));
                        }
                        suffixes
                    })
                    .collect()
            }
        }
        TyStructure::Leaf => {
            assert!(proj.is_empty());
            vec![vec![]]
        }
    }
}

#[derive(Debug, Clone)]
pub enum OpVal {
    Place(AccPath, bool),
    Int(Int),
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
    fn new(local: Local, projection: Vec<AccElem>) -> Self {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccElem {
    Int(usize),
    Symbolic(HashSet<Local>),
}

impl AccElem {
    fn from_elem(proj: PlaceElem<'_>, state: &AbsMem) -> Option<Self> {
        match proj {
            ProjectionElem::Deref => None,
            ProjectionElem::Field(i, _) => Some(AccElem::Int(i.index())),
            ProjectionElem::Index(local) => {
                let path = AccPath::new(local, vec![]);
                if let Some(i) = state.g().get_x_as_int(&path) {
                    Some(AccElem::Int(i.as_usize()))
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

macro_rules! create_cast_method {
    ($method_name:ident, $sign:ident, $typ:ty) => {
        fn $method_name(self) -> Self {
            #[allow(trivial_numeric_casts)]
            match self {
                Int::Signed(v) => Int::$sign(v as $typ as _),
                Int::Unsigned(v) => Int::$sign(v as $typ as _),
                Int::Bool(v) => Int::$sign(v as $typ as _),
            }
        }
    };
}

macro_rules! create_arith_method {
    ($method_name:ident, $op:tt) => {
        fn $method_name(self, other: Self) -> Self {
            match (self, other) {
                (Int::Signed(v1), Int::Signed(v2)) => Int::Signed(v1 $op v2),
                (Int::Unsigned(v1), Int::Unsigned(v2)) => Int::Unsigned(v1 $op v2),
                _ => unreachable!(),
            }
        }
    }
}

macro_rules! create_logic_method {
    ($method_name:ident, $op:tt) => {
        fn $method_name(self, other: Self) -> Self {
            match (self, other) {
                (Int::Signed(v1), Int::Signed(v2)) => Int::Signed(v1 $op v2),
                (Int::Unsigned(v1), Int::Unsigned(v2)) => Int::Unsigned(v1 $op v2),
                (Int::Bool(v1), Int::Bool(v2)) => Int::Bool(v1 $op v2),
                _ => unreachable!(),
            }
        }
    }
}

macro_rules! create_shift_method {
    ($method_name:ident, $op:tt) => {
        fn $method_name(self, other: Self) -> Self {
            match (self, other) {
                (Int::Signed(v1), Int::Signed(v2)) => Int::Signed(v1 $op v2),
                (Int::Signed(v1), Int::Unsigned(v2)) => Int::Signed(v1 $op v2),
                (Int::Unsigned(v1), Int::Signed(v2)) => Int::Unsigned(v1 $op v2),
                (Int::Unsigned(v1), Int::Unsigned(v2)) => Int::Unsigned(v1 $op v2),
                _ => unreachable!(),
            }
        }
    }
}

macro_rules! create_cmp_method {
    ($method_name:ident, $op:tt) => {
        fn $method_name(self, other: Self) -> Self {
            match (self, other) {
                (Int::Signed(v1), Int::Signed(v2)) => Int::Bool(v1 $op v2),
                (Int::Unsigned(v1), Int::Unsigned(v2)) => Int::Bool(v1 $op v2),
                (Int::Bool(v1), Int::Bool(v2)) => Int::Bool(v1 $op v2),
                _ => unreachable!(),
            }
        }
    }
}

impl Int {
    create_cast_method!(cast_to_i8, Signed, i8);

    create_cast_method!(cast_to_i16, Signed, i16);

    create_cast_method!(cast_to_i32, Signed, i32);

    create_cast_method!(cast_to_i64, Signed, i64);

    create_cast_method!(cast_to_i128, Signed, i128);

    create_cast_method!(cast_to_u8, Unsigned, u8);

    create_cast_method!(cast_to_u16, Unsigned, u16);

    create_cast_method!(cast_to_u32, Unsigned, u32);

    create_cast_method!(cast_to_u64, Unsigned, u64);

    create_cast_method!(cast_to_u128, Unsigned, u128);

    create_arith_method!(add, +);

    create_arith_method!(sub, -);

    create_arith_method!(mul, *);

    create_arith_method!(div, /);

    create_arith_method!(rem, %);

    create_logic_method!(bit_xor, ^);

    create_logic_method!(bit_and, &);

    create_logic_method!(bit_or, |);

    create_shift_method!(shl, <<);

    create_shift_method!(shr, >>);

    create_cmp_method!(eq, ==);

    create_cmp_method!(lt, <);

    create_cmp_method!(le, <=);

    create_cmp_method!(ne, !=);

    create_cmp_method!(ge, >);

    create_cmp_method!(gt, >=);

    fn not(self) -> Self {
        match self {
            Int::Signed(v) => Int::Signed(!v),
            Int::Unsigned(v) => Int::Unsigned(!v),
            Int::Bool(v) => Int::Bool(!v),
        }
    }

    fn neg(self) -> Self {
        let Int::Signed(v) = self else { unreachable!() };
        Int::Signed(-v)
    }

    fn from_u128(v: u128, ty: Ty<'_>) -> Self {
        match ty.kind() {
            TyKind::Int(int_ty) => {
                let v = match int_ty {
                    IntTy::Isize => v as isize as i128,
                    IntTy::I8 => v as i8 as i128,
                    IntTy::I16 => v as i16 as i128,
                    IntTy::I32 => v as i32 as i128,
                    IntTy::I64 => v as i64 as i128,
                    IntTy::I128 => v as i128,
                };
                Int::Signed(v)
            }
            TyKind::Uint(uint_ty) => {
                let v = match uint_ty {
                    UintTy::Usize => v as usize as u128,
                    UintTy::U8 => v as u8 as u128,
                    UintTy::U16 => v as u16 as u128,
                    UintTy::U32 => v as u32 as u128,
                    UintTy::U64 => v as u64 as u128,
                    UintTy::U128 => v,
                };
                Int::Unsigned(v)
            }
            TyKind::Bool => Int::Bool(v != 0),
            _ => unreachable!(),
        }
    }
}
