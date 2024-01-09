use rustc_middle::{
    mir::{
        interpret::{ConstValue, Scalar},
        CastKind, ConstantKind, Location, Operand, Place, PlaceElem, ProjectionElem, Rvalue,
        Statement, StatementKind, Terminator,
    },
    ty::{IntTy, TyKind, UintTy},
};

use super::*;
use crate::*;

impl<'tcx> Analyzer<'tcx> {
    pub fn transfer_stmt(&self, stmt: &Statement<'tcx>, state: &mut AbsMem) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        let (l, l_deref) = AccPath::from_place(*l, state);
        match r {
            Rvalue::Use(r) => {
                let r = self.transfer_op(r, state);
                let graph = state.graph_mut();
                match r {
                    OpVal::Place(r, r_deref) => match (l_deref, r_deref) {
                        (true, true) => panic!(),
                        (true, false) => graph.deref_x_eq_y(&l, &r),
                        (false, true) => graph.x_eq_deref_y(&l, &r),
                        (false, false) => graph.x_eq_y(&l, &r),
                    },
                    OpVal::Int(n) => {
                        if l_deref {
                            graph.deref_x_eq_int(&l, n);
                        } else {
                            graph.x_eq_int(&l, n);
                        }
                    }
                    OpVal::Other => {
                        if l_deref {
                            graph.deref_x_eq(&l);
                        } else {
                            graph.x_eq(&l);
                        }
                    }
                }
            }
            Rvalue::Cast(kind, r, _) => match kind {
                CastKind::PointerExposeAddress => todo!(),
                CastKind::PointerFromExposedAddress => todo!(),
                CastKind::PointerCoercion(_) => todo!(),
                CastKind::DynStar => todo!(),
                CastKind::IntToInt => todo!(),
                CastKind::FloatToInt => todo!(),
                CastKind::FloatToFloat => todo!(),
                CastKind::IntToFloat => todo!(),
                CastKind::PtrToPtr => todo!(),
                CastKind::FnPtrToPtr => todo!(),
                CastKind::Transmute => todo!(),
            },
            Rvalue::Repeat(r, _) => {
                todo!()
            }
            Rvalue::Ref(_, _, r) => {
                todo!()
            }
            Rvalue::ThreadLocalRef(def_id) => {
                todo!()
            }
            Rvalue::AddressOf(_, r) => {
                todo!()
            }
            Rvalue::Len(_) => unreachable!(),
            Rvalue::BinaryOp(op, box (r1, r2)) | Rvalue::CheckedBinaryOp(op, box (r1, r2)) => {
                todo!()
            }
            Rvalue::UnaryOp(_, r) => {
                todo!()
            }
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::Discriminant(_) => {
                todo!()
            }
            Rvalue::Aggregate(box _, rs) => {
                todo!()
            }
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                todo!()
            }
        }
    }

    fn transfer_op(&self, op: &Operand<'_>, state: &mut AbsMem) -> OpVal {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let (path, is_deref) = AccPath::from_place(*place, state);
                OpVal::Place(path, is_deref)
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

    pub fn transfer_term(&self, term: &Terminator<'tcx>) -> Vec<(Location, AbsMem)> {
        todo!()
    }
}

enum OpVal {
    Place(AccPath, bool),
    Int(Int),
    Other,
}

impl AccPath {
    fn from_place(place: Place<'_>, state: &mut AbsMem) -> (Self, bool) {
        let root = place.local;
        let projections = place
            .projection
            .iter()
            .filter_map(|e| AccProj::from_elem(e, state))
            .collect();
        let is_deref = place.is_indirect_first_projection();
        (AccPath::new(root, projections), is_deref)
    }
}

impl AccProj {
    fn from_elem(proj: PlaceElem<'_>, state: &mut AbsMem) -> Option<Self> {
        match proj {
            ProjectionElem::Deref => None,
            ProjectionElem::Field(i, _) => Some(AccProj::Int(i.index())),
            ProjectionElem::Index(local) => {
                let path = AccPath::new(local, vec![]);
                if let Some(i) = state.graph_mut().get_int_value(&path) {
                    Some(AccProj::Int(i.as_usize()))
                } else {
                    // TODO: aliasing
                    Some(AccProj::Symbolic([local].into_iter().collect()))
                }
            }
            ProjectionElem::ConstantIndex { .. } => unreachable!(),
            ProjectionElem::Subslice { .. } => unreachable!(),
            ProjectionElem::Downcast(_, _) => unreachable!(),
            ProjectionElem::OpaqueCast(_) => unreachable!(),
        }
    }
}
