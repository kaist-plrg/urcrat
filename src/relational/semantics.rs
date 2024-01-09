use rustc_middle::{
    mir::{
        interpret::{ConstValue, GlobalAlloc, Scalar},
        CastKind, ConstantKind, Location, Operand, ProjectionElem, Rvalue, Statement,
        StatementKind, Terminator,
    },
    ty::TyKind,
};

use super::*;
use crate::*;

impl<'tcx> Analyzer<'tcx> {
    pub fn transfer_stmt(&self, stmt: &Statement<'tcx>, state: &mut AbsMem) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        l.projection.iter().filter(|proj| match proj {
            ProjectionElem::Deref => todo!(),
            ProjectionElem::Field(_, _) => todo!(),
            ProjectionElem::Index(_) => todo!(),
            ProjectionElem::ConstantIndex { .. } => todo!(),
            ProjectionElem::Subslice { .. } => todo!(),
            ProjectionElem::Downcast(_, _) => todo!(),
            ProjectionElem::OpaqueCast(_) => todo!(),
        });
        match r {
            Rvalue::Use(r) => {
                todo!()
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

    fn transfer_operand(&self, l_id: usize, l_deref: bool, r: &Operand<'_>, state: &mut AbsRelMem) {
        match r {
            Operand::Copy(r) | Operand::Move(r) => {
                let r_deref = r.is_indirect_first_projection();
                let r_id = r.local.as_usize();
                // match (l_deref, r_deref) {
                //     (false, false) => self.x_eq_y(l_id, r_id),
                //     (false, true) => self.x_eq_deref_y(l_id, r_id),
                //     (true, false) => self.deref_x_eq_y(l_id, r_id),
                //     (true, true) => self.deref_x_eq_deref_y(l_id, r_id),
                // }
            }
            Operand::Constant(box constant) => match constant.literal {
                ConstantKind::Ty(_) => unreachable!(),
                ConstantKind::Unevaluated(_, _) => {}
                ConstantKind::Val(value, ty) => match value {
                    ConstValue::Scalar(scalar) => match scalar {
                        Scalar::Int(_) => {}
                        Scalar::Ptr(ptr, _) => match self.tcx.global_alloc(ptr.provenance) {
                            GlobalAlloc::Static(def_id) => {
                                todo!()
                            }
                            GlobalAlloc::Memory(_) => {
                                todo!()
                            }
                            _ => unreachable!(),
                        },
                    },
                    ConstValue::ZeroSized => {
                        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                        todo!()
                    }
                    ConstValue::Slice { .. } => unreachable!(),
                    ConstValue::ByRef { .. } => unreachable!(),
                },
            },
        }
    }

    pub fn transfer_term(&self, term: &Terminator<'tcx>) -> Vec<(Location, AbsMem)> {
        todo!()
    }

    fn x_eq_y(&self, x: usize, y: usize, state: &mut AbsRelMem) {}

    fn deref_x_eq_y(&self, x: usize, y: usize, state: &mut AbsRelMem) {}
}
