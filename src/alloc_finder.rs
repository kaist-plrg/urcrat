use std::{
    collections::{HashMap, HashSet},
    path::Path,
};

use etrace::some_or;
use rustc_hir::{def_id::LocalDefId, ItemKind};
use rustc_middle::{
    mir::{
        ConstantKind, Local, Operand, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{IntTy, TyCtxt, TyKind, TypeAndMut, UintTy},
};
use rustc_session::config::Input;

use crate::*;

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
    let hir = tcx.hir();

    for item_id in hir.items() {
        let item = hir.item(item_id);
        if !matches!(item.kind, ItemKind::Fn(_, _, _)) {
            continue;
        }
        let local_def_id = item_id.owner_id.def_id;
        let sig = tcx.fn_sig(local_def_id).skip_binder();
        let output = sig.output().skip_binder();
        let TyKind::RawPtr(TypeAndMut { ty, .. }) = output.kind() else { continue };
        if !ty.is_c_void(tcx) {
            continue;
        }
        let body = tcx.optimized_mir(local_def_id);
        let mut analyzer = Analyzer {
            tcx,
            assigns: HashMap::new(),
            address_takens: HashSet::new(),
        };
        for bbd in body.basic_blocks.iter() {
            for stmt in &bbd.statements {
                analyzer.transfer_stmt(stmt);
            }
            analyzer.transfer_term(bbd.terminator());
        }

        println!("{:?}", local_def_id);
        println!("{:?}", analyzer.assigns);
        println!("{:?}", analyzer.address_takens);
    }

    assert_eq!(hir.items().count(), 1);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Value {
    Local(Local),
    Zero,
    IntraCall(LocalDefId),
    CCall,
}

struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    assigns: HashMap<Local, HashSet<Value>>,
    address_takens: HashSet<Local>,
}

impl<'tcx> Analyzer<'tcx> {
    fn transfer_stmt(&mut self, stmt: &Statement<'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        if !l.projection.is_empty() {
            return;
        }
        match r {
            Rvalue::Use(r) | Rvalue::Cast(_, r, _) => {
                if let Some(r) = self.transfer_op(r) {
                    self.assigns.entry(l.local).or_default().insert(r);
                }
            }
            Rvalue::Ref(_, _, r) => {
                self.address_takens.insert(r.local);
            }
            _ => {}
        }
    }

    fn transfer_op(&self, op: &Operand<'tcx>) -> Option<Value> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    Some(Value::Local(place.local))
                } else {
                    None
                }
            }
            Operand::Constant(box constant) => {
                let ConstantKind::Val(val, ty) = constant.literal else { return None };
                let v = val.try_to_scalar_int()?;
                let is_zero = match ty.kind() {
                    TyKind::Int(IntTy::I8) => v.try_to_i8().ok()? == 0,
                    TyKind::Int(IntTy::I16) => v.try_to_i16().ok()? == 0,
                    TyKind::Int(IntTy::I32) => v.try_to_i32().ok()? == 0,
                    TyKind::Int(IntTy::I64) => v.try_to_i64().ok()? == 0,
                    TyKind::Int(IntTy::I128) => v.try_to_i128().ok()? == 0,
                    TyKind::Int(IntTy::Isize) => v.try_to_i128().ok()? == 0,
                    TyKind::Uint(UintTy::U8) => v.try_to_u8().ok()? == 0,
                    TyKind::Uint(UintTy::U16) => v.try_to_u16().ok()? == 0,
                    TyKind::Uint(UintTy::U32) => v.try_to_u32().ok()? == 0,
                    TyKind::Uint(UintTy::U64) => v.try_to_u64().ok()? == 0,
                    TyKind::Uint(UintTy::U128) => v.try_to_u128().ok()? == 0,
                    TyKind::Uint(UintTy::Usize) => v.try_to_u128().ok()? == 0,
                    _ => return None,
                };
                if is_zero {
                    Some(Value::Zero)
                } else {
                    None
                }
            }
        }
    }

    fn transfer_term(&mut self, term: &Terminator<'tcx>) {
        let TerminatorKind::Call {
            func, destination, ..
        } = &term.kind
        else {
            return;
        };
        if !destination.projection.is_empty() {
            return;
        }
        let constant = some_or!(func.constant(), return);
        let ConstantKind::Val(_, ty) = constant.literal else { unreachable!() };
        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
        let local_def_id = some_or!(def_id.as_local(), return);
        let name: Vec<_> = self
            .tcx
            .def_path(*def_id)
            .data
            .into_iter()
            .map(|data| data.to_string())
            .collect();
        let is_extern = name.iter().any(|s| s.starts_with("{extern#"));
        if is_extern {
            let name = name.last().unwrap();
            if name == "malloc" || name == "calloc" || name == "realloc" {
                self.assigns
                    .entry(destination.local)
                    .or_default()
                    .insert(Value::CCall);
            }
        } else {
            self.assigns
                .entry(destination.local)
                .or_default()
                .insert(Value::IntraCall(local_def_id));
        }
    }
}
