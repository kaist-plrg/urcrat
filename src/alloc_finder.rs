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
    ty::{TyCtxt, TyKind, TypeAndMut},
};
use rustc_session::config::Input;

use crate::*;

pub fn analyze_path(path: &Path) -> HashSet<LocalDefId> {
    analyze_input(compile_util::path_to_input(path))
}

pub fn analyze_str(code: &str) -> HashSet<LocalDefId> {
    analyze_input(compile_util::str_to_input(code))
}

fn analyze_input(input: Input) -> HashSet<LocalDefId> {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, analyze).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>) -> HashSet<LocalDefId> {
    let hir = tcx.hir();

    let mut call_graph = HashMap::new();
    let mut assigns = HashMap::new();
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
        let mut analyzer = Analyzer::new(tcx);
        for bbd in body.basic_blocks.iter() {
            for stmt in &bbd.statements {
                analyzer.transfer_stmt(stmt);
            }
            analyzer.transfer_term(bbd.terminator());
        }
        analyzer.remove_address_takens();
        assigns.insert(local_def_id, analyzer.assigns);
        call_graph.insert(local_def_id, analyzer.calls);
    }
    let fns: HashSet<_> = call_graph.keys().copied().collect();
    for callees in call_graph.values_mut() {
        callees.retain(|callee| fns.contains(callee));
    }
    let (call_graph_sccs, scc_elems) = graph::compute_sccs(&call_graph);
    let inv_call_graph_sccs = graph::inverse(&call_graph_sccs);
    let po = graph::post_order(&call_graph_sccs, &inv_call_graph_sccs);
    let mut alloc_fns = HashSet::new();
    for f in po.iter().flatten().flat_map(|scc| &scc_elems[scc]) {
        let assigns = &assigns[f];
        if is_alloc(Local::from_u32(0), assigns, &alloc_fns) {
            alloc_fns.insert(*f);
        }
    }
    alloc_fns
}

fn is_alloc(
    local: Local,
    assigns: &HashMap<Local, HashSet<Value>>,
    alloc_fns: &HashSet<LocalDefId>,
) -> bool {
    let vs = some_or!(assigns.get(&local), return false);
    for v in vs {
        let b = match v {
            Value::Local(l) => is_alloc(*l, assigns, alloc_fns),
            Value::IntraCall(def_id) => alloc_fns.contains(def_id),
            Value::CCall => true,
        };
        if b {
            return true;
        }
    }
    false
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Value {
    Local(Local),
    IntraCall(LocalDefId),
    CCall,
}

struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    assigns: HashMap<Local, HashSet<Value>>,
    address_takens: HashSet<Local>,
    calls: HashSet<LocalDefId>,
}

impl<'tcx> Analyzer<'tcx> {
    #[inline]
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            assigns: HashMap::new(),
            address_takens: HashSet::new(),
            calls: HashSet::new(),
        }
    }

    #[inline]
    fn remove_address_takens(&mut self) {
        self.assigns
            .retain(|local, _| !self.address_takens.contains(local));
    }

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
        let place = op.place()?;
        if place.projection.is_empty() {
            Some(Value::Local(place.local))
        } else {
            None
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
            self.calls.insert(local_def_id);
        }
    }
}
