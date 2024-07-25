// from rustc_mir_build/src/check_unsafety.rs

use std::{
    collections::{HashMap, HashSet},
    path::Path,
};

use rustc_hir::{HirId, Unsafety};
use rustc_middle::{
    thir::{visit, visit::Visitor, Expr, ExprKind, LintLevel, Pat, PatKind, Thir},
    ty,
    ty::TyCtxt,
};
use rustc_session::config::Input;
use rustc_span::def_id::{DefId, LocalDefId};

use crate::{compile_util, graph};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum UnsafeOpKind {
    CallToUnsafeFunction(Option<DefId>),
    UseOfInlineAssembly,
    UseOfMutableStatic,
    UseOfExternStatic,
    DerefOfRawPointer,
    AccessToUnionField(DefId),
}

use UnsafeOpKind::*;

pub fn analyze_path(path: &Path, unions: Option<HashSet<String>>) {
    analyze_input(compile_util::path_to_input(path), unions)
}

pub fn analyze_str(code: &str, unions: Option<HashSet<String>>) {
    analyze_input(compile_util::str_to_input(code), unions)
}

fn analyze_input(input: Input, unions: Option<HashSet<String>>) {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| analyze(tcx, unions)).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>, unions: Option<HashSet<String>>) {
    let hir = tcx.hir();
    let mut fns = HashMap::new();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if matches!(item.kind, rustc_hir::ItemKind::Fn(..)) {
            let def_id = item_id.owner_id.def_id;
            let kinds = check_unsafety(tcx, def_id);
            fns.insert(def_id, kinds);
        }
    }
    let fn_def_ids: HashSet<_> = fns.keys().copied().collect();
    let mut call_graph: HashMap<LocalDefId, HashSet<LocalDefId>> = HashMap::new();
    for def_id in &fn_def_ids {
        call_graph.insert(*def_id, HashSet::new());
    }
    for (f, kinds) in &mut fns {
        let ks: Vec<_> = kinds.iter().copied().collect();
        kinds.clear();
        for kind in ks {
            if let CallToUnsafeFunction(Some(def_id)) = kind {
                if let Some(def_id) = def_id.as_local() {
                    if fn_def_ids.contains(&def_id) {
                        call_graph.get_mut(f).unwrap().insert(def_id);
                        continue;
                    }
                }
            }
            kinds.insert(kind);
        }
    }

    let is_union_unsafe: HashMap<_, _> = fns
        .iter()
        .map(|(f, kinds)| {
            let b = kinds.iter().any(|k| {
                let AccessToUnionField(def_id) = k else { return false };
                let Some(ref unions) = unions else { return true };
                let s = tcx.def_path_str(*def_id);
                unions.contains(&s)
            });
            (*f, b)
        })
        .collect();

    let transitive = graph::transitive_closure(&call_graph);
    let mut unsafes = 0;
    let mut unions = 0;
    for (f, kinds) in &fns {
        if !kinds.is_empty() || transitive[f].iter().any(|c| !fns[c].is_empty()) {
            unsafes += 1;
            if is_union_unsafe[f] || transitive[f].iter().any(|c| is_union_unsafe[c]) {
                unions += 1;
            }
        }
    }
    println!(
        "{} {} {} {}",
        fns.len(),
        unsafes,
        unions,
        unions as f32 / unsafes as f32
    );
}

struct UnsafetyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    hir_context: HirId,
    assignment: bool,
    in_union: Option<DefId>,
    kinds: HashSet<UnsafeOpKind>,
}

impl UnsafetyVisitor<'_, '_> {
    fn requires_unsafe(&mut self, kind: UnsafeOpKind) {
        self.kinds.insert(kind);
    }
}

impl<'a, 'tcx> Visitor<'a, 'tcx> for UnsafetyVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_pat(&mut self, pat: &Pat<'tcx>) {
        if let Some(u) = self.in_union {
            match pat.kind {
                PatKind::Binding { .. }
                | PatKind::Constant { .. }
                | PatKind::Variant { .. }
                | PatKind::Leaf { .. }
                | PatKind::Deref { .. }
                | PatKind::Range { .. }
                | PatKind::Slice { .. }
                | PatKind::Array { .. } => self.requires_unsafe(AccessToUnionField(u)),
                PatKind::Wild | PatKind::Or { .. } | PatKind::AscribeUserType { .. } => {}
            }
        };

        match &pat.kind {
            PatKind::Leaf { .. } => {
                if let ty::Adt(adt_def, ..) = pat.ty.kind() {
                    if adt_def.is_union() {
                        let old_in_union =
                            std::mem::replace(&mut self.in_union, Some(adt_def.did()));
                        visit::walk_pat(self, pat);
                        self.in_union = old_in_union;
                    } else {
                        visit::walk_pat(self, pat);
                    }
                } else {
                    visit::walk_pat(self, pat);
                }
            }
            _ => visit::walk_pat(self, pat),
        }
    }

    fn visit_expr(&mut self, expr: &Expr<'tcx>) {
        match expr.kind {
            ExprKind::Field { .. }
            | ExprKind::VarRef { .. }
            | ExprKind::UpvarRef { .. }
            | ExprKind::Scope { .. }
            | ExprKind::Cast { .. } => {}
            ExprKind::AddressOf { .. }
            | ExprKind::Adt { .. }
            | ExprKind::Array { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Block { .. }
            | ExprKind::Borrow { .. }
            | ExprKind::Literal { .. }
            | ExprKind::NamedConst { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::ZstLiteral { .. }
            | ExprKind::ConstParam { .. }
            | ExprKind::ConstBlock { .. }
            | ExprKind::Deref { .. }
            | ExprKind::Index { .. }
            | ExprKind::NeverToAny { .. }
            | ExprKind::PlaceTypeAscription { .. }
            | ExprKind::ValueTypeAscription { .. }
            | ExprKind::PointerCoercion { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::StaticRef { .. }
            | ExprKind::ThreadLocalRef { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Call { .. }
            | ExprKind::Assign { .. }
            | ExprKind::AssignOp { .. }
            | ExprKind::Break { .. }
            | ExprKind::Closure { .. }
            | ExprKind::Continue { .. }
            | ExprKind::Return { .. }
            | ExprKind::Become { .. }
            | ExprKind::Yield { .. }
            | ExprKind::Loop { .. }
            | ExprKind::Let { .. }
            | ExprKind::Match { .. }
            | ExprKind::Box { .. }
            | ExprKind::If { .. }
            | ExprKind::InlineAsm { .. }
            | ExprKind::OffsetOf { .. }
            | ExprKind::LogicalOp { .. }
            | ExprKind::Use { .. } => {
                self.assignment = false;
            }
        };
        match expr.kind {
            ExprKind::Scope {
                value,
                lint_level: LintLevel::Explicit(hir_id),
                region_scope: _,
            } => {
                let prev_id = self.hir_context;
                self.hir_context = hir_id;
                self.visit_expr(&self.thir[value]);
                self.hir_context = prev_id;
                return;
            }
            ExprKind::Call {
                fun,
                ty: _,
                args: _,
                from_hir_call: _,
                fn_span: _,
            } => {
                if self.thir[fun].ty.fn_sig(self.tcx).unsafety() == Unsafety::Unsafe {
                    let func_id = if let ty::FnDef(func_id, _) = self.thir[fun].ty.kind() {
                        Some(*func_id)
                    } else {
                        None
                    };
                    self.requires_unsafe(CallToUnsafeFunction(func_id));
                }
            }
            ExprKind::Deref { arg } => {
                if let ExprKind::StaticRef { def_id, .. } = self.thir[arg].kind {
                    if self.tcx.is_mutable_static(def_id) {
                        self.requires_unsafe(UseOfMutableStatic);
                    } else if self.tcx.is_foreign_item(def_id) {
                        self.requires_unsafe(UseOfExternStatic);
                    }
                } else if self.thir[arg].ty.is_unsafe_ptr() {
                    self.requires_unsafe(DerefOfRawPointer);
                }
            }
            ExprKind::InlineAsm { .. } => self.requires_unsafe(UseOfInlineAssembly),
            ExprKind::Field { lhs, .. } => {
                let lhs = &self.thir[lhs];
                if let ty::Adt(adt_def, _) = lhs.ty.kind() {
                    if adt_def.is_union() && !self.assignment {
                        self.requires_unsafe(AccessToUnionField(adt_def.did()));
                    }
                }
            }
            ExprKind::Assign { lhs, rhs } | ExprKind::AssignOp { lhs, rhs, .. } => {
                let lhs = &self.thir[lhs];
                if matches!(expr.kind, ExprKind::Assign { .. }) {
                    self.assignment = true;
                    visit::walk_expr(self, lhs);
                    self.assignment = false;
                    visit::walk_expr(self, &self.thir()[rhs]);
                    return;
                }
            }
            ExprKind::Let { expr: expr_id, .. } => {
                let let_expr = &self.thir[expr_id];
                if let ty::Adt(adt_def, _) = let_expr.ty.kind() {
                    if adt_def.is_union() {
                        self.requires_unsafe(AccessToUnionField(adt_def.did()));
                    }
                }
            }
            _ => {}
        }
        visit::walk_expr(self, expr);
    }
}

fn check_unsafety(tcx: TyCtxt<'_>, def: LocalDefId) -> HashSet<UnsafeOpKind> {
    let Ok((thir, expr)) = tcx.thir_body(def) else { panic!() };
    let thir = &thir.borrow();
    assert!(!thir.exprs.is_empty());

    let hir_id = tcx.hir().local_def_id_to_hir_id(def);
    let mut visitor = UnsafetyVisitor {
        tcx,
        thir,
        hir_context: hir_id,
        assignment: false,
        in_union: None,
        kinds: HashSet::new(),
    };
    visitor.visit_expr(&thir[expr]);
    visitor.kinds
}
