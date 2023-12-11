use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};

use etrace::some_or;
use rustc_hir::{
    def::Res, intravisit, intravisit::Visitor, Expr, ExprKind, ItemKind, Node, QPath, Ty, TyKind,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{TyCtxt, TypeckResults},
};
use rustc_span::def_id::DefId;

use crate::{compile_util, graph};

pub fn analyze(path: &Path) {
    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| {
        let mut visitor = TyVisitor::new(tcx);
        tcx.hir().visit_all_item_likes_in_crate(&mut visitor);
        let foreign_tys: BTreeSet<_> = visitor
            .foreign_types
            .into_iter()
            .flat_map(|id| graph::reachable_vertices(&visitor.type_graph, id, visitor.tys.len()))
            .map(|id| visitor.tys[id])
            .collect();

        for item_id in tcx.hir().items() {
            let item = tcx.hir().item(item_id);
            if !matches!(
                item.kind,
                ItemKind::Static(_, _, _) | ItemKind::Const(_, _, _) | ItemKind::Fn(_, _, _)
            ) {
                continue;
            }
            let typeck = tcx.typeck(item.owner_id);
            let mut visitor = UnionVisitor::new(tcx, typeck, &foreign_tys);
            visitor.visit_item(item);
            if !visitor.map.is_empty() {
                let def_path = tcx.def_path_str(item.owner_id.to_def_id());
                println!("{:?} {:?}", def_path, visitor.map);
            }
        }
    })
    .unwrap();
}

struct TyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    tys: Vec<DefId>,
    ty_ids: BTreeMap<DefId, usize>,
    foreign_types: BTreeSet<usize>,
    type_graph: BTreeMap<usize, BTreeSet<usize>>,
}

impl<'tcx> TyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            tys: Vec::new(),
            ty_ids: BTreeMap::new(),
            foreign_types: BTreeSet::new(),
            type_graph: BTreeMap::new(),
        }
    }

    fn ty_to_id(&mut self, ty: DefId) -> usize {
        self.ty_ids.get(&ty).copied().unwrap_or_else(|| {
            let id = self.tys.len();
            self.tys.push(ty);
            self.ty_ids.insert(ty, id);
            id
        })
    }

    fn handle_ty(&mut self, ty: &'tcx Ty<'tcx>) {
        let TyKind::Path(QPath::Resolved(_, path)) = ty.kind else { return };
        let Res::Def(_, def_id) = path.res else { return };
        if !def_id.is_local() {
            return;
        }
        let id = self.ty_to_id(def_id);

        let hir = self.tcx.hir();
        let mut hir_id = ty.hir_id;
        while let Some(parent_id) = hir.opt_parent_id(hir_id) {
            let node = hir.get(parent_id);
            match node {
                Node::ForeignItem(_) => {
                    self.foreign_types.insert(id);
                    break;
                }
                Node::Item(item) => {
                    if matches!(
                        item.kind,
                        ItemKind::Struct(_, _) | ItemKind::Union(_, _) | ItemKind::TyAlias(_, _)
                    ) {
                        let item_def_id = item.owner_id.to_def_id();
                        let item_id = self.ty_to_id(item_def_id);
                        self.type_graph.entry(item_id).or_default().insert(id);
                    }
                    break;
                }
                _ => hir_id = parent_id,
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for TyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_ty(&mut self, ty: &'tcx Ty<'tcx>) {
        self.handle_ty(ty);
        intravisit::walk_ty(self, ty);
    }
}

struct UnionVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    foreign_tys: &'a BTreeSet<DefId>,
    map: BTreeMap<String, BTreeSet<String>>,
}

impl<'tcx, 'a> UnionVisitor<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        typeck: &'a TypeckResults<'tcx>,
        foreign_tys: &'a BTreeSet<DefId>,
    ) -> Self {
        Self {
            tcx,
            typeck,
            foreign_tys,
            map: BTreeMap::new(),
        }
    }

    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let ExprKind::Field(expr, ident) = expr.kind else { return };
        let ty = self.typeck.expr_ty(expr);
        let adt_def = some_or!(ty.ty_adt_def(), return);
        if !adt_def.is_union() {
            return;
        }
        let def_id = adt_def.did();
        if !def_id.is_local() {
            return;
        }
        if self.foreign_tys.contains(&def_id) {
            return;
        }
        let ty = format!("{:?}", ty);
        let field = ident.name.to_string();
        self.map.entry(ty).or_default().insert(field);
    }
}

impl<'tcx> Visitor<'tcx> for UnionVisitor<'tcx, '_> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }
}
