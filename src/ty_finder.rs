use std::collections::{HashMap, HashSet};

use etrace::some_or;
use rustc_hir::{def::Res, intravisit, intravisit::Visitor, ItemKind, Node, QPath, Ty, TyKind};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;

use crate::graph;

pub struct TyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    tys: Vec<LocalDefId>,
    ty_ids: HashMap<LocalDefId, usize>,
    foreign_types: HashSet<usize>,
    type_graph: HashMap<usize, HashSet<usize>>,
}

impl std::fmt::Debug for TyVisitor<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TyVisitor")
            .field("tys", &self.tys)
            .field("ty_ids", &self.ty_ids)
            .field("foreign_types", &self.foreign_types)
            .field("type_graph", &self.type_graph)
            .finish()
    }
}

impl<'tcx> TyVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            tys: Vec::new(),
            ty_ids: HashMap::new(),
            foreign_types: HashSet::new(),
            type_graph: HashMap::new(),
        }
    }

    pub fn find_foreign_tys(mut self, tcx: TyCtxt<'tcx>) -> HashSet<LocalDefId> {
        tcx.hir().visit_all_item_likes_in_crate(&mut self);
        self.foreign_types
            .into_iter()
            .flat_map(|id| graph::reachable_vertices(&self.type_graph, id, self.tys.len()))
            .map(|id| self.tys[id])
            .collect()
    }

    fn ty_to_id(&mut self, ty: LocalDefId) -> usize {
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
        let def_id = some_or!(def_id.as_local(), return);
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
                        let item_id = self.ty_to_id(item.owner_id.def_id);
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
