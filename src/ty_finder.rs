use std::collections::{HashMap, HashSet};

use etrace::some_or;
use rustc_hir::{
    def::Res,
    intravisit::{self, Visitor},
    AmbigArg, ItemKind, Node, QPath, Ty, TyKind,
};
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

    pub fn find_foreign_tys(
        mut self,
        tcx: TyCtxt<'tcx>,
    ) -> (HashSet<LocalDefId>, HashSet<LocalDefId>) {
        tcx.hir_visit_all_item_likes_in_crate(&mut self);
        let ftypes: HashSet<_> = self
            .foreign_types
            .into_iter()
            .flat_map(|id| graph::reachable_vertices(&self.type_graph, id, self.tys.len()))
            .collect();
        let mut local_types = HashSet::new();
        let mut foreign_types = HashSet::new();
        for (i, ty) in self.tys.iter().enumerate() {
            if ftypes.contains(&i) {
                foreign_types.insert(*ty);
            } else {
                local_types.insert(*ty);
            }
        }
        (local_types, foreign_types)
    }

    fn ty_to_id(&mut self, ty: LocalDefId) -> usize {
        self.ty_ids.get(&ty).copied().unwrap_or_else(|| {
            let id = self.tys.len();
            self.tys.push(ty);
            self.ty_ids.insert(ty, id);
            id
        })
    }

    fn handle_ty<Unambig>(&mut self, ty: &'tcx Ty<'tcx, Unambig>) {
        let TyKind::Path(QPath::Resolved(_, path)) = ty.kind else { return };
        let Res::Def(_, def_id) = path.res else { return };
        let def_id = some_or!(def_id.as_local(), return);
        let id = self.ty_to_id(def_id);

        let hir = self.tcx.hir();
        let hir_id = ty.hir_id;
        for parent_id in hir.parent_id_iter(hir_id) {
            let node = self.tcx.hir_node(parent_id);
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
                _ => {}
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for TyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_ty(&mut self, ty: &'tcx Ty<'tcx, AmbigArg>) {
        self.handle_ty(ty);
        intravisit::walk_ty(self, ty);
    }
}
