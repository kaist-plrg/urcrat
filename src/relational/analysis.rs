use std::{
    collections::{BTreeMap, HashMap, HashSet},
    path::Path,
};

use rustc_abi::VariantIdx;
use rustc_data_structures::graph::WithSuccessors;
use rustc_hir::{def_id::DefId, ItemKind};
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::{
        interpret::ConstValue, visit::Visitor, BasicBlock, Body, ConstantKind, Local, Location,
        Operand, Place, Rvalue, Terminator, TerminatorKind,
    },
    ty::{AdtKind, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_mir_dataflow::Analysis;
use rustc_session::config::Input;
use rustc_span::def_id::LocalDefId;

use super::*;
use crate::*;

pub fn analyze_path(path: &Path) -> AnalysisResults {
    analyze_input(compile_util::path_to_input(path))
}

pub fn analyze_str(code: &str) -> AnalysisResults {
    analyze_input(compile_util::str_to_input(code))
}

fn analyze_input(input: Input) -> AnalysisResults {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, analyze).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>) -> AnalysisResults {
    let hir = tcx.hir();
    let may_aliases = steensgaard::analyze(tcx);
    let alias_graph = may_aliases.get_alias_graph();

    let func_ids: Vec<_> = hir
        .items()
        .filter_map(|item_id| {
            let item = hir.item(item_id);
            if item.ident.name.as_str() == "main" || !matches!(item.kind, ItemKind::Fn(_, _, _)) {
                return None;
            }
            Some(item_id.owner_id.def_id)
        })
        .collect();

    let (indirect_assigns, call_graph): (HashMap<_, _>, HashMap<_, _>) = func_ids
        .iter()
        .map(|def_id| {
            let body = tcx.optimized_mir(def_id.to_def_id());
            let (indirect_assigns, callees) = visit_body(*def_id, body, &alias_graph, tcx);
            ((*def_id, indirect_assigns), (*def_id, callees))
        })
        .unzip();
    let mut reachability = graph::transitive_closure(&call_graph);
    for (caller, callees) in &mut reachability {
        callees.insert(*caller);
    }

    let mut functions = HashMap::new();
    for local_def_id in func_ids.iter().copied() {
        let def_id = local_def_id.to_def_id();
        let body = tcx.optimized_mir(def_id);

        println!("{:?}", def_id);
        // for bbd in body.basic_blocks.iter() {
        //     for stmt in &bbd.statements {
        //         println!("{:?}", stmt);
        //     }
        //     if !matches!(
        //         bbd.terminator().kind,
        //         TerminatorKind::Return | TerminatorKind::Assert { .. }
        //     ) {
        //         println!("{:?}", bbd.terminator().kind);
        //     }
        // }

        let pre_rpo_map = get_rpo_map(body);
        let loop_blocks = get_loop_blocks(body, &pre_rpo_map);
        let rpo_map = compute_rpo_map(body, &loop_blocks);
        let dead_locals = get_dead_locals(body, tcx);
        let local_tys = body
            .local_decls
            .iter()
            .map(|decl| TyStructure::from_ty(decl.ty, def_id, tcx))
            .collect();
        let local_ptr_tys = body
            .local_decls
            .iter_enumerated()
            .filter_map(|(local, decl)| {
                let (TyKind::RawPtr(TypeAndMut { ty, .. }) | TyKind::Ref(_, ty, _)) =
                    decl.ty.kind()
                else {
                    return None;
                };
                Some((local, TyStructure::from_ty(*ty, def_id, tcx)))
            })
            .collect();
        let analyzer = Analyzer {
            tcx,
            body,
            rpo_map,
            dead_locals,
            local_tys,
            local_ptr_tys,
            local_def_id,
            indirect_assigns: &indirect_assigns,
            reachability: &reachability,
            alias_graph: &alias_graph,
        };
        functions.insert(def_id, analyzer.analyze());
    }

    AnalysisResults { functions }
}

#[derive(Debug, Clone)]
pub struct AnalysisResults {
    pub functions: HashMap<DefId, HashMap<Location, AbsMem>>,
}

#[allow(missing_debug_implementations)]
pub struct Analyzer<'tcx, 'a> {
    pub tcx: TyCtxt<'tcx>,
    body: &'tcx Body<'tcx>,
    rpo_map: HashMap<BasicBlock, usize>,
    dead_locals: Vec<BitSet<Local>>,
    local_tys: Vec<TyStructure>,
    local_ptr_tys: HashMap<Local, TyStructure>,
    local_def_id: LocalDefId,
    indirect_assigns: &'a HashMap<LocalDefId, HashSet<Local>>,
    reachability: &'a HashMap<LocalDefId, HashSet<LocalDefId>>,
    alias_graph: &'a steensgaard::AliasGraph,
}

impl<'tcx> Analyzer<'tcx, '_> {
    fn analyze(&self) -> HashMap<Location, AbsMem> {
        let bot = AbsMem::bot();

        let mut work_list = WorkList::new(&self.rpo_map);
        work_list.push(Location::START);

        let mut states: HashMap<Location, AbsMem> = HashMap::new();
        states.insert(Location::START, AbsMem::top());

        while let Some(location) = work_list.pop() {
            let state = states.get(&location).unwrap_or(&bot);
            let mut next_state = state.clone();
            let bbd = &self.body.basic_blocks[location.block];
            let nexts = if let Some(stmt) = bbd.statements.get(location.statement_index) {
                self.transfer_stmt(stmt, &mut next_state);
                vec![(location.successor_within_block(), next_state)]
            } else {
                self.transfer_term(bbd.terminator(), &next_state)
            };
            for (next_location, new_next_state) in nexts {
                let next_state = states.get(&next_location).unwrap_or(&bot);
                let joined = next_state.join(&new_next_state);
                if next_location.statement_index == 0 {
                    let _dead_locals = &self.dead_locals[next_location.block.as_usize()];
                    // joined.clear_dead_locals(dead_locals);
                }
                if !joined.ord(next_state) {
                    states.insert(next_location, joined);
                    work_list.push(next_location);
                }
            }
        }

        states
    }

    pub fn get_path_suffixes(&self, path: &AccPath, deref: bool) -> Vec<Vec<AccElem>> {
        let ty = if deref {
            &self.local_ptr_tys[&path.local]
        } else {
            &self.local_tys[path.local.index()]
        };
        let mut suffixes = get_path_suffixes(ty, &path.projection);
        for suffix in &mut suffixes {
            suffix.reverse();
        }
        suffixes
    }

    pub fn ty(&self, operand: &Operand<'tcx>) -> Ty<'tcx> {
        operand.ty(&self.body.local_decls, self.tcx)
    }

    pub fn resolve_indirect_calls(&self, local: Local) -> HashSet<LocalDefId> {
        self.alias_graph
            .find_fn_may_aliases(self.local_def_id, local, self.tcx)
    }

    pub fn locals_invalidated_by_call(&self, callee: LocalDefId) -> HashSet<(Local, usize)> {
        self.reachability[&callee]
            .iter()
            .flat_map(|func| {
                self.indirect_assigns[func].iter().flat_map(|local| {
                    self.alias_graph
                        .find_may_aliases(*func, *local)
                        .into_iter()
                        .filter_map(|alias| {
                            if alias.function == self.local_def_id {
                                Some((alias.local, alias.depth))
                            } else {
                                None
                            }
                        })
                })
            })
            .collect()
    }

    pub fn find_may_aliases(&self, local: Local) -> HashSet<(Local, usize)> {
        self.alias_graph
            .find_may_aliases(self.local_def_id, local)
            .into_iter()
            .filter_map(|alias| {
                if alias.function == self.local_def_id {
                    Some((alias.local, alias.depth))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }
}

#[derive(Debug)]
struct WorkList<'a> {
    rpo_map: &'a HashMap<BasicBlock, usize>,
    locations: BTreeMap<(usize, usize), Location>,
}

impl<'a> WorkList<'a> {
    fn new(rpo_map: &'a HashMap<BasicBlock, usize>) -> Self {
        Self {
            rpo_map,
            locations: BTreeMap::new(),
        }
    }

    fn pop(&mut self) -> Option<Location> {
        let (_, loc) = self.locations.pop_first()?;
        Some(loc)
    }

    fn push(&mut self, location: Location) {
        let block_idx = self.rpo_map[&location.block];
        self.locations
            .insert((block_idx, location.statement_index), location);
    }
}

#[derive(Debug, Clone)]
pub enum TyStructure {
    Adt(Vec<TyStructure>),
    Array(Box<TyStructure>, usize),
    Leaf,
}

impl TyStructure {
    fn from_ty<'tcx>(ty: Ty<'tcx>, def_id: DefId, tcx: TyCtxt<'tcx>) -> Self {
        match ty.kind() {
            TyKind::Adt(adt_def, generic_args) => {
                if adt_def.adt_kind() == AdtKind::Enum {
                    Self::Adt(vec![Self::Leaf])
                } else {
                    let variant = &adt_def.variants()[VariantIdx::from_usize(0)];
                    let tys = variant
                        .fields
                        .iter()
                        .map(|field| Self::from_ty(field.ty(tcx, generic_args), def_id, tcx))
                        .collect();
                    Self::Adt(tys)
                }
            }
            TyKind::Array(ty, len) => {
                let len = len
                    .eval(tcx, tcx.param_env(def_id))
                    .try_to_scalar_int()
                    .unwrap()
                    .try_to_u64()
                    .unwrap() as usize;
                Self::Array(Box::new(Self::from_ty(*ty, def_id, tcx)), len)
            }
            _ => Self::Leaf,
        }
    }
}

fn get_path_suffixes(ty: &TyStructure, proj: &[AccElem]) -> Vec<Vec<AccElem>> {
    match ty {
        TyStructure::Adt(tys) => {
            if let Some(elem) = proj.get(0) {
                let AccElem::Int(n) = elem else { unreachable!() };
                get_path_suffixes(&tys[*n], &proj[1..])
            } else {
                tys.iter()
                    .enumerate()
                    .flat_map(|(i, ty)| {
                        let mut suffixes = get_path_suffixes(ty, &[]);
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
                get_path_suffixes(ty, &proj[1..])
            } else {
                (0..*len)
                    .flat_map(|i| {
                        let mut suffixes = get_path_suffixes(ty, &[]);
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

fn get_rpo_map(body: &Body<'_>) -> HashMap<BasicBlock, usize> {
    body.basic_blocks
        .reverse_postorder()
        .iter()
        .enumerate()
        .map(|(i, bb)| (*bb, i))
        .collect()
}

fn get_loop_blocks(
    body: &Body<'_>,
    rpo_map: &HashMap<BasicBlock, usize>,
) -> HashMap<BasicBlock, HashSet<BasicBlock>> {
    let dominators = body.basic_blocks.dominators();
    let loop_heads: HashSet<_> = body
        .basic_blocks
        .indices()
        .flat_map(|bb| {
            let mut doms: Vec<_> = dominators.dominators(bb).collect();
            let succs: HashSet<_> = body.basic_blocks.successors(bb).collect();
            doms.retain(|dom| succs.contains(dom));
            doms
        })
        .collect();
    let mut loop_heads: Vec<_> = loop_heads.into_iter().collect();
    loop_heads.sort_by_key(|bb| rpo_map[bb]);

    let succ_map: HashMap<_, HashSet<_>> = body
        .basic_blocks
        .indices()
        .map(|bb| (bb, body.basic_blocks.successors(bb).collect()))
        .collect();
    let mut inv_map = graph::inverse(&succ_map);
    loop_heads
        .into_iter()
        .map(|head| {
            let reachables = graph::reachable_vertices(&inv_map, head, inv_map.len());
            for succs in inv_map.values_mut() {
                succs.remove(&head);
            }
            let loop_blocks = body
                .basic_blocks
                .indices()
                .filter(|bb| dominators.dominates(head, *bb) && reachables.contains(bb))
                .collect();
            (head, loop_blocks)
        })
        .collect()
}

fn compute_rpo_map(
    body: &Body<'_>,
    loop_blocks: &HashMap<BasicBlock, HashSet<BasicBlock>>,
) -> HashMap<BasicBlock, usize> {
    fn traverse(
        current: BasicBlock,
        visited: &mut HashSet<BasicBlock>,
        po: &mut Vec<BasicBlock>,
        body: &Body<'_>,
        loop_blocks: &HashMap<BasicBlock, HashSet<BasicBlock>>,
    ) {
        if visited.contains(&current) {
            return;
        }
        visited.insert(current);
        let loops: Vec<_> = loop_blocks
            .values()
            .filter(|blocks| blocks.contains(&current))
            .collect();
        let mut succs: Vec<_> = body.basic_blocks.successors(current).collect();
        succs.sort_by_key(|succ| loops.iter().filter(|blocks| blocks.contains(succ)).count());
        for succ in succs {
            traverse(succ, visited, po, body, loop_blocks);
        }
        po.push(current);
    }
    let mut visited = HashSet::new();
    let mut rpo = vec![];
    traverse(
        BasicBlock::from_usize(0),
        &mut visited,
        &mut rpo,
        body,
        loop_blocks,
    );
    rpo.reverse();
    rpo.into_iter().enumerate().map(|(i, bb)| (bb, i)).collect()
}

fn get_dead_locals<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Vec<BitSet<Local>> {
    let mut borrowed_locals = rustc_mir_dataflow::impls::borrowed_locals(body);
    borrowed_locals.insert(Local::from_usize(0));
    let mut cursor = rustc_mir_dataflow::impls::MaybeLiveLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);
    body.basic_blocks
        .indices()
        .map(|bb| {
            cursor.seek_to_block_start(bb);
            let live_locals = cursor.get();
            let mut borrowed_or_live_locals = borrowed_locals.clone();
            borrowed_or_live_locals.union(live_locals);
            let mut dead_locals = BitSet::new_filled(body.local_decls.len());
            dead_locals.subtract(&borrowed_or_live_locals);
            dead_locals
        })
        .collect()
}

struct BodyVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    current_fn: LocalDefId,
    var_graph: &'a steensgaard::AliasGraph,

    indirect_assigns: HashSet<Local>,
    callees: HashSet<LocalDefId>,
}

impl BodyVisitor<'_, '_> {
    fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }
}

impl<'tcx> Visitor<'tcx> for BodyVisitor<'tcx, '_> {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        if place.is_indirect_first_projection() {
            self.indirect_assigns.insert(place.local);
        }
        self.super_assign(place, rvalue, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call {
            func, destination, ..
        } = &terminator.kind
        {
            assert!(destination.projection.is_empty());
            match func {
                Operand::Copy(f) | Operand::Move(f) => {
                    assert!(f.projection.is_empty());
                    let callees =
                        self.var_graph
                            .find_fn_may_aliases(self.current_fn, f.local, self.tcx);
                    self.callees.extend(callees);
                }
                Operand::Constant(box constant) => {
                    if let ConstantKind::Val(value, ty) = constant.literal {
                        assert_eq!(value, ConstValue::ZeroSized);
                        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                        if self.tcx.impl_of_method(*def_id).is_none() {
                            let name = self.def_id_to_string(*def_id);
                            if let Some(def_id) = def_id.as_local() {
                                if !name.contains("{extern#") {
                                    self.callees.insert(def_id);
                                }
                            }
                        }
                    }
                }
            }
        }
        self.super_terminator(terminator, location);
    }
}

fn visit_body<'tcx>(
    current_fn: LocalDefId,
    body: &Body<'tcx>,
    alias_graph: &steensgaard::AliasGraph,
    tcx: TyCtxt<'tcx>,
) -> (HashSet<Local>, HashSet<LocalDefId>) {
    let mut visitor = BodyVisitor {
        tcx,
        current_fn,
        var_graph: alias_graph,
        indirect_assigns: HashSet::new(),
        callees: HashSet::new(),
    };
    visitor.visit_body(body);
    (visitor.indirect_assigns, visitor.callees)
}
