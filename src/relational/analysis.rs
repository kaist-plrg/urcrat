use std::{
    collections::{BTreeMap, HashMap, HashSet},
    path::Path,
};

use rustc_abi::VariantIdx;
use rustc_data_structures::graph::WithSuccessors;
use rustc_hir::{def_id::DefId, ItemKind};
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location, Operand},
    ty::{AdtKind, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_mir_dataflow::Analysis;
use rustc_session::config::Input;

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

    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.name.as_str() == "main" {
            continue;
        }
        if !matches!(item.kind, ItemKind::Fn(_, _, _)) {
            continue;
        }

        let def_id = item.owner_id.def_id.to_def_id();
        let body = tcx.optimized_mir(def_id);

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
            def_id,
            rpo_map,
            dead_locals,
            local_tys,
            local_ptr_tys,
        };
        analyzer.analyze();

        for bbd in body.basic_blocks.iter() {
            for stmt in &bbd.statements {
                println!("{:?}", stmt);
            }
        }
    }

    AnalysisResults
}

#[derive(Debug, Clone, Copy)]
pub struct AnalysisResults;

#[allow(missing_debug_implementations)]
pub struct Analyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub body: &'tcx Body<'tcx>,
    pub def_id: DefId,
    pub rpo_map: HashMap<BasicBlock, usize>,
    pub dead_locals: Vec<BitSet<Local>>,
    pub local_tys: Vec<TyStructure>,
    pub local_ptr_tys: HashMap<Local, TyStructure>,
}

impl<'tcx> Analyzer<'tcx> {
    fn analyze(&self) {
        let bot = AbsMem::bot();

        let mut work_list = WorkList::new(&self.rpo_map);
        work_list.push(Location::START);

        let states: HashMap<Location, AbsMem> = HashMap::new();

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
                    work_list.push(next_location);
                }
            }
        }
    }

    pub fn ty(&self, operand: &Operand<'tcx>) -> Ty<'tcx> {
        operand.ty(&self.body.local_decls, self.tcx)
    }

    // fn def_id_to_string(&self, def_id: DefId) -> String {
    //     self.tcx.def_path(def_id).to_string_no_crate_verbose()
    // }
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
                    let def_id = adt_def.did();
                    let name = tcx.def_path(def_id).to_string_no_crate_verbose();
                    assert!(name.contains("::Option") && def_id.is_local(), "{name}");
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
