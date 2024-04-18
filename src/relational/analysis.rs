use std::{
    collections::{BTreeMap, HashMap, HashSet},
    path::Path,
};

use rustc_abi::VariantIdx;
use rustc_data_structures::graph::WithSuccessors;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::{BitSet, HybridBitSet};
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, Local, Location, Operand, Rvalue, StatementKind, TerminatorKind,
    },
    ty::{AdtKind, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_mir_dataflow::Analysis;
use rustc_session::config::Input;
use rustc_span::def_id::LocalDefId;

use super::*;
use crate::*;

pub fn analyze_path(path: &Path, gc: bool) -> AnalysisResults {
    analyze_input(compile_util::path_to_input(path), gc)
}

pub fn analyze_str(code: &str, gc: bool) -> AnalysisResults {
    analyze_input(compile_util::str_to_input(code), gc)
}

fn analyze_input(input: Input, gc: bool) -> AnalysisResults {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| analyze(tcx, gc)).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>, gc: bool) -> AnalysisResults {
    let may_points_to = points_to::analyze(tcx);
    let functions = may_points_to
        .call_graph
        .keys()
        .map(|def_id| (*def_id, analyze_fn(tcx, &may_points_to, *def_id, gc)))
        .collect();
    AnalysisResults { functions }
}

pub fn analyze_fn(
    tcx: TyCtxt<'_>,
    may_points_to: &points_to::AnalysisResults,
    local_def_id: LocalDefId,
    gc: bool,
) -> HashMap<Location, AbsMem> {
    let def_id = local_def_id.to_def_id();
    let body = tcx.optimized_mir(def_id);
    // println!("{}", compile_util::body_to_str(&body));
    // println!("{}", compile_util::body_size(&body));
    let pre_rpo_map = get_rpo_map(body);
    let loop_blocks = get_loop_blocks(body, &pre_rpo_map);
    let rpo_map = compute_rpo_map(body, &loop_blocks);
    let dead_locals = get_dead_locals(body, tcx);
    let discriminant_values = find_discriminant_values(body);
    let local_tys = body
        .local_decls
        .iter()
        .map(|decl| TyStructure::from_ty(decl.ty, def_id, tcx))
        .collect();
    let local_ptr_tys = body
        .local_decls
        .iter_enumerated()
        .filter_map(|(local, decl)| {
            let (TyKind::RawPtr(TypeAndMut { ty, .. }) | TyKind::Ref(_, ty, _)) = decl.ty.kind()
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
        discriminant_values,
        may_points_to,
        gc,
    };
    analyzer.analyze()
}

#[derive(Debug, Clone)]
pub struct AnalysisResults {
    pub functions: HashMap<LocalDefId, HashMap<Location, AbsMem>>,
}

#[allow(missing_debug_implementations)]
pub struct Analyzer<'tcx, 'a> {
    pub tcx: TyCtxt<'tcx>,
    body: &'tcx Body<'tcx>,
    rpo_map: HashMap<BasicBlock, usize>,
    dead_locals: Vec<BitSet<Local>>,
    local_tys: Vec<TyStructure>,
    local_ptr_tys: HashMap<Local, TyStructure>,
    pub local_def_id: LocalDefId,
    discriminant_values: HashMap<BasicBlock, DiscrVal>,
    pub may_points_to: &'a points_to::AnalysisResults,
    gc: bool,
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
            let nexts = self.body.stmt_at(location).either(
                |stmt| {
                    let mut next_state = state.clone();
                    self.transfer_stmt(stmt, location, &mut next_state);
                    vec![(location.successor_within_block(), next_state)]
                },
                |terminator| {
                    let v = self.discriminant_values.get(&location.block);
                    self.transfer_term(terminator, v, location, state)
                },
            );
            // println!("{:?}", state);
            // println!("{:?} {:?}", location, self.body.stmt_at(location));
            // println!("{:?}", nexts);
            // println!("-----------------");
            for (next_location, new_next_state) in nexts {
                let next_state = states.get(&next_location).unwrap_or(&bot);
                let mut joined = next_state.join(&new_next_state);
                if self.gc && next_location.statement_index == 0 {
                    let dead_locals = &self.dead_locals[next_location.block.as_usize()];
                    joined.clear_dead_locals(dead_locals);
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

    pub fn resolve_indirect_call(&self, loc: Location) -> &[LocalDefId] {
        &self.may_points_to.indirect_calls[&self.local_def_id][&loc.block]
    }

    pub fn get_assign_writes(&self, loc: Location) -> &HybridBitSet<usize> {
        &self.may_points_to.writes[&self.local_def_id][&loc]
    }

    pub fn get_call_writes(&self, callees: &[LocalDefId]) -> Option<HybridBitSet<usize>> {
        let c0 = callees.get(0)?;
        let mut writes = self.may_points_to.call_writes[c0].clone();
        for c in &callees[1..] {
            writes.union(&self.may_points_to.call_writes[c]);
        }
        Some(writes)
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
                Self::Array(Box::new(Self::from_ty(*ty, def_id, tcx)), len.min(10))
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
                get_path_suffixes(&tys[*n as usize], &proj[1..])
            } else {
                tys.iter()
                    .enumerate()
                    .flat_map(|(i, ty)| {
                        let mut suffixes = get_path_suffixes(ty, &[]);
                        for suffix in &mut suffixes {
                            suffix.push(AccElem::Int(i as _));
                        }
                        suffixes
                    })
                    .collect()
            }
        }
        TyStructure::Array(box ty, len) => {
            if let Some(elem) = proj.get(0) {
                if let AccElem::Int(n) = elem {
                    assert!(*n < *len as u128, "{} {}", n, len);
                }
                get_path_suffixes(ty, &proj[1..])
            } else {
                (0..*len)
                    .flat_map(|i| {
                        let mut suffixes = get_path_suffixes(ty, &[]);
                        for suffix in &mut suffixes {
                            suffix.push(AccElem::Int(i as _));
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

#[derive(Debug, Clone, Copy)]
pub struct DiscrVal {
    pub equal: bool,
    pub lhs: Local,
    pub rhs: Local,
}

fn find_discriminant_values(body: &Body<'_>) -> HashMap<BasicBlock, DiscrVal> {
    body.basic_blocks
        .iter_enumerated()
        .filter_map(|(bb, bbd)| {
            let TerminatorKind::SwitchInt { discr, .. } = &bbd.terminator().kind else {
                return None;
            };
            let place = discr.place()?;
            let local = place.as_local()?;
            let v = bbd.statements.iter().rev().find_map(|stmt| {
                let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind else { return None };
                if lhs.as_local()? != local {
                    return None;
                }
                let Rvalue::BinaryOp(op, box (lhs, rhs)) = rhs else { return None };
                let equal = match op {
                    BinOp::Eq => true,
                    BinOp::Ne => false,
                    _ => return None,
                };
                let lhs = lhs.place()?.as_local()?;
                let rhs = rhs.place()?.as_local()?;
                Some(DiscrVal { equal, lhs, rhs })
            })?;
            Some((bb, v))
        })
        .collect()
}
