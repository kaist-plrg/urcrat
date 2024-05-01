use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    path::Path,
};

use etrace::some_or;
use rustc_data_structures::graph::{
    scc::Sccs, DirectedGraph, GraphSuccessors, WithNumNodes, WithSuccessors,
};
use rustc_hir::{def::Res, ItemKind, QPath, TyKind as HirTyKind};
use rustc_index::{
    bit_set::{HybridBitSet, HybridIter},
    Idx, IndexVec,
};
use rustc_middle::{
    mir::{
        interpret::{ConstValue, GlobalAlloc, Scalar},
        visit::Visitor,
        AggregateKind, BasicBlock, BinOp, Body, ConstantKind, Local, LocalDecl, Location, Operand,
        Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
    },
    ty::{Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_session::config::Input;
use rustc_span::def_id::{DefId, LocalDefId};
use ty_shape::*;
use typed_arena::Arena;

use crate::*;

pub fn analyze_path(path: &Path) -> Solutions {
    analyze_input(compile_util::path_to_input(path))
}

pub fn analyze_str(code: &str) -> Solutions {
    analyze_input(compile_util::str_to_input(code))
}

fn analyze_input(input: Input) -> Solutions {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| {
        let arena = Arena::new();
        let tss = get_ty_shapes(&arena, tcx);
        let pre = pre_analyze(&tss, tcx);
        analyze(&pre, &tss, tcx)
    })
    .unwrap()
}

#[derive(Debug)]
pub struct BodyItem<'tcx> {
    local_def_id: LocalDefId,
    body: &'tcx Body<'tcx>,
    is_fn: bool,
}

#[derive(Debug)]
pub struct PreAnalysisData<'tcx> {
    bodies: Vec<BodyItem<'tcx>>,

    pub call_graph: HashMap<LocalDefId, HashSet<LocalDefId>>,
    indirect_calls: HashMap<LocalDefId, HashMap<BasicBlock, usize>>,

    ends: Vec<usize>,
    globals: HashMap<LocalDefId, usize>,
    inv_fns: HashMap<usize, LocalDefId>,
    vars: HashMap<Var, usize>,

    index_prefixes: HashMap<usize, u8>,
    union_offsets: HashMap<usize, Vec<usize>>,
    graph: HashMap<LocNode, LocEdges>,
    var_nodes: HashMap<(LocalDefId, Local), LocNode>,
}

pub type Solutions = Vec<HybridBitSet<usize>>;

#[derive(Debug)]
pub struct AnalysisResults {
    pub ends: Vec<usize>,
    pub union_offsets: HashMap<usize, Vec<usize>>,
    pub graph: LocGraph,
    pub var_nodes: HashMap<(LocalDefId, Local), LocNode>,

    pub solutions: Solutions,

    pub call_graph: HashMap<LocalDefId, HashSet<LocalDefId>>,
    pub indirect_calls: HashMap<LocalDefId, HashMap<BasicBlock, Vec<LocalDefId>>>,

    pub writes: HashMap<LocalDefId, HashMap<Location, HybridBitSet<usize>>>,
    pub bitfield_writes: HashMap<LocalDefId, HashMap<Location, HybridBitSet<usize>>>,
    pub call_writes: HashMap<LocalDefId, HybridBitSet<usize>>,
}

pub fn pre_analyze<'a, 'tcx>(
    tss: &'a TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> PreAnalysisData<'tcx> {
    let hir = tcx.hir();

    let mut bodies = vec![];
    let mut fn_def_ids = HashSet::new();
    let mut visitor = FnPtrVisitor::new(tcx);
    for item_id in hir.items() {
        let item = hir.item(item_id);
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        match item.kind {
            ItemKind::Fn(_, _, _) if item.ident.name.as_str() != "main" => {
                fn_def_ids.insert(local_def_id);
                let body = tcx.optimized_mir(def_id);
                visitor.visit_body(body);
                let body_item = BodyItem {
                    local_def_id,
                    body,
                    is_fn: true,
                };
                bodies.push(body_item);
            }
            ItemKind::Static(_, _, _) => {
                let body = tcx.mir_for_ctfe(def_id);
                visitor.visit_body(body);
                let body_item = BodyItem {
                    local_def_id,
                    body,
                    is_fn: false,
                };
                bodies.push(body_item);
            }
            _ => {}
        }
    }
    let mut call_graph: HashMap<_, _> = fn_def_ids.iter().map(|f| (*f, HashSet::new())).collect();
    let fn_ptrs = visitor.fn_ptrs;

    let mut globals = HashMap::new();
    let mut inv_fns = HashMap::new();
    let mut vars = HashMap::new();
    let mut ends = vec![];
    let mut alloc_ends: Vec<usize> = vec![];
    let mut allocs = vec![];
    let mut graph = HashMap::new();
    let mut union_offsets = HashMap::new();
    let mut index_prefixes = HashMap::new();
    let mut indirect_calls: HashMap<_, HashMap<_, _>> = HashMap::new();
    let mut var_nodes = HashMap::new();
    for item in &bodies {
        let fn_ptr = fn_ptrs.contains(&item.local_def_id);
        let global_index = ends.len();
        globals.insert(item.local_def_id, global_index);

        if item.is_fn {
            inv_fns.insert(global_index, item.local_def_id);
        }

        let mut local_decls = item.body.local_decls.iter_enumerated();
        let ret = local_decls.next().unwrap();
        let mut params = vec![];
        for _ in 0..item.body.arg_count {
            params.push(local_decls.next().unwrap());
        }
        let local_decls = params
            .into_iter()
            .chain(std::iter::once(ret))
            .chain(local_decls);

        for (local, local_decl) in local_decls {
            vars.insert(Var::Local(item.local_def_id, local), ends.len());
            let ty = tss.tys[&local_decl.ty];
            let node = add_edges(
                ty,
                ends.len(),
                &mut graph,
                &mut index_prefixes,
                &mut union_offsets,
            );
            var_nodes.insert((item.local_def_id, local), node);
            compute_ends(ty, &mut ends);

            if fn_ptr && local.index() == 0 {
                ends[global_index] = ends.len() - 1;
            }

            if let Some(ty) = unwrap_ptr(local_decl.ty) {
                let mut ends = vec![];
                let ty = tss.tys[&ty];
                compute_ends(ty, &mut ends);
                for (i, end) in ends.into_iter().enumerate() {
                    if alloc_ends.len() > i {
                        alloc_ends[i] = alloc_ends[i].max(end);
                    } else {
                        alloc_ends.push(end);
                    }
                }
            }
        }

        for (bb, bbd) in item.body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call {
                func, destination, ..
            } = &bbd.terminator().kind
            else {
                continue;
            };
            match func {
                Operand::Copy(func) | Operand::Move(func) => {
                    assert!(func.projection.is_empty());
                    let var = Var::Local(item.local_def_id, func.local);
                    let index = vars[&var];
                    indirect_calls
                        .entry(item.local_def_id)
                        .or_default()
                        .insert(bb, index);
                }
                _ => {
                    let def_id = some_or!(operand_to_fn(func), continue);
                    let ty = destination.ty(&item.body.local_decls, tcx).ty;
                    if ty.is_unsafe_ptr() && is_c_fn(def_id, tcx) {
                        allocs.push(Var::Alloc(item.local_def_id, bb));
                    }
                    if let Some(callee) = def_id.as_local() {
                        if fn_def_ids.contains(&callee) {
                            call_graph
                                .get_mut(&item.local_def_id)
                                .unwrap()
                                .insert(callee);
                        }
                    }
                }
            }
        }
    }

    for alloc in allocs {
        let len = ends.len();
        vars.insert(alloc, len);
        for end in &alloc_ends {
            ends.push(len + *end);
        }
    }

    PreAnalysisData {
        bodies,
        call_graph,
        indirect_calls,
        ends,
        globals,
        inv_fns,
        vars,
        index_prefixes,
        union_offsets,
        graph,
        var_nodes,
    }
}

pub fn analyze<'a, 'tcx>(
    pre: &PreAnalysisData<'tcx>,
    tss: &'a TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Solutions {
    let mut analyzer = Analyzer {
        tcx,
        tss,
        pre,
        graph: Graph::new(pre.ends.len()),
    };
    for item in &pre.bodies {
        // println!("{}", compile_util::body_to_str(body));
        for (block, bbd) in item.body.basic_blocks.iter_enumerated() {
            for stmt in bbd.statements.iter() {
                let ctx = Context::new(&item.body.local_decls, item.local_def_id);
                analyzer.transfer_stmt(stmt, ctx);
            }
            let terminator = bbd.terminator();
            let ctx = Context::new(&item.body.local_decls, item.local_def_id);
            analyzer.transfer_term(terminator, ctx, block);
        }
    }
    analyzer.graph.solve(&pre.ends)
}

pub fn serialize_solutions(solutions: &Solutions) -> Vec<u8> {
    let mut arr = vec![];
    for v in solutions {
        for mut i in v.iter() {
            while i > 0 {
                arr.push((i & 127) as u8);
                i >>= 7;
            }
            arr.push(254);
        }
        arr.push(255);
    }
    arr.pop();
    arr
}

pub fn deserialize_solutions(arr: &[u8]) -> Solutions {
    let size = arr.iter().filter(|n| **n == 255).count() + 1;
    let mut solutions: Solutions = vec![HybridBitSet::new_empty(size)];
    let mut s = &mut solutions[0];
    let mut i = 0;
    let mut len = 0;
    for n in arr {
        match *n {
            255 => {
                solutions.push(HybridBitSet::new_empty(size));
                s = solutions.last_mut().unwrap();
            }
            254 => {
                s.insert(i);
                i = 0;
                len = 0;
            }
            n => {
                i |= (n as usize) << len;
                len += 7;
            }
        }
    }
    solutions
}

pub fn post_analyze<'a, 'tcx>(
    mut pre: PreAnalysisData<'tcx>,
    solutions: Solutions,
    tss: &'a TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> AnalysisResults {
    for (index, sols) in solutions.iter().enumerate() {
        let node = LocNode::new(0, index);
        let mut succs = vec![];
        for succ in sols.iter() {
            let max = pre.index_prefixes.get(&succ).cloned().unwrap_or(0);
            succs.extend((0..=max).map(|p| LocNode::new(p, succ)));
        }
        pre.graph.insert(node, LocEdges::Deref(succs));
    }
    let mut address_taken_indices = HybridBitSet::new_empty(pre.ends.len());
    for indices in &solutions {
        address_taken_indices.union(indices);
    }
    for (i, _) in pre.ends.iter().enumerate() {
        if address_taken_indices.contains(i) {
            for j in (i + 1)..=pre.ends[i] {
                address_taken_indices.insert(j);
            }
        }
    }

    let analyzer = Analyzer {
        tcx,
        pre: &pre,
        tss,
        graph: Graph::new(pre.ends.len()),
    };
    let mut writes: HashMap<_, HashMap<_, _>> = HashMap::new();
    let mut bitfield_writes: HashMap<_, HashMap<_, _>> = HashMap::new();
    for item in &pre.bodies {
        let writes = writes.entry(item.local_def_id).or_default();
        let bitfield_writes = bitfield_writes.entry(item.local_def_id).or_default();
        let ctx = Context::new(&item.body.local_decls, item.local_def_id);
        for (block, bbd) in item.body.basic_blocks.iter_enumerated() {
            for (statement_index, stmt) in bbd.statements.iter().enumerate() {
                let StatementKind::Assign(box (l, _)) = stmt.kind else { continue };
                let location = Location {
                    block,
                    statement_index,
                };
                compute_writes(l, location, &pre.ends, &solutions, ctx, &analyzer, writes);
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &bbd.terminator().kind
            {
                let location = Location {
                    block,
                    statement_index: bbd.statements.len(),
                };
                compute_writes(
                    *destination,
                    location,
                    &pre.ends,
                    &solutions,
                    ctx,
                    &analyzer,
                    writes,
                );
                compute_bitfield_writes(
                    func,
                    args,
                    location,
                    &tss.bitfields,
                    tcx,
                    &pre.ends,
                    &solutions,
                    ctx,
                    &analyzer,
                    bitfield_writes,
                );
            }
        }
    }
    for writes in writes.values_mut() {
        for writes in writes.values_mut() {
            writes.intersect(&address_taken_indices);
        }
    }
    let fn_writes: HashMap<_, _> = writes
        .iter()
        .map(|(f, writes)| {
            let mut ws = HybridBitSet::new_empty(pre.ends.len());
            for w in writes.values() {
                ws.union(w);
            }
            (*f, ws)
        })
        .collect();

    let indirect_calls: HashMap<_, HashMap<_, Vec<_>>> = pre
        .indirect_calls
        .into_iter()
        .map(|(def_id, calls)| {
            let calls = calls
                .into_iter()
                .map(|(bb, index)| {
                    let callees = solutions[index]
                        .iter()
                        .filter_map(|index| pre.inv_fns.get(&index).copied())
                        .collect();
                    (bb, callees)
                })
                .collect();
            (def_id, calls)
        })
        .collect();
    for (caller, calls) in &indirect_calls {
        let callees = pre.call_graph.get_mut(caller).unwrap();
        callees.extend(calls.values().flatten());
    }
    let mut reachability = graph::transitive_closure(&pre.call_graph);
    for (func, reachables) in &mut reachability {
        reachables.insert(*func);
    }
    let call_writes: HashMap<_, _> = reachability
        .iter()
        .map(|(func, reachables)| {
            let mut writes = HybridBitSet::new_empty(pre.ends.len());
            for reachable in reachables {
                writes.union(&fn_writes[reachable]);
            }
            (*func, writes)
        })
        .collect();

    AnalysisResults {
        ends: pre.ends,
        union_offsets: pre.union_offsets,
        graph: pre.graph,
        var_nodes: pre.var_nodes,
        solutions,
        call_graph: pre.call_graph,
        indirect_calls,
        writes,
        bitfield_writes,
        call_writes,
    }
}

fn compute_ends(ty: &TyShape<'_>, ends: &mut Vec<usize>) {
    match ty {
        TyShape::Primitive => ends.push(ends.len()),
        TyShape::Array(t, _) => compute_ends(t, ends),
        TyShape::Struct(len, ts, _) => {
            let end = ends.len();
            for (_, t) in ts {
                compute_ends(t, ends);
            }
            ends[end] = end + *len - 1;
        }
    }
}

#[inline]
fn compute_writes<'tcx>(
    l: Place<'tcx>,
    location: Location,
    ends: &[usize],
    solutions: &[HybridBitSet<usize>],
    ctx: Context<'_, 'tcx>,
    analyzer: &Analyzer<'_, '_, 'tcx>,
    writes: &mut HashMap<Location, HybridBitSet<usize>>,
) {
    let writes = writes
        .entry(location)
        .or_insert(HybridBitSet::new_empty(ends.len()));
    let ty = l.ty(ctx.locals, analyzer.tcx).ty;
    let len = analyzer.tss.tys[&ty].len();
    let l = analyzer.prefixed_loc(l, ctx);
    if l.deref {
        for loc in solutions[l.var.root].iter() {
            let loc = loc + l.var.proj;
            let end = *some_or!(ends.get(loc), continue);
            for i in 0..len {
                if loc + i > end {
                    break;
                }
                writes.insert(loc + i);
            }
        }
    } else {
        let loc = l.var.root + l.var.proj;
        for i in 0..len {
            writes.insert(loc + i);
        }
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
fn compute_bitfield_writes<'tcx>(
    func: &Operand<'tcx>,
    args: &[Operand<'tcx>],
    location: Location,
    bitfields: &HashMap<LocalDefId, HashMap<String, usize>>,
    tcx: TyCtxt<'tcx>,
    ends: &[usize],
    solutions: &[HybridBitSet<usize>],
    ctx: Context<'_, 'tcx>,
    analyzer: &Analyzer<'_, '_, 'tcx>,
    writes: &mut HashMap<Location, HybridBitSet<usize>>,
) {
    if args.len() != 2 {
        return;
    }
    let Operand::Constant(box constant) = func else { return };
    let ConstantKind::Val(_, ty) = constant.literal else { unreachable!() };
    let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
    let local_def_id = some_or!(def_id.as_local(), return);
    let (local_def_id, method) = some_or!(receiver_and_method(local_def_id, tcx), return);
    let field = method.strip_prefix("set_").unwrap();
    let offset = bitfields[&local_def_id][field];
    let lhs = args[0].place().unwrap();
    assert!(lhs.projection.is_empty());
    let l = analyzer.prefixed_loc(lhs, ctx);
    let writes = writes
        .entry(location)
        .or_insert(HybridBitSet::new_empty(ends.len()));
    for loc in solutions[l.var.root].iter() {
        let loc = loc + offset;
        let end = ends[loc];
        if loc <= end {
            writes.insert(loc);
        }
    }
}

pub fn receiver_and_method(
    local_def_id: LocalDefId,
    tcx: TyCtxt<'_>,
) -> Option<(LocalDefId, String)> {
    let hir = tcx.hir();
    let impl_def_id = tcx.impl_of_method(local_def_id.to_def_id())?;
    let impl_item = hir.expect_impl_item(local_def_id);
    let method = impl_item.ident.name.to_ident_string();
    let item = hir.expect_item(impl_def_id.expect_local());
    let ItemKind::Impl(imp) = item.kind else { unreachable!() };
    let HirTyKind::Path(QPath::Resolved(_, path)) = imp.self_ty.kind else { unreachable!() };
    let Res::Def(_, struct_def_id) = path.res else { unreachable!() };
    let local_def_id = struct_def_id.expect_local();
    Some((local_def_id, method))
}

fn add_edges(
    ty: &TyShape<'_>,
    index: usize,
    graph: &mut LocGraph,
    index_prefixes: &mut HashMap<usize, u8>,
    union_offsets: &mut HashMap<usize, Vec<usize>>,
) -> LocNode {
    let node = match ty {
        TyShape::Primitive => return LocNode::new(0, index),
        TyShape::Array(t, _) => {
            let succ = add_edges(t, index, graph, index_prefixes, union_offsets);
            let node = succ.parent();
            graph.insert(node, LocEdges::Index(succ));
            node
        }
        TyShape::Struct(len, ts, is_union) => {
            let succs: Vec<_> = ts
                .iter()
                .map(|(offset, t)| {
                    add_edges(t, index + offset, graph, index_prefixes, union_offsets)
                })
                .collect();
            let node = succs[0].parent();
            graph.insert(node, LocEdges::Fields(succs));
            if *is_union {
                let mut offsets: Vec<usize> = ts.iter().map(|(offset, _)| *offset).collect();
                offsets.push(*len);
                union_offsets.insert(index, offsets);
            }
            node
        }
    };
    index_prefixes.insert(index, node.prefix);
    node
}

pub type LocGraph = HashMap<LocNode, LocEdges>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocNode {
    pub prefix: u8,
    pub index: usize,
}

impl std::fmt::Debug for LocNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.index)?;
        if self.prefix != 0 {
            write!(f, ":{}", self.prefix)?;
        }
        Ok(())
    }
}

impl LocNode {
    fn new(prefix: u8, index: usize) -> Self {
        Self { prefix, index }
    }

    fn parent(self) -> Self {
        Self {
            prefix: self.prefix + 1,
            index: self.index,
        }
    }
}

pub enum LocEdges {
    Fields(Vec<LocNode>),
    Index(LocNode),
    Deref(Vec<LocNode>),
}

impl std::fmt::Debug for LocEdges {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocEdges::Fields(succs) => {
                write!(f, "[")?;
                for (i, succ) in succs.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {:?}", i, succ)?;
                }
                write!(f, "]")
            }
            LocEdges::Index(succ) => write!(f, "[_: {:?}]", succ),
            LocEdges::Deref(succs) => {
                write!(f, "[")?;
                for (i, field) in succs.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "*: {:?}", field)?;
                }
                write!(f, "]")
            }
        }
    }
}

#[derive(Clone, Copy)]
struct Context<'a, 'tcx> {
    locals: &'a IndexVec<Local, LocalDecl<'tcx>>,
    owner: LocalDefId,
}

impl<'a, 'tcx> Context<'a, 'tcx> {
    #[inline]
    fn new(locals: &'a IndexVec<Local, LocalDecl<'tcx>>, owner: LocalDefId) -> Self {
        Self { locals, owner }
    }
}

struct Analyzer<'a, 'b, 'tcx> {
    tcx: TyCtxt<'tcx>,
    pre: &'b PreAnalysisData<'tcx>,
    tss: &'a TyShapes<'a, 'tcx>,
    graph: Graph,
}

impl<'tcx> Analyzer<'_, '_, 'tcx> {
    fn transfer_stmt(&mut self, stmt: &Statement<'tcx>, ctx: Context<'_, 'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        let ty = l.ty(ctx.locals, self.tcx).ty;
        let l = self.prefixed_loc(*l, ctx);
        match r {
            Rvalue::Use(r) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::Repeat(r, _) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    let TyKind::Array(ty, _) = ty.kind() else { unreachable!() };
                    self.transfer_assign(l, r, *ty);
                }
            }
            Rvalue::Ref(_, _, r) => {
                let r = self.prefixed_loc(*r, ctx).with_ref(true);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::ThreadLocalRef(r) => {
                if let Some(r) = self.static_ref(*r) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::AddressOf(_, r) => {
                assert!(r.is_indirect_first_projection());
                let r = self.prefixed_loc(*r, ctx).with_deref(false);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::Len(_) => {}
            Rvalue::Cast(_, r, _) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::BinaryOp(op, box (r1, r2)) => {
                if !matches!(
                    op,
                    BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt
                ) {
                    if let Some(r) = self.transfer_op(r1, ctx) {
                        if !r.deref {
                            self.transfer_assign(l, r, ty);
                        }
                    }
                    if let Some(r) = self.transfer_op(r2, ctx) {
                        self.transfer_assign(l, r, ty);
                    }
                }
            }
            Rvalue::CheckedBinaryOp(op, box (r1, r2)) => {
                if !matches!(
                    op,
                    BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt
                ) {
                    let TyKind::Tuple(ts) = ty.kind() else { unreachable!() };
                    let ty = ts[0];
                    if let Some(r) = self.transfer_op(r1, ctx) {
                        self.transfer_assign(l, r, ty);
                    }
                    if let Some(r) = self.transfer_op(r2, ctx) {
                        self.transfer_assign(l, r, ty);
                    }
                }
            }
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::UnaryOp(op, r) => {
                if matches!(op, UnOp::Neg) {
                    if let Some(r) = self.transfer_op(r, ctx) {
                        self.transfer_assign(l, r, ty);
                    }
                }
            }
            Rvalue::Discriminant(_) => {}
            Rvalue::Aggregate(box kind, fs) => match kind {
                AggregateKind::Array(ty) => {
                    for f in fs.iter() {
                        if let Some(r) = self.transfer_op(f, ctx) {
                            self.transfer_assign(l, r, *ty);
                        }
                    }
                }
                AggregateKind::Adt(_, v_idx, _, _, idx) => {
                    let TyShape::Struct(_, ts, _) = self.tss.tys[&ty] else { unreachable!() };
                    let TyKind::Adt(adt_def, generic_args) = ty.kind() else { unreachable!() };
                    let variant = adt_def.variant(*v_idx);
                    for ((i, d), f) in variant.fields.iter_enumerated().zip(fs) {
                        if let Some(r) = self.transfer_op(f, ctx) {
                            let i = if let Some(idx) = idx { *idx } else { i };
                            let proj = ts[i.index()].0;
                            let ty = d.ty(self.tcx, generic_args);
                            self.transfer_assign(l.add(proj), r, ty);
                        }
                    }
                }
                _ => unreachable!(),
            },
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                let r = self.prefixed_loc(*r, ctx);
                self.transfer_assign(l, r, ty);
            }
        }
    }

    fn transfer_assign(&mut self, l: PrefixedLoc, r: PrefixedLoc, ty: Ty<'tcx>) {
        assert!(!l.r#ref);
        let len = self.tss.tys[&ty].len();
        for i in 0..len {
            let l = l.add(i);
            let r = r.add(i);
            match (l.deref, r.r#ref, r.deref) {
                (true, true, _) => unreachable!(),
                (true, false, true) => unreachable!(),
                (true, false, false) => self.graph.add_deref_eq(l.var.root, l.var.proj, r.index()),
                (false, true, true) => self.graph.add_edge(l.index(), r.var.root, r.var.proj),
                (false, true, false) => self.graph.add_solution(l.index(), r.index()),
                (false, false, true) => self.graph.add_eq_deref(l.index(), r.var.root, r.var.proj),
                (false, false, false) => self.graph.add_edge(l.index(), r.index(), 0),
            }
        }
    }

    fn transfer_op(&mut self, op: &Operand<'tcx>, ctx: Context<'_, 'tcx>) -> Option<PrefixedLoc> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => Some(self.prefixed_loc(*place, ctx)),
            Operand::Constant(box constant) => match constant.literal {
                ConstantKind::Ty(_) => unreachable!(),
                ConstantKind::Unevaluated(_, _) => None,
                ConstantKind::Val(value, ty) => match value {
                    ConstValue::Scalar(scalar) => match scalar {
                        Scalar::Int(_) => None,
                        Scalar::Ptr(ptr, _) => match self.tcx.global_alloc(ptr.provenance) {
                            GlobalAlloc::Static(def_id) => self.static_ref(def_id),
                            GlobalAlloc::Memory(_) => None,
                            _ => unreachable!(),
                        },
                    },
                    ConstValue::ZeroSized => {
                        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                        let var =
                            Loc::new_root(self.pre.globals.get(&def_id.as_local()?).copied()?);
                        Some(PrefixedLoc::new_ref(var))
                    }
                    ConstValue::Slice { .. } => None,
                    _ => unreachable!(),
                },
            },
        }
    }

    fn transfer_term(
        &mut self,
        term: &Terminator<'tcx>,
        ctx: Context<'_, 'tcx>,
        block: BasicBlock,
    ) {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            return;
        };
        assert!(destination.projection.is_empty());

        let arg_locs: Vec<_> = args.iter().map(|arg| self.transfer_op(arg, ctx)).collect();
        let output = destination.ty(ctx.locals, self.tcx).ty;
        let dst = self.prefixed_loc(*destination, ctx);

        match func {
            Operand::Copy(func) | Operand::Move(func) => {
                assert!(func.projection.is_empty());
                let mut func = self.prefixed_loc(*func, ctx).with_deref(true);
                for (arg, arg_loc) in args.iter().zip(arg_locs) {
                    let ty = arg.ty(ctx.locals, self.tcx);
                    if let Some(arg) = arg_loc {
                        self.transfer_assign(func, arg, ty);
                    }
                    func = func.add(self.tss.tys[&ty].len());
                }
                self.transfer_assign(dst, func, output);
            }
            Operand::Constant(box constant) => {
                let ConstantKind::Val(value, ty) = constant.literal else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                let name: Vec<_> = self
                    .tcx
                    .def_path(*def_id)
                    .data
                    .into_iter()
                    .map(|data| data.to_string())
                    .collect();
                let is_extern = name.iter().any(|s| s.starts_with("{extern#"));
                let seg = |i: usize| name.get(i).map(|s| s.as_str()).unwrap_or_default();
                let name = (seg(0), seg(1), seg(2), seg(3));
                if let Some(local_def_id) = def_id.as_local() {
                    if let Some(impl_def_id) = self.tcx.impl_of_method(*def_id) {
                        let span = self.tcx.span_of_impl(impl_def_id).unwrap();
                        let code = self.tcx.sess.source_map().span_to_snippet(span).unwrap();
                        assert_eq!(code, "BitfieldStruct");
                    } else if is_extern {
                        if output.is_unsafe_ptr() {
                            let var = Var::Alloc(ctx.owner, block);
                            let loc = Loc::new_root(self.pre.vars[&var]);
                            self.transfer_assign(dst, PrefixedLoc::new_ref(loc), output);
                        }
                    } else {
                        let mut index = self.pre.globals[&local_def_id];
                        for (arg, arg_loc) in args.iter().zip(arg_locs) {
                            let ty = arg.ty(ctx.locals, self.tcx);
                            if let Some(arg) = arg_loc {
                                let loc = Loc::new_root(index);
                                self.transfer_assign(PrefixedLoc::new(loc), arg, ty);
                            }
                            index += self.tss.tys[&ty].len();
                        }
                        let loc = Loc::new_root(index);
                        self.transfer_assign(dst, PrefixedLoc::new(loc), output);
                    }
                } else {
                    match name {
                        ("option" | "result", _, "unwrap", _)
                        | ("slice", _, "as_ptr" | "as_mut_ptr", _)
                        | ("ptr", _, _, "offset") => {
                            if let Some(arg) = &arg_locs[0] {
                                self.transfer_assign(dst, *arg, output);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fn static_ref(&self, def_id: DefId) -> Option<PrefixedLoc> {
        let var = Var::Local(def_id.as_local()?, Local::new(0));
        let loc = Loc::new_root(self.pre.vars.get(&var).copied()?);
        Some(PrefixedLoc::new_ref(loc))
    }

    fn prefixed_loc(&self, place: Place<'tcx>, ctx: Context<'_, 'tcx>) -> PrefixedLoc {
        let mut index = 0;
        let mut ty = ctx.locals[place.local].ty;
        let deref = place.is_indirect_first_projection();
        if deref {
            ty = unwrap_ptr(ty).unwrap();
        }
        let mut ty = self.tss.tys[&ty];
        for proj in place.projection {
            match proj {
                PlaceElem::Deref => {}
                PlaceElem::Index(_) => {
                    let TyShape::Array(t, _) = ty else { unreachable!() };
                    ty = t;
                }
                PlaceElem::Field(f, _) => {
                    let TyShape::Struct(_, fs, _) = ty else { unreachable!() };
                    let (i, nested_ty) = fs[f.index()];
                    index += i;
                    ty = nested_ty;
                }
                _ => unreachable!(),
            }
        }
        let var = Var::Local(ctx.owner, place.local);
        let loc = Loc::new(self.pre.vars[&var], index);
        PrefixedLoc::new(loc).with_deref(place.is_indirect_first_projection())
    }
}

type WeightedGraph = HashMap<usize, HashMap<usize, HashSet<usize>>>;

struct Graph {
    solutions: Solutions,
    zero_weight_edges: Vec<HybridBitSet<usize>>,
    pos_weight_edges: WeightedGraph,
    deref_eqs: WeightedGraph,
    eq_derefs: WeightedGraph,
}

impl std::fmt::Debug for Graph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "solutions: ")?;
        for (i, sol) in self.solutions.iter().enumerate() {
            write!(f, "{}: {:?}, ", i, sol.iter().collect::<Vec<_>>())?;
        }
        write!(f, "\nzero_weight_edges: ")?;
        for (i, sol) in self.zero_weight_edges.iter().enumerate() {
            write!(f, "{}: {:?}, ", i, sol.iter().collect::<Vec<_>>())?;
        }
        write!(f, "\npos_weight_edges: {:?}", self.pos_weight_edges)?;
        write!(f, "\nderef_eqs: {:?}", self.deref_eqs)?;
        write!(f, "\neq_derefs: {:?}", self.eq_derefs)
    }
}

impl Graph {
    fn new(size: usize) -> Self {
        Self {
            solutions: vec![HybridBitSet::new_empty(size); size],
            zero_weight_edges: vec![HybridBitSet::new_empty(size); size],
            pos_weight_edges: HashMap::new(),
            deref_eqs: HashMap::new(),
            eq_derefs: HashMap::new(),
        }
    }

    fn add_solution(&mut self, v: usize, sol: usize) {
        self.solutions[v.index()].insert(sol);
    }

    fn add_edge(&mut self, l: usize, r: usize, weight: usize) {
        if weight == 0 {
            self.zero_weight_edges[r].insert(l);
        } else {
            self.pos_weight_edges
                .entry(r)
                .or_default()
                .entry(l)
                .or_default()
                .insert(weight);
        }
    }

    fn add_deref_eq(&mut self, v: usize, proj: usize, i: usize) {
        self.deref_eqs
            .entry(v)
            .or_default()
            .entry(i)
            .or_default()
            .insert(proj);
    }

    fn add_eq_deref(&mut self, i: usize, v: usize, proj: usize) {
        self.eq_derefs
            .entry(v)
            .or_default()
            .entry(i)
            .or_default()
            .insert(proj);
    }

    fn solve(self, ends: &[usize]) -> Solutions {
        let Self {
            mut solutions,
            mut zero_weight_edges,
            mut pos_weight_edges,
            mut deref_eqs,
            mut eq_derefs,
        } = self;
        let len = solutions.len();

        let mut deltas = solutions.clone();
        let mut id_to_rep = Vec::from_iter(0..len);

        while deltas.iter().any(|s| !s.is_empty()) {
            let sccs: Sccs<_, usize> = Sccs::new(&VecBitSet(&zero_weight_edges));

            let mut components = vec![HybridBitSet::new_empty(len); sccs.num_sccs()];
            for i in 0..len {
                let scc = sccs.scc(i);
                components[scc.index()].insert(i);
            }

            let mut scc_to_rep = vec![];
            let mut cycles = vec![];
            let mut new_id_to_rep = HashMap::new();
            for component in components.iter() {
                let rep = component.iter().next().unwrap();
                scc_to_rep.push(rep);
                if contains_multiple(component) {
                    cycles.push((rep, component));
                    for id in component.iter() {
                        if id != rep {
                            new_id_to_rep.insert(id, rep);
                        }
                    }
                }
            }

            let mut po = vec![];
            for scc in sccs.all_sccs() {
                po.push(scc_to_rep[scc]);
            }

            if sccs.num_sccs() != len {
                // update id_to_rep
                for rep in &mut id_to_rep {
                    if let Some(new_rep) = new_id_to_rep.get(rep) {
                        *rep = *new_rep;
                    }
                }

                // update deltas
                for (rep, ids) in &cycles {
                    for id in ids.iter() {
                        if *rep != id {
                            let set =
                                std::mem::replace(&mut deltas[id], HybridBitSet::new_empty(len));
                            deltas[*rep].union(&set);
                        }
                    }
                }

                // update solutions
                for (rep, ids) in &cycles {
                    let mut intersection = HybridBitSet::new_empty(len);
                    intersection.insert_all();
                    for id in ids.iter() {
                        intersection.intersect(&solutions[id]);
                        if *rep != id {
                            let set =
                                std::mem::replace(&mut solutions[id], HybridBitSet::new_empty(len));
                            solutions[*rep].union(&set);
                        }
                    }
                    let mut union = solutions[*rep].clone();
                    union.subtract(&intersection);
                    deltas[*rep].union(&union);
                }

                // update zero_weight_edges
                zero_weight_edges = vec![HybridBitSet::new_empty(len); len];
                for (scc, rep) in scc_to_rep.iter().enumerate() {
                    let succs = &mut zero_weight_edges[*rep];
                    for succ in sccs.successors(scc) {
                        succs.insert(scc_to_rep[*succ]);
                    }
                }

                // update pos_weight_edges
                update_weighted_graph(&mut pos_weight_edges, &cycles);
                // update deref_eqs
                update_weighted_graph(&mut deref_eqs, &cycles);
                // update eq_derefs
                update_weighted_graph(&mut eq_derefs, &cycles);
            }

            for v in po.into_iter().rev() {
                if deltas[v].is_empty() {
                    continue;
                }
                let delta = std::mem::replace(&mut deltas[v], HybridBitSet::new_empty(len));

                propagate_deref(
                    v,
                    &deref_eqs,
                    &delta,
                    ends,
                    &id_to_rep,
                    &mut zero_weight_edges,
                    &mut solutions,
                    &mut deltas,
                    true,
                );
                propagate_deref(
                    v,
                    &eq_derefs,
                    &delta,
                    ends,
                    &id_to_rep,
                    &mut zero_weight_edges,
                    &mut solutions,
                    &mut deltas,
                    false,
                );

                for l in zero_weight_edges[v].iter() {
                    if l == v {
                        continue;
                    }
                    for f in delta.iter() {
                        if solutions[l].insert(f) {
                            deltas[l].insert(f);
                        }
                    }
                }

                if let Some(pos_weight_edges) = pos_weight_edges.get(&v) {
                    for (l, projs) in pos_weight_edges {
                        for proj in projs {
                            for i in delta.iter() {
                                let f = i + proj;
                                if f > ends[i] {
                                    continue;
                                }
                                if !solutions[*l].insert(f) {
                                    continue;
                                }
                                deltas[*l].insert(f);
                            }
                        }
                    }
                }
            }
        }

        for (id, rep) in id_to_rep.iter().enumerate() {
            if id != *rep {
                solutions[id] = solutions[*rep].clone();
            }
        }

        solutions
    }
}

fn update_weighted_graph(graph: &mut WeightedGraph, cycles: &[(usize, &HybridBitSet<usize>)]) {
    for (rep, ids) in cycles {
        let mut rep_edges = graph.remove(rep).unwrap_or_default();
        for id in ids.iter() {
            if let Some(edges) = graph.remove(&id) {
                for (l, weights) in edges {
                    match rep_edges.entry(l) {
                        Entry::Occupied(mut entry) => {
                            entry.get_mut().extend(weights);
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(weights);
                        }
                    }
                }
            }
        }
        if !rep_edges.is_empty() {
            graph.insert(*rep, rep_edges);
        }
    }
    for edges in graph.values_mut() {
        for (rep, ids) in cycles {
            let mut rep_weights = edges.remove(rep).unwrap_or_default();
            for id in ids.iter() {
                if let Some(weights) = edges.remove(&id) {
                    rep_weights.extend(weights);
                }
            }
            if !rep_weights.is_empty() {
                edges.insert(*rep, rep_weights);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
#[inline]
fn propagate_deref(
    v: usize,
    derefs: &WeightedGraph,
    delta: &HybridBitSet<usize>,
    ends: &[usize],
    id_to_rep: &[usize],
    zero_weight_edges: &mut [HybridBitSet<usize>],
    solutions: &mut [HybridBitSet<usize>],
    deltas: &mut [HybridBitSet<usize>],
    deref_eq: bool,
) {
    let derefs = some_or!(derefs.get(&v), return);
    for (w, projs) in derefs {
        for proj in projs {
            for i in delta.iter() {
                let f = i + proj;
                if f > ends[i] {
                    continue;
                }
                let f = id_to_rep[f];
                let (l, r) = if deref_eq { (f, *w) } else { (*w, f) };
                if !zero_weight_edges[r].insert(l) {
                    continue;
                }
                let mut diff = solutions[r].clone();
                diff.subtract(&solutions[l]);
                if !diff.is_empty() {
                    solutions[l].union(&diff);
                    deltas[l].union(&diff);
                }
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Var {
    Local(LocalDefId, Local),
    Alloc(LocalDefId, BasicBlock),
}

impl std::fmt::Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::Local(def_id, local) => write!(f, "{:?}::{:?}", def_id, local),
            Var::Alloc(def_id, bb) => write!(f, "{:?}::{:?}", def_id, bb),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Loc {
    root: usize,
    proj: usize,
}

impl std::fmt::Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.root)?;
        if self.proj != 0 {
            write!(f, "+{}", self.proj)?;
        }
        Ok(())
    }
}

impl Loc {
    #[inline]
    fn new(root: usize, proj: usize) -> Self {
        Self { root, proj }
    }

    #[inline]
    fn new_root(root: usize) -> Self {
        Self { root, proj: 0 }
    }

    #[inline]
    fn add(self, proj: usize) -> Self {
        Self {
            proj: self.proj + proj,
            ..self
        }
    }

    #[inline]
    fn index(self) -> usize {
        self.root + self.proj
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PrefixedLoc {
    deref: bool,
    r#ref: bool,
    var: Loc,
}

impl PrefixedLoc {
    #[inline]
    fn new(var: Loc) -> Self {
        Self {
            deref: false,
            r#ref: false,
            var,
        }
    }

    #[inline]
    fn new_ref(var: Loc) -> Self {
        Self {
            deref: false,
            r#ref: true,
            var,
        }
    }

    #[inline]
    fn with_deref(self, deref: bool) -> Self {
        Self { deref, ..self }
    }

    #[inline]
    fn with_ref(self, r#ref: bool) -> Self {
        Self { r#ref, ..self }
    }

    #[inline]
    fn add(self, proj: usize) -> Self {
        Self {
            var: self.var.add(proj),
            ..self
        }
    }

    #[inline]
    fn index(self) -> usize {
        self.var.index()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocProjection {
    Field(usize),
    Index,
    Deref,
}

#[inline]
pub fn unwrap_ptr(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::Ref(_, ty, _) | TyKind::RawPtr(TypeAndMut { ty, .. }) => Some(*ty),
        _ => None,
    }
}

#[inline]
fn operand_to_fn(operand: &Operand<'_>) -> Option<DefId> {
    let constant = operand.constant()?;
    let ConstantKind::Val(_, ty) = constant.literal else { return None };
    let TyKind::FnDef(def_id, _) = ty.kind() else { return None };
    Some(*def_id)
}

#[inline]
fn is_c_fn(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    for data in tcx.def_path(def_id).data {
        if data.to_string().starts_with("{extern#") {
            return true;
        }
    }
    false
}

#[inline]
fn contains_multiple<T: Idx>(set: &HybridBitSet<T>) -> bool {
    let mut iter = set.iter();
    iter.next().is_some() && iter.next().is_some()
}

struct FnPtrVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    fn_ptrs: HashSet<LocalDefId>,
}

impl<'tcx> FnPtrVisitor<'tcx> {
    #[inline]
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            fn_ptrs: HashSet::new(),
        }
    }

    fn get_function(&self, operand: &Operand<'tcx>) -> Option<LocalDefId> {
        let constant = operand.constant()?;
        let ConstantKind::Val(_, ty) = constant.literal else { return None };
        let TyKind::FnDef(def_id, _) = ty.kind() else { return None };
        let local_def_id = def_id.as_local()?;
        if self.tcx.impl_of_method(*def_id).is_none() && !is_c_fn(*def_id, self.tcx) {
            Some(local_def_id)
        } else {
            None
        }
    }

    fn operand(&mut self, operand: &Operand<'tcx>) {
        let local_def_id = some_or!(self.get_function(operand), return);
        self.fn_ptrs.insert(local_def_id);
    }
}

impl<'tcx> Visitor<'tcx> for FnPtrVisitor<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Use(v)
            | Rvalue::Repeat(v, _)
            | Rvalue::Cast(_, v, _)
            | Rvalue::UnaryOp(_, v) => self.operand(v),
            Rvalue::BinaryOp(_, box (v1, v2)) => {
                self.operand(v1);
                self.operand(v2);
            }
            Rvalue::Aggregate(_, fs) => {
                for f in fs {
                    self.operand(f);
                }
            }
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }
}

#[repr(transparent)]
struct VecBitSet<'a, T: Idx>(&'a Vec<HybridBitSet<T>>);

impl<T: Idx> DirectedGraph for VecBitSet<'_, T> {
    type Node = T;
}

impl<T: Idx> WithNumNodes for VecBitSet<'_, T> {
    fn num_nodes(&self) -> usize {
        self.0.len()
    }
}

impl<'a, T: Idx> GraphSuccessors<'_> for VecBitSet<'a, T> {
    type Item = T;
    type Iter = HybridIter<'a, T>;
}

impl<T: Idx> WithSuccessors for VecBitSet<'_, T> {
    fn successors(&self, node: Self::Node) -> <Self as GraphSuccessors<'_>>::Iter {
        self.0[node.index()].iter()
    }
}

#[cfg(test)]
mod tests;
