use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    path::Path,
};

use etrace::some_or;
use rustc_data_structures::graph::{
    scc::Sccs, DirectedGraph, GraphSuccessors, WithNumNodes, WithSuccessors,
};
use rustc_hir::ItemKind;
use rustc_index::{
    bit_set::{HybridBitSet, HybridIter},
    Idx, IndexVec,
};
use rustc_middle::{
    mir::{
        interpret::{ConstValue, GlobalAlloc, Scalar},
        visit::Visitor,
        AggregateKind, BasicBlock, BinOp, ConstantKind, Local, LocalDecl, Location, Operand, Place,
        PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
    },
    ty::{Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_session::config::Input;
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;

use crate::*;

pub fn analyze_path(path: &Path) {
    analyze_input(compile_util::path_to_input(path));
}

pub fn analyze_str(code: &str) {
    analyze_input(compile_util::str_to_input(code));
}

fn analyze_input(input: Input) {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| {
        analyze(tcx);
    })
    .unwrap();
}

pub struct AnalysisResults {
    pub solutions: Vec<HybridBitSet<usize>>,
    pub ends: Vec<usize>,
}

impl std::fmt::Debug for AnalysisResults {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, sol) in self.solutions.iter().enumerate() {
            let sol: Vec<_> = sol.iter().collect();
            writeln!(f, "{}: {:?}", i, sol)?;
        }
        write!(f, "{:?}", self.ends)
    }
}

pub fn analyze(tcx: TyCtxt<'_>) -> AnalysisResults {
    let hir = tcx.hir();

    let bodies: Vec<_> = hir
        .items()
        .filter_map(|item_id| {
            let item = hir.item(item_id);
            if item.ident.name.as_str() == "main" {
                return None;
            }
            let local_def_id = item.owner_id.def_id;
            let def_id = local_def_id.to_def_id();
            let body = match item.kind {
                ItemKind::Fn(_, _, _) => tcx.optimized_mir(def_id),
                ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(def_id),
                _ => return None,
            };
            Some((local_def_id, body))
        })
        .collect();

    let mut visitor = FnPtrVisitor::new(tcx);
    for (_, body) in &bodies {
        visitor.visit_body(body);
    }
    let fn_ptrs = visitor.fn_ptrs;

    let arena = Arena::new();
    let prim = arena.alloc(TyInfo::Primitive);
    let mut statics = HashMap::new();
    let mut vars = HashMap::new();
    let mut ends = vec![];
    let mut alloc_ends: Vec<usize> = vec![];
    let mut allocs = vec![];
    let mut ty_infos = HashMap::new();
    let mut index_to_loc = vec![];
    for (local_def_id, body) in &bodies {
        let fn_ptr = fn_ptrs.contains(local_def_id);
        let static_index = ends.len();
        statics.insert(*local_def_id, static_index);

        let mut local_decls = body.local_decls.iter_enumerated();
        let ret = local_decls.next().unwrap();
        let mut params = vec![];
        for _ in 0..body.arg_count {
            params.push(local_decls.next().unwrap());
        }
        let local_decls = params
            .into_iter()
            .chain(std::iter::once(ret))
            .chain(local_decls);

        for (local, local_decl) in local_decls {
            vars.insert(Var::Local(*local_def_id, local), ends.len());
            let ty = compute_ty_info(local_decl.ty, &mut ty_infos, prim, &arena, tcx);
            compute_ends(ty, &mut ends);

            let root = LocRoot::Local(*local_def_id, local);
            compute_locs(ty, ProjectedLoc::new_root(root), &mut index_to_loc);

            if fn_ptr && local.index() == 0 {
                ends[static_index] = ends.len() - 1;
            }

            if let Some(ty) = unwrap_ptr(local_decl.ty) {
                let mut ends = vec![];
                let ty = compute_ty_info(ty, &mut ty_infos, prim, &arena, tcx);
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

        let root = LocRoot::Static(*local_def_id);
        index_to_loc[static_index].push(ProjectedLoc::new_root(root));

        for (bb, bbd) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call {
                func, destination, ..
            } = &bbd.terminator().kind
            else {
                continue;
            };
            let def_id = some_or!(operand_to_fn(func), continue);
            let ty = destination.ty(&body.local_decls, tcx).ty;
            if ty.is_unsafe_ptr() && is_c_fn(def_id, tcx) {
                allocs.push(Var::Alloc(*local_def_id, bb));
            }
        }
    }

    let mut alloc_id = 0;
    for alloc in allocs {
        let len = ends.len();
        vars.insert(alloc, len);
        for end in &alloc_ends {
            ends.push(len + *end);

            let root = LocRoot::Alloc(alloc_id);
            index_to_loc.push(vec![ProjectedLoc::new_root(root)]);
            alloc_id += 1;
        }
    }

    let mut analyzer = Analyzer {
        tcx,
        ty_infos,
        vars,
        statics,
        graph: Graph::new(ends.len()),
    };
    for (local_def_id, body) in &bodies {
        // println!("{}", compile_util::body_to_str(body));
        for (block, bbd) in body.basic_blocks.iter_enumerated() {
            for stmt in bbd.statements.iter() {
                let ctx = Context::new(&body.local_decls, *local_def_id);
                analyzer.transfer_stmt(stmt, ctx);
            }
            let terminator = bbd.terminator();
            let ctx = Context::new(&body.local_decls, *local_def_id);
            analyzer.transfer_term(terminator, ctx, block);
        }
    }

    let solutions = analyzer.graph.solve(&ends);
    AnalysisResults { solutions, ends }
}

fn compute_ty_info<'a, 'tcx>(
    ty: Ty<'tcx>,
    tys: &mut HashMap<Ty<'tcx>, &'a TyInfo<'a>>,
    prim: &'a TyInfo<'a>,
    arena: &'a Arena<TyInfo<'a>>,
    tcx: TyCtxt<'tcx>,
) -> &'a TyInfo<'a> {
    if let Some(ty_info) = tys.get(&ty) {
        return ty_info;
    }
    let ty_info = match ty.kind() {
        TyKind::Adt(adt_def, generic_args) => {
            if ty.is_c_void(tcx) {
                prim
            } else {
                let ts = adt_def.variants().iter().flat_map(|variant| {
                    variant
                        .fields
                        .iter()
                        .map(|field| field.ty(tcx, generic_args))
                });
                compute_ty_info_iter(ts, tys, prim, arena, tcx)
            }
        }
        TyKind::Array(ty, _) => {
            let t = compute_ty_info(*ty, tys, prim, arena, tcx);
            arena.alloc(TyInfo::Array(t))
        }
        TyKind::Tuple(ts) => compute_ty_info_iter(ts.iter(), tys, prim, arena, tcx),
        _ => prim,
    };
    tys.insert(ty, ty_info);
    assert_ne!(ty_info.len(), 0);
    ty_info
}

#[inline]
fn compute_ty_info_iter<'a, 'tcx, I: Iterator<Item = Ty<'tcx>>>(
    ts: I,
    tys: &mut HashMap<Ty<'tcx>, &'a TyInfo<'a>>,
    prim: &'a TyInfo<'a>,
    arena: &'a Arena<TyInfo<'a>>,
    tcx: TyCtxt<'tcx>,
) -> &'a TyInfo<'a> {
    let mut len = 0;
    let mut fields = vec![];
    for ty in ts {
        let ty_info = compute_ty_info(ty, tys, prim, arena, tcx);
        fields.push((len, ty_info));
        len += ty_info.len();
    }
    if len == 0 {
        prim
    } else {
        arena.alloc(TyInfo::Struct(len, fields))
    }
}

fn compute_ends(ty: &TyInfo<'_>, ends: &mut Vec<usize>) {
    match ty {
        TyInfo::Primitive => ends.push(ends.len()),
        TyInfo::Array(t) => compute_ends(t, ends),
        TyInfo::Struct(len, ts) => {
            let end = ends.len();
            for (_, t) in ts {
                compute_ends(t, ends);
            }
            ends[end] = end + *len - 1;
        }
    }
}

fn compute_locs(ty: &TyInfo<'_>, loc: ProjectedLoc, index_to_loc: &mut Vec<Vec<ProjectedLoc>>) {
    match ty {
        TyInfo::Primitive => index_to_loc.push(vec![loc]),
        TyInfo::Array(t) => {
            let len = index_to_loc.len();
            compute_locs(t, loc.index(), index_to_loc);
            index_to_loc[len].push(loc);
        }
        TyInfo::Struct(_, ts) => {
            let len = index_to_loc.len();
            for (i, (_, t)) in ts.iter().enumerate() {
                compute_locs(t, loc.field(i), index_to_loc);
            }
            index_to_loc[len].push(loc);
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

struct Analyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ty_infos: HashMap<Ty<'tcx>, &'a TyInfo<'a>>,
    vars: HashMap<Var, usize>,
    statics: HashMap<LocalDefId, usize>,
    graph: Graph,
}

impl<'tcx> Analyzer<'_, 'tcx> {
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
                    let TyInfo::Struct(_, ts) = self.ty_infos[&ty] else { unreachable!() };
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
        let len = self.ty_infos[&ty].len();
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
                        let var = Loc::new_root(self.statics.get(&def_id.as_local()?).copied()?);
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
                    func = func.add(self.ty_infos[&ty].len());
                }
                self.transfer_assign(dst, func, output);
            }
            Operand::Constant(box constant) => {
                let ConstantKind::Val(value, ty) = constant.literal else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                let mut name: Vec<_> = self
                    .tcx
                    .def_path(*def_id)
                    .data
                    .into_iter()
                    .map(|data| data.to_string())
                    .collect();
                let is_extern = name.iter().any(|s| s.starts_with("{extern#"));
                while name.len() < 4 {
                    name.push(String::new());
                }
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
                            let loc = Loc::new_root(self.vars[&var]);
                            self.transfer_assign(dst, PrefixedLoc::new_ref(loc), output);
                        }
                    } else {
                        let mut index = self.statics[&local_def_id];
                        for (arg, arg_loc) in args.iter().zip(arg_locs) {
                            let ty = arg.ty(ctx.locals, self.tcx);
                            if let Some(arg) = arg_loc {
                                let loc = Loc::new_root(index);
                                self.transfer_assign(PrefixedLoc::new(loc), arg, ty);
                            }
                            index += self.ty_infos[&ty].len();
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
        let loc = Loc::new_root(self.vars.get(&var).copied()?);
        Some(PrefixedLoc::new_ref(loc))
    }

    fn prefixed_loc(&self, place: Place<'tcx>, ctx: Context<'_, 'tcx>) -> PrefixedLoc {
        let mut index = 0;
        let mut ty = ctx.locals[place.local].ty;
        let deref = place.is_indirect_first_projection();
        if deref {
            ty = unwrap_ptr(ty).unwrap();
        }
        let mut ty = self.ty_infos[&ty];
        for proj in place.projection {
            match proj {
                PlaceElem::Deref => {}
                PlaceElem::Index(_) => {
                    let TyInfo::Array(t) = ty else { unreachable!() };
                    ty = t;
                }
                PlaceElem::Field(f, _) => {
                    let TyInfo::Struct(_, fs) = ty else { unreachable!() };
                    let (i, nested_ty) = fs[f.index()];
                    index += i;
                    ty = nested_ty;
                }
                _ => unreachable!(),
            }
        }
        let var = Var::Local(ctx.owner, place.local);
        let loc = Loc::new(self.vars[&var], index);
        PrefixedLoc::new(loc).with_deref(place.is_indirect_first_projection())
    }
}

type WeightedGraph = HashMap<usize, HashMap<usize, HashSet<usize>>>;

struct Graph {
    solutions: Vec<HybridBitSet<usize>>,
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

    fn solve(self, ends: &[usize]) -> Vec<HybridBitSet<usize>> {
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

#[allow(variant_size_differences)]
enum TyInfo<'a> {
    Primitive,
    Array(&'a TyInfo<'a>),
    Struct(usize, Vec<(usize, &'a TyInfo<'a>)>),
}

impl std::fmt::Debug for TyInfo<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primitive => write!(f, "*"),
            Self::Array(t) => write!(f, "[{:?}]", t),
            Self::Struct(len, fields) => {
                write!(f, "[{}", len)?;
                for (i, ty_info) in fields {
                    let sep = if *i == 0 { ";" } else { "," };
                    write!(f, "{} {}: {:?}", sep, i, ty_info)?;
                }
                write!(f, "]")
            }
        }
    }
}

impl TyInfo<'_> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::Primitive => 1,
            Self::Array(t) => t.len(),
            Self::Struct(len, _) => *len,
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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocRoot {
    Static(LocalDefId),
    Local(LocalDefId, Local),
    Alloc(usize),
}

impl std::fmt::Debug for LocRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocRoot::Static(def_id) => write!(f, "{:?}", def_id),
            LocRoot::Local(def_id, local) => write!(f, "{:?}:{:?}", def_id, local),
            LocRoot::Alloc(id) => write!(f, "alloc{}", id),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocProjection {
    Field(usize),
    Index,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ProjectedLoc {
    root: LocRoot,
    projection: Vec<LocProjection>,
}

impl ProjectedLoc {
    #[inline]
    fn new_root(root: LocRoot) -> Self {
        Self {
            root,
            projection: vec![],
        }
    }

    #[inline]
    fn field(&self, i: usize) -> Self {
        let mut this = self.clone();
        this.projection.push(LocProjection::Field(i));
        this
    }

    #[inline]
    fn index(&self) -> Self {
        let mut this = self.clone();
        this.projection.push(LocProjection::Index);
        this
    }
}

impl std::fmt::Debug for ProjectedLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.root)?;
        for proj in &self.projection {
            match proj {
                LocProjection::Field(i) => write!(f, ".{}", i)?,
                LocProjection::Index => write!(f, "[]")?,
            }
        }
        Ok(())
    }
}

#[inline]
fn unwrap_ptr(ty: Ty<'_>) -> Option<Ty<'_>> {
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
