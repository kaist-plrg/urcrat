use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::Path,
};

use disjoint_set::DisjointSet;
use etrace::some_or;
use lazy_static::lazy_static;
use rustc_hir::{ForeignItemKind, Item, ItemKind, Node};
use rustc_middle::{
    mir::{
        interpret::{ConstValue, GlobalAlloc, Scalar},
        visit::Visitor,
        BasicBlock, BinOp, ConstantKind, Local, Location, Operand, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_session::config::Input;
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;

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

    let var_arena = typed_arena::Arena::new();
    let fn_arena = typed_arena::Arena::new();
    let mut analyzer = Analyzer::new(tcx, &var_arena, &fn_arena);

    let mut cstrss: HashMap<_, Vec<_>> = HashMap::new();
    let mut fn_ptrs = HashSet::new();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.name.as_str() == "main" {
            continue;
        }
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let body = match item.kind {
            ItemKind::Fn(_, _, _) => tcx.optimized_mir(def_id),
            ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(def_id),
            _ => continue,
        };
        let mut visitor = BodyVisitor::new(tcx);
        visitor.visit_body(body);
        for (bb, callee) in visitor.calls {
            cstrss
                .entry(callee)
                .or_default()
                .push(CallStr::Single(local_def_id, bb));
        }
        fn_ptrs.extend(visitor.fn_ptrs);
    }
    for fn_ptr in fn_ptrs {
        cstrss.entry(fn_ptr).or_default().push(CallStr::Empty);
    }

    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.name.as_str() == "main" {
            continue;
        }
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        match item.kind {
            ItemKind::ForeignMod { items, .. } => {
                for item_ref in items {
                    let item = hir.foreign_item(item_ref.id);
                    if !matches!(item.kind, ForeignItemKind::Static(_, _)) {
                        continue;
                    }
                    let id = VarId::Global(CallStr::Empty, item.owner_id.def_id);
                    analyzer.insert_and_allocate(id);
                }
            }
            ItemKind::Static(_, _, _) => {
                let body = tcx.mir_for_ctfe(def_id);
                let local_decls = body.local_decls.len();

                for i in 0..local_decls {
                    let id = VarId::Local(CallStr::Empty, local_def_id, i as _);
                    analyzer.insert_and_allocate(id);
                }

                let id = VarId::Global(CallStr::Empty, local_def_id);
                analyzer.insert_and_allocate(id);
                analyzer.x_eq_y(id, VarId::Local(CallStr::Empty, local_def_id, 0));

                cstrss.insert(local_def_id, vec![CallStr::Empty]);
            }
            ItemKind::Fn(_, _, _) => {
                let body = tcx.optimized_mir(def_id);
                let local_decls = body.local_decls.len();

                let cstrs = cstrss
                    .entry(local_def_id)
                    .or_insert_with(|| vec![CallStr::Empty]);
                for cstr in cstrs {
                    for i in 0..local_decls {
                        let id = VarId::Local(*cstr, local_def_id, i as _);
                        analyzer.insert_and_allocate(id);
                    }

                    let id = VarId::Global(*cstr, local_def_id);
                    analyzer.insert_and_allocate(id);
                    analyzer.x_eq_fn(*cstr, id, local_def_id, body.arg_count);
                }
            }
            _ => {}
        }
    }

    for item_id in hir.items() {
        let item = hir.item(item_id);
        if !matches!(item.kind, ItemKind::Static(_, _, _) | ItemKind::Fn(_, _, _)) {
            continue;
        }
        if item.ident.name.as_str() == "main" {
            continue;
        }

        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let body = if matches!(item.kind, ItemKind::Fn(_, _, _)) {
            tcx.optimized_mir(def_id)
        } else {
            tcx.mir_for_ctfe(def_id)
        };
        for cstr in &cstrss[&local_def_id] {
            for (bb, bbd) in body.basic_blocks.iter_enumerated() {
                for stmt in &bbd.statements {
                    analyzer.transfer_stmt(*cstr, local_def_id, stmt);
                }
                let term = bbd.terminator();
                analyzer.transfer_term(*cstr, local_def_id, term, bb);
            }
        }
    }

    analyzer.get_results()
}

struct BodyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    calls: Vec<(BasicBlock, LocalDefId)>,
    fn_ptrs: HashSet<LocalDefId>,
}

impl<'tcx> BodyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            calls: Vec::new(),
            fn_ptrs: HashSet::new(),
        }
    }

    fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }

    fn get_function(&self, operand: &Operand<'tcx>) -> Option<LocalDefId> {
        let constant = operand.constant()?;
        let ConstantKind::Val(value, ty) = constant.literal else { return None };
        if !matches!(value, ConstValue::ZeroSized) {
            return None;
        }
        let TyKind::FnDef(def_id, _) = ty.kind() else { return None };
        let local_def_id = def_id.as_local()?;
        if self.tcx.impl_of_method(*def_id).is_none()
            && !self.def_id_to_string(*def_id).contains("{extern#")
        {
            Some(local_def_id)
        } else {
            None
        }
    }

    fn terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        let TerminatorKind::Call { func, .. } = &terminator.kind else { return };
        let local_def_id = some_or!(self.get_function(func), return);
        self.calls.push((location.block, local_def_id));
    }

    fn operand(&mut self, operand: &Operand<'tcx>) {
        let local_def_id = some_or!(self.get_function(operand), return);
        self.fn_ptrs.insert(local_def_id);
    }
}

impl<'tcx> Visitor<'tcx> for BodyVisitor<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.terminator(terminator, location);
        self.super_terminator(terminator, location);
    }

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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallStr {
    Empty,
    Single(LocalDefId, BasicBlock),
}

impl PartialOrd for CallStr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CallStr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;

        use rustc_index::Idx;
        match (self, other) {
            (Self::Empty, Self::Empty) => Equal,
            (Self::Empty, Self::Single(_, _)) => Less,
            (Self::Single(_, _), Self::Empty) => Greater,
            (Self::Single(id1, bb1), Self::Single(id2, bb2)) => {
                match id1.index().cmp(&id2.index()) {
                    Equal => bb1.cmp(bb2),
                    x => x,
                }
            }
        }
    }
}

impl std::fmt::Debug for CallStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CallStr::Empty => write!(f, "ε"),
            CallStr::Single(id, bb) => {
                write!(f, "{:?}:{:?}", id.local_def_index.index(), bb.index())
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum VarId {
    Global(CallStr, LocalDefId),
    Local(CallStr, LocalDefId, u32),
    Temp(usize),
}

impl std::fmt::Debug for VarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Global(cs, id) => write!(f, "[{:?}]#{:?}", cs, id.local_def_index.index()),
            Self::Local(cs, id, i) => {
                write!(f, "[{:?}]#{:?}_{}", cs, id.local_def_index.index(), i)
            }
            Self::Temp(i) => write!(f, "#t{}", i),
        }
    }
}

impl PartialOrd for VarId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VarId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;

        use rustc_index::Idx;
        match (self, other) {
            (Self::Global(cs1, id1), Self::Global(cs2, id2)) => match cs1.cmp(cs2) {
                Equal => id1.index().cmp(&id2.index()),
                x => x,
            },
            (Self::Global(_, _), _) => Less,
            (Self::Local(_, _, _), Self::Global(_, _)) => Greater,
            (Self::Local(cs1, id1, l1), Self::Local(cs2, id2, l2)) => match cs1.cmp(cs2) {
                Equal => match id1.index().cmp(&id2.index()) {
                    Equal => l1.cmp(l2),
                    x => x,
                },
                x => x,
            },
            (Self::Local(_, _, _), _) => Less,
            (Self::Temp(i1), Self::Temp(i2)) => i1.cmp(i2),
            (Self::Temp(_), _) => Greater,
        }
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FnId(usize);

impl std::fmt::Debug for FnId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Type {
    pub var_ty: VarId,
    fn_ty: FnId,
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:?}, {:?})", self.var_ty, self.fn_ty)
    }
}

impl Type {
    fn subst(&mut self, vars: &HashMap<VarId, VarId>, fns: &HashMap<FnId, FnId>) {
        self.var_ty = vars[&self.var_ty];
        self.fn_ty = fns[&self.fn_ty];
    }
}

type Unify<T, S> = (Vec<(T, T)>, Vec<(S, S)>);

trait Domain {
    type I1: Copy + Eq + std::hash::Hash;
    type I2: Copy + Eq + std::hash::Hash;

    fn bot() -> Self;
    fn is_bot(&self) -> bool;
    fn unify(self, other: Self) -> Unify<Self::I1, Self::I2>;
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum VarType {
    Bot,
    Ref(Type),
}

impl std::fmt::Debug for VarType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VarType::Bot => write!(f, "⊥"),
            VarType::Ref(ty) => write!(f, "Ref{:?}", ty),
        }
    }
}

impl Domain for VarType {
    type I1 = VarId;
    type I2 = FnId;

    #[inline]
    fn bot() -> Self {
        VarType::Bot
    }

    #[inline]
    fn is_bot(&self) -> bool {
        matches!(self, VarType::Bot)
    }

    fn unify(self, other: Self) -> Unify<Self::I1, Self::I2> {
        let VarType::Ref(t1) = self else { panic!() };
        let VarType::Ref(t2) = other else { panic!() };
        (vec![(t1.var_ty, t2.var_ty)], vec![(t1.fn_ty, t2.fn_ty)])
    }
}

impl VarType {
    #[inline]
    fn new(var_ty: VarId, fn_ty: FnId) -> Self {
        VarType::Ref(Type { var_ty, fn_ty })
    }

    fn subst(&mut self, vars: &HashMap<VarId, VarId>, fns: &HashMap<FnId, FnId>) {
        if let Self::Ref(ty) = self {
            ty.subst(vars, fns);
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum FnType {
    Bot,
    Lambda(Vec<Type>, Type),
}

impl std::fmt::Debug for FnType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FnType::Bot => write!(f, "⊥"),
            FnType::Lambda(arg_tys, ret_ty) => {
                write!(f, "{:?} -> {:?}", arg_tys, ret_ty)
            }
        }
    }
}

impl Domain for FnType {
    type I1 = FnId;
    type I2 = VarId;

    #[inline]
    fn bot() -> Self {
        FnType::Bot
    }

    #[inline]
    fn is_bot(&self) -> bool {
        matches!(self, FnType::Bot)
    }

    fn unify(self, other: Self) -> Unify<Self::I1, Self::I2> {
        let FnType::Lambda(p1, r1) = self else { panic!() };
        let FnType::Lambda(p2, r2) = other else { panic!() };
        std::iter::once(r1)
            .chain(p1)
            .zip(std::iter::once(r2).chain(p2))
            .map(|(t1, t2)| ((t1.fn_ty, t2.fn_ty), (t1.var_ty, t2.var_ty)))
            .unzip()
    }
}

impl FnType {
    fn subst(&mut self, vars: &HashMap<VarId, VarId>, fns: &HashMap<FnId, FnId>) {
        if let Self::Lambda(arg_tys, ret_ty) = self {
            for t in arg_tys {
                t.subst(vars, fns);
            }
            ret_ty.subst(vars, fns);
        }
    }
}

type Ecr<'a, I> = &'a DisjointSet<'a, I>;

struct Ecrs<'a, T: Domain> {
    ecrs: HashMap<T::I1, Ecr<'a, T::I1>>,
    types: HashMap<T::I1, T>,
    pendings: HashMap<T::I1, HashSet<T::I1>>,
}

impl<'a, T: Clone + Domain> Ecrs<'a, T> {
    fn new() -> Self {
        Self {
            ecrs: HashMap::new(),
            types: HashMap::new(),
            pendings: HashMap::new(),
        }
    }

    #[inline]
    fn root(&self, x: T::I1) -> T::I1 {
        self.ecrs[&x].find_set().id()
    }

    #[inline]
    fn insert(&mut self, x: T::I1, e: Ecr<'a, T::I1>) {
        self.ecrs.insert(x, e);
        self.types.insert(x, T::bot());
    }

    fn set_type<S>(&mut self, e: T::I1, t: T, other: &mut Ecrs<'a, S>)
    where S: Clone + Domain<I1 = T::I2, I2 = T::I1> {
        let e = self.root(e);
        self.types.insert(e, t);
        let pendings = some_or!(self.pendings.remove(&e), return);
        for x in pendings {
            self.join(e, x, other);
        }
    }

    fn cond_join<S>(&mut self, e1: T::I1, e2: T::I1, other: &mut Ecrs<'a, S>)
    where S: Clone + Domain<I1 = T::I2, I2 = T::I1> {
        let e1 = self.root(e1);
        let e2 = self.root(e2);
        if e1 == e2 {
            return;
        }
        let t2 = &self.types[&e2];
        if t2.is_bot() {
            self.pendings.entry(e2).or_default().insert(e1);
        } else {
            self.join(e1, e2, other);
        }
    }

    fn join<S>(&mut self, e1: T::I1, e2: T::I1, other: &mut Ecrs<'a, S>)
    where S: Clone + Domain<I1 = T::I2, I2 = T::I1> {
        let e1 = self.ecrs[&e1].find_set();
        let e2 = self.ecrs[&e2].find_set();
        if e1 == e2 {
            return;
        }

        let e1_id = e1.id();
        let e2_id = e2.id();
        let e = e1.union(e2);

        let e = e.id();
        let e1 = e1_id;
        let e2 = e2_id;

        let t1 = self.types[&e1].clone();
        let t2 = self.types[&e2].clone();
        let t1_is_bot = t1.is_bot();
        let t2_is_bot = t2.is_bot();

        if t1_is_bot {
            self.types.insert(e, t2);
            if t2_is_bot {
                if e1 == e {
                    if let Some(s) = self.pendings.remove(&e2) {
                        self.pendings.entry(e).or_default().extend(s);
                    }
                } else if let Some(s) = self.pendings.remove(&e1) {
                    self.pendings.entry(e).or_default().extend(s);
                }
            } else if let Some(pendings) = self.pendings.remove(&e1) {
                for x in pendings {
                    self.join(e, x, other);
                }
            }
        } else {
            self.types.insert(e, t1.clone());
            if t2_is_bot {
                if let Some(pendings) = self.pendings.remove(&e2) {
                    for x in pendings {
                        self.join(e, x, other);
                    }
                }
            } else {
                let (this_ts, other_ts) = t1.unify(t2);
                for (t1, t2) in this_ts {
                    self.join(t1, t2, other);
                }
                for (t1, t2) in other_ts {
                    other.join(t1, t2, self);
                }
            }
        }
    }
}

struct Analyzer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    id: usize,

    var_arena: &'a Arena<DisjointSet<'a, VarId>>,
    fn_arena: &'a Arena<DisjointSet<'a, FnId>>,

    var_ecrs: Ecrs<'a, VarType>,
    fn_ecrs: Ecrs<'a, FnType>,
}

pub struct AnalysisResults {
    vars: HashMap<VarId, VarId>,
    var_tys: HashMap<VarId, VarType>,
    fns: HashMap<FnId, FnId>,
    fn_tys: HashMap<FnId, FnType>,
}

impl std::fmt::Debug for AnalysisResults {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut inv_vars: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
        for (k, v) in &self.vars {
            inv_vars.entry(v).or_default().insert(k);
        }
        for (id, ids) in inv_vars {
            let ty = &self.var_tys[id];
            writeln!(f, "{:?}: {:?}", ids, ty)?;
        }

        let mut inv_fns: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
        for (k, v) in &self.fns {
            inv_fns.entry(v).or_default().insert(k);
        }
        for (id, ids) in inv_fns {
            let ty = &self.fn_tys[id];
            writeln!(f, "{:?}: {:?}", ids, ty)?;
        }

        Ok(())
    }
}

impl AnalysisResults {
    #[inline]
    pub fn local(&self, cstr: CallStr, f: LocalDefId, i: u32) -> VarId {
        self.vars[&VarId::Local(cstr, f, i)]
    }

    #[inline]
    pub fn global(&self, cstr: CallStr, f: LocalDefId) -> VarId {
        self.vars[&VarId::Global(cstr, f)]
    }

    #[inline]
    pub fn var_ty(&self, id: VarId) -> Type {
        let VarType::Ref(ty) = self.var_tys[&id] else { panic!() };
        ty
    }

    pub fn get_alias_graph(&self) -> AliasGraph {
        let id_to_node = self.vars.clone();
        let mut local_to_nodes: HashMap<_, HashSet<_>> = HashMap::new();
        for (id, node) in &id_to_node {
            let VarId::Local(_, local_def_id, local) = id else { continue };
            local_to_nodes
                .entry((*local_def_id, *local))
                .or_default()
                .insert(*node);
        }
        let node_to_ids = inv(&id_to_node);
        let (points_to, points_to_fn): (HashMap<_, _>, HashMap<_, _>) = self
            .var_tys
            .iter()
            .filter_map(|(k, v)| {
                let VarType::Ref(ty) = v else { return None };
                Some(((*k, ty.var_ty), (*k, ty.fn_ty)))
            })
            .unzip();
        let pointed_by = inv(&points_to);
        let pointed_by_fn = inv(&points_to_fn);
        AliasGraph {
            id_to_node,
            local_to_nodes,
            node_to_ids,
            points_to,
            pointed_by,
            points_to_fn,
            fn_pointed_by: pointed_by_fn,
        }
    }
}

fn inv<T, S>(map: &HashMap<T, S>) -> HashMap<S, HashSet<T>>
where
    T: Eq + std::hash::Hash + Copy,
    S: Eq + std::hash::Hash + Copy,
{
    let mut new_map: HashMap<_, HashSet<_>> = HashMap::new();
    for (k, v) in map {
        new_map.entry(*v).or_default().insert(*k);
    }
    new_map
}

#[derive(Debug)]
pub struct AliasGraph {
    id_to_node: HashMap<VarId, VarId>,
    local_to_nodes: HashMap<(LocalDefId, u32), HashSet<VarId>>,
    node_to_ids: HashMap<VarId, HashSet<VarId>>,
    points_to: HashMap<VarId, VarId>,
    pointed_by: HashMap<VarId, HashSet<VarId>>,
    points_to_fn: HashMap<VarId, FnId>,
    fn_pointed_by: HashMap<FnId, HashSet<VarId>>,
}

impl AliasGraph {
    pub fn find_may_aliases(
        &self,
        fls: &[(LocalDefId, Local)],
        caller: LocalDefId,
    ) -> HashSet<(Local, usize)> {
        let mut aliases = HashSet::new();
        let mut done = HashSet::new();

        let mut remainings: HashSet<_> = fls
            .iter()
            .flat_map(|(local_def_id, local)| {
                self.local_to_nodes[&(*local_def_id, local.as_u32())]
                    .iter()
                    .map(|node| (self.points_to[node], 0))
            })
            .collect();

        while !remainings.is_empty() {
            let mut new_remainings = HashSet::new();
            for (node, depth) in remainings {
                done.insert(node);
                for node in &self.node_to_ids[&node] {
                    let VarId::Local(_, f, l) = *node else { continue };
                    if f == caller {
                        aliases.insert((Local::from_u32(l), depth));
                    }
                }
                if let Some(nodes) = self.pointed_by.get(&node) {
                    for node in nodes {
                        if !done.contains(node) {
                            new_remainings.insert((*node, depth + 1));
                        }
                    }
                }
            }
            remainings = new_remainings;
        }

        aliases
    }

    pub fn find_fn_may_aliases(
        &self,
        f: LocalDefId,
        l: Local,
        tcx: TyCtxt<'_>,
    ) -> HashSet<LocalDefId> {
        self.id_to_node
            .iter()
            .filter_map(|(id, node)| {
                let VarId::Local(_, local_def_id, local) = id else { return None };
                if *local_def_id == f && *local == l.as_u32() {
                    Some(&self.fn_pointed_by[&self.points_to_fn[node]])
                } else {
                    None
                }
            })
            .flatten()
            .filter_map(|node| {
                let VarId::Global(_, f) = node else { return None };
                let node = tcx.hir().find_by_def_id(*f).unwrap();
                if matches!(
                    node,
                    Node::Item(Item {
                        kind: ItemKind::Fn(..),
                        ..
                    })
                ) {
                    Some(*f)
                } else {
                    None
                }
            })
            .collect()
    }
}

impl<'tcx, 'a> Analyzer<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        var_arena: &'a Arena<DisjointSet<'a, VarId>>,
        fn_arena: &'a Arena<DisjointSet<'a, FnId>>,
    ) -> Self {
        Self {
            tcx,
            id: 0,
            var_arena,
            fn_arena,
            var_ecrs: Ecrs::new(),
            fn_ecrs: Ecrs::new(),
        }
    }

    fn transfer_stmt(&mut self, cstr: CallStr, func: LocalDefId, stmt: &Statement<'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        let l_id = VarId::Local(cstr, func, l.local.as_u32());
        let l_deref = l.is_indirect_first_projection();
        match r {
            Rvalue::Use(r)
            | Rvalue::Repeat(r, _)
            | Rvalue::Cast(_, r, _)
            | Rvalue::UnaryOp(_, r) => self.transfer_operand(cstr, func, l_id, l_deref, r),
            Rvalue::Ref(_, _, r) => {
                assert!(!l_deref);
                let r_id = VarId::Local(cstr, func, r.local.as_u32());
                if r.is_indirect_first_projection() {
                    self.x_eq_y(l_id, r_id);
                } else {
                    self.x_eq_ref_y(l_id, r_id);
                }
            }
            Rvalue::ThreadLocalRef(def_id) => {
                assert!(!l_deref);
                let r_id = VarId::Global(cstr, def_id.as_local().unwrap());
                self.x_eq_ref_y(l_id, r_id);
            }
            Rvalue::AddressOf(_, r) => {
                assert!(!l_deref);
                assert!(r.is_indirect_first_projection());
                let r_id = VarId::Local(cstr, func, r.local.as_u32());
                self.x_eq_y(l_id, r_id);
            }
            Rvalue::Len(_) => unreachable!(),
            Rvalue::BinaryOp(op, box (r1, r2)) | Rvalue::CheckedBinaryOp(op, box (r1, r2)) => {
                if !matches!(
                    op,
                    BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt
                ) {
                    self.transfer_operand(cstr, func, l_id, l_deref, r1);
                    self.transfer_operand(cstr, func, l_id, l_deref, r2);
                }
            }
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::Discriminant(_) => {}
            Rvalue::Aggregate(box _, rs) => {
                for r in rs {
                    self.transfer_operand(cstr, func, l_id, l_deref, r);
                }
            }
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                assert!(!l_deref);
                let r_id = VarId::Local(cstr, func, r.local.as_u32());
                if r.is_indirect_first_projection() {
                    self.x_eq_deref_y(l_id, r_id);
                } else {
                    self.x_eq_y(l_id, r_id);
                }
            }
        }
    }

    fn transfer_operand(
        &mut self,
        cstr: CallStr,
        func: LocalDefId,
        l_id: VarId,
        l_deref: bool,
        r: &Operand<'_>,
    ) {
        match r {
            Operand::Copy(r) | Operand::Move(r) => {
                let r_deref = r.is_indirect_first_projection();
                let r_id = VarId::Local(cstr, func, r.local.as_u32());
                match (l_deref, r_deref) {
                    (false, false) => self.x_eq_y(l_id, r_id),
                    (false, true) => self.x_eq_deref_y(l_id, r_id),
                    (true, false) => self.deref_x_eq_y(l_id, r_id),
                    (true, true) => self.deref_x_eq_deref_y(l_id, r_id),
                }
            }
            Operand::Constant(box constant) => match constant.literal {
                ConstantKind::Ty(_) => unreachable!(),
                ConstantKind::Unevaluated(_, _) => {}
                ConstantKind::Val(value, ty) => match value {
                    ConstValue::Scalar(scalar) => match scalar {
                        Scalar::Int(_) => {}
                        Scalar::Ptr(ptr, _) => match self.tcx.global_alloc(ptr.provenance) {
                            GlobalAlloc::Static(def_id) => {
                                let r_id =
                                    VarId::Global(CallStr::Empty, def_id.as_local().unwrap());
                                assert!(!l_deref);
                                self.x_eq_ref_y(l_id, r_id);
                            }
                            GlobalAlloc::Memory(_) => {
                                self.x_eq_alloc(l_id);
                            }
                            _ => unreachable!(),
                        },
                    },
                    ConstValue::ZeroSized => {
                        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                        let name = self.def_id_to_string(*def_id);
                        if !name.contains("{extern#") {
                            let r_id = VarId::Global(CallStr::Empty, def_id.as_local().unwrap());
                            assert!(!l_deref);
                            self.x_eq_y(l_id, r_id);
                        }
                    }
                    ConstValue::Slice { .. } => unreachable!(),
                    ConstValue::ByRef { .. } => unreachable!(),
                },
            },
        }
    }

    fn transfer_term(
        &mut self,
        cstr: CallStr,
        caller: LocalDefId,
        term: &Terminator<'tcx>,
        bb: BasicBlock,
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
        assert!(!destination.is_indirect_first_projection());
        let d_id = VarId::Local(cstr, caller, destination.local.as_u32());

        match func {
            Operand::Copy(func) | Operand::Move(func) => {
                assert!(!func.is_indirect_first_projection());
                let callee = VarId::Local(cstr, caller, func.local.as_u32());
                self.transfer_intra_call(cstr, caller, callee, args, d_id);
            }
            Operand::Constant(box constant) => {
                let ConstantKind::Val(value, ty) = constant.literal else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                let name = self.def_id_to_string(*def_id);
                let mut segs: Vec<_> = name.split("::").collect();
                let seg0 = segs.pop().unwrap_or_default();
                let seg1 = segs.pop().unwrap_or_default();
                let seg2 = segs.pop().unwrap_or_default();
                let seg3 = segs.pop().unwrap_or_default();
                let sig = self.tcx.fn_sig(def_id).skip_binder();
                let inputs = sig.inputs().skip_binder();
                let output = sig.output().skip_binder();
                if let Some(local_def_id) = def_id.as_local() {
                    if let Some(impl_def_id) = self.tcx.impl_of_method(*def_id) {
                        let span = self.tcx.span_of_impl(impl_def_id).unwrap();
                        let code = self.tcx.sess.source_map().span_to_snippet(span).unwrap();
                        assert_eq!(code, "BitfieldStruct");
                    } else if seg1.contains("{extern#") {
                        self.transfer_c_call(cstr, caller, seg0, inputs, output, args, d_id);
                    } else {
                        let callee = VarId::Global(CallStr::Single(caller, bb), local_def_id);
                        self.transfer_intra_call(cstr, caller, callee, args, d_id);
                    }
                } else {
                    self.transfer_rust_call(
                        cstr,
                        caller,
                        (seg3, seg2, seg1, seg0),
                        inputs,
                        output,
                        args,
                        d_id,
                    );
                }
            }
        }
    }

    fn transfer_intra_call(
        &mut self,
        cstr: CallStr,
        caller: LocalDefId,
        callee: VarId,
        args: &[Operand<'_>],
        dst: VarId,
    ) {
        let (_, ft) = self.variable_type(callee);
        if self.fn_type(ft).is_bot() {
            let args = args.iter().map(|_| self.mk_ecr()).collect();
            let ret = self.mk_ecr();
            self.fn_set_type(ft, FnType::Lambda(args, ret));
        }
        let FnType::Lambda(params, ret) = self.fn_type(ft) else { panic!() };
        let ret = *ret;

        for (p, a) in params.clone().into_iter().zip(args) {
            match a {
                Operand::Copy(a) | Operand::Move(a) => {
                    assert!(!a.is_indirect_first_projection());
                    let a_id = VarId::Local(cstr, caller, a.local.as_u32());
                    let (vt, ft) = self.variable_type(a_id);
                    self.var_cond_join(p.var_ty, vt);
                    self.fn_cond_join(p.fn_ty, ft);
                }
                Operand::Constant(box constant) => {
                    assert!(constant.ty().is_primitive());
                }
            }
        }

        let (vt, ft) = self.variable_type(dst);
        self.var_cond_join(vt, ret.var_ty);
        self.fn_cond_join(ft, ret.fn_ty);
    }

    #[allow(clippy::too_many_arguments)]
    fn transfer_c_call(
        &mut self,
        cstr: CallStr,
        caller: LocalDefId,
        name: &str,
        inputs: &[Ty<'_>],
        output: Ty<'_>,
        args: &[Operand<'_>],
        dst: VarId,
    ) {
        if (output.is_unit() || output.is_never() || output.is_primitive())
            && inputs.iter().filter(|t| !t.is_primitive()).count() < 2
            || name.contains("printf")
            || NO_OP_C_FNS.contains(name)
        {
        } else if output.is_unsafe_ptr() && inputs.iter().all(|t| t.is_primitive())
            || ALLOC_C_FNS.contains(name)
        {
            self.x_eq_alloc(dst);
        } else if name == "realloc" {
            self.transfer_operand(cstr, caller, dst, false, &args[0]);
            self.x_eq_alloc(dst);
        } else if RET_0_C_FNS.contains(name) {
            self.transfer_operand(cstr, caller, dst, false, &args[0]);
        } else if name == "bcopy" {
            let l = args[1].place().unwrap();
            let r = args[0].place().unwrap();
            assert!(!l.is_indirect_first_projection());
            assert!(!r.is_indirect_first_projection());
            let l_id = VarId::Local(cstr, caller, l.local.as_u32());
            let r_id = VarId::Local(cstr, caller, r.local.as_u32());
            self.deref_x_eq_deref_y(l_id, r_id);
        } else if COPY_C_FNS.contains(name) {
            let l = args[0].place().unwrap();
            let r = args[1].place().unwrap();
            assert!(!l.is_indirect_first_projection());
            assert!(!r.is_indirect_first_projection());
            let l_id = VarId::Local(cstr, caller, l.local.as_u32());
            let r_id = VarId::Local(cstr, caller, r.local.as_u32());
            self.deref_x_eq_deref_y(l_id, r_id);
            self.x_eq_y(dst, l_id);
        } else {
            tracing::info!("{}", name);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn transfer_rust_call(
        &mut self,
        cstr: CallStr,
        caller: LocalDefId,
        name: (&str, &str, &str, &str),
        inputs: &[Ty<'_>],
        output: Ty<'_>,
        args: &[Operand<'_>],
        dst: VarId,
    ) {
        if (output.is_unit() || output.is_never() || output.is_primitive())
            && inputs.iter().filter(|t| !t.is_primitive()).count() < 2
        {
            return;
        }
        match name {
            (_, "slice", _, "as_ptr" | "as_mut_ptr")
            | ("ptr", _, _, "offset" | "offset_from")
            | ("ops", "deref", _, "deref" | "deref_mut")
            | ("", "option", _, "unwrap")
            | ("", "result", _, "unwrap")
            | ("", "vec", _, "as_mut_ptr" | "leak") => {
                self.transfer_operand(cstr, caller, dst, false, &args[0]);
            }
            ("", "", "ptr", "write_volatile") => {
                let l = args[0].place().unwrap();
                assert!(!l.is_indirect_first_projection());
                let l_id = VarId::Local(cstr, caller, l.local.as_u32());
                self.transfer_operand(cstr, caller, l_id, true, &args[1]);
            }
            ("", "clone", "Clone", "clone")
            | ("", "ffi", _, "as_va_list")
            | ("", "ffi", _, "arg")
            | ("", "", "ptr", "read_volatile") => {
                let a = args[0].place().unwrap();
                assert!(!a.is_indirect_first_projection());
                let a_id = VarId::Local(cstr, caller, a.local.as_u32());
                self.x_eq_deref_y(dst, a_id);
            }
            ("", "", "vec", "from_elem") => {
                self.x_eq_alloc(dst);
            }
            ("", "unix", _, "memcpy") => {
                let l = args[0].place().unwrap();
                let r = args[1].place().unwrap();
                assert!(!l.is_indirect_first_projection());
                assert!(!r.is_indirect_first_projection());
                let l_id = VarId::Local(cstr, caller, l.local.as_u32());
                let r_id = VarId::Local(cstr, caller, r.local.as_u32());
                self.deref_x_eq_deref_y(l_id, r_id);
                self.x_eq_y(dst, l_id);
            }
            ("", "num", _, name) if name.starts_with("overflowing_") => {
                self.transfer_operand(cstr, caller, dst, false, &args[0]);
                self.transfer_operand(cstr, caller, dst, false, &args[1]);
            }
            (_, _, "AsmCastTrait", _)
            | ("", "cast", "ToPrimitive", _)
            | ("", "cmp", "PartialEq", _)
            | ("", "cmp", "PartialOrd", _)
            | ("", "convert", _, _)
            | ("ops", "arith", _, _)
            | ("", "f128_t", _, _) => {}
            _ => tracing::info!("{:?}", name),
        }
    }

    fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }

    fn get_results(&self) -> AnalysisResults {
        let vars: HashMap<_, _> = self
            .var_ecrs
            .ecrs
            .iter()
            .map(|(i, ecr)| (*i, ecr.id()))
            .collect();
        let fns: HashMap<_, _> = self
            .fn_ecrs
            .ecrs
            .iter()
            .map(|(i, ecr)| (*i, ecr.id()))
            .collect();

        let var_set: HashSet<_> = vars.values().collect();
        let var_tys: HashMap<_, _> = var_set
            .into_iter()
            .map(|id| {
                let mut ty = self.var_ecrs.types[id];
                ty.subst(&vars, &fns);
                (*id, ty)
            })
            .collect();

        let fn_set: HashSet<_> = fns.values().collect();
        let fn_tys: HashMap<_, _> = fn_set
            .into_iter()
            .map(|id| {
                let mut ty = self.fn_ecrs.types[id].clone();
                ty.subst(&vars, &fns);
                (*id, ty)
            })
            .collect();

        AnalysisResults {
            vars,
            var_tys,
            fns,
            fn_tys,
        }
    }

    #[inline]
    fn get_id(&mut self) -> usize {
        let id = self.id;
        self.id += 1;
        id
    }

    fn mk_ecr(&mut self) -> Type {
        let id = self.get_id();

        let var_ty = VarId::Temp(id);
        let var_ecr = self.var_arena.alloc(DisjointSet::new(var_ty));
        self.var_ecrs.insert(var_ty, var_ecr);

        let fn_ty = FnId(id);
        let fn_ecr = self.fn_arena.alloc(DisjointSet::new(fn_ty));
        self.fn_ecrs.insert(fn_ty, fn_ecr);

        Type { var_ty, fn_ty }
    }

    fn x_eq_y(&mut self, x: VarId, y: VarId) {
        let (vt1, ft1) = self.variable_type(x);
        let (vt2, ft2) = self.variable_type(y);
        self.var_cond_join(vt1, vt2);
        self.fn_cond_join(ft1, ft2);
    }

    fn x_eq_ref_y(&mut self, x: VarId, y: VarId) {
        let (vt1, _) = self.variable_type(x);
        self.var_join(vt1, y);
    }

    fn x_eq_deref_y(&mut self, x: VarId, y: VarId) {
        let (vt1, ft1) = self.variable_type(x);
        let (vt2, _) = self.variable_type(y);
        match self.var_type(vt2) {
            VarType::Bot => {
                self.var_set_type(vt2, VarType::new(vt1, ft1));
            }
            VarType::Ref(Type {
                var_ty: vt3,
                fn_ty: ft3,
            }) => {
                self.var_cond_join(vt1, vt3);
                self.fn_cond_join(ft1, ft3);
            }
        }
    }

    fn deref_x_eq_y(&mut self, x: VarId, y: VarId) {
        let (vt1, _) = self.variable_type(x);
        let (vt2, ft2) = self.variable_type(y);
        match self.var_type(vt1) {
            VarType::Bot => {
                self.var_set_type(vt1, VarType::new(vt2, ft2));
            }
            VarType::Ref(Type {
                var_ty: vt3,
                fn_ty: ft3,
            }) => {
                self.var_cond_join(vt3, vt2);
                self.fn_cond_join(ft3, ft2);
            }
        }
    }

    fn deref_x_eq_deref_y(&mut self, x: VarId, y: VarId) {
        let z = VarId::Temp(self.get_id());
        self.insert_and_allocate(z);
        self.x_eq_deref_y(z, y);
        self.deref_x_eq_y(x, z);
    }

    fn x_eq_alloc(&mut self, x: VarId) {
        let (vt1, _) = self.variable_type(x);
        if self.var_type(vt1).is_bot() {
            self.allocate(vt1);
        }
    }

    #[inline]
    fn insert_and_allocate(&mut self, x: VarId) {
        self.var_ecrs
            .insert(x, self.var_arena.alloc(DisjointSet::new(x)));
        self.allocate(x);
    }

    #[inline]
    fn allocate(&mut self, x: VarId) {
        let ty = self.mk_ecr();
        self.var_set_type(x, VarType::Ref(ty));
    }

    fn x_eq_fn(&mut self, cstr: CallStr, x: VarId, func: LocalDefId, args: usize) {
        let args = (1..=args)
            .map(|i| {
                let (var_ty, fn_ty) = self.variable_type(VarId::Local(cstr, func, i as _));
                Type { var_ty, fn_ty }
            })
            .collect();
        let (var_ty, fn_ty) = self.variable_type(VarId::Local(cstr, func, 0));
        let ret = Type { var_ty, fn_ty };
        let t = FnType::Lambda(args, ret);

        let (_, ft1) = self.variable_type(x);
        self.fn_set_type(ft1, t);
    }

    #[inline]
    fn variable_type(&self, e: VarId) -> (VarId, FnId) {
        let VarType::Ref(Type { var_ty, fn_ty }) = self.var_type(e) else { panic!() };
        (var_ty, fn_ty)
    }

    #[inline]
    fn var_type(&self, e: VarId) -> VarType {
        self.var_ecrs.types[&self.var_ecrs.root(e)]
    }

    #[inline]
    fn fn_type(&self, e: FnId) -> &FnType {
        &self.fn_ecrs.types[&self.fn_ecrs.root(e)]
    }

    #[inline]
    fn var_set_type(&mut self, e: VarId, t: VarType) {
        self.var_ecrs.set_type(e, t, &mut self.fn_ecrs);
    }

    #[inline]
    fn fn_set_type(&mut self, e: FnId, t: FnType) {
        self.fn_ecrs.set_type(e, t, &mut self.var_ecrs);
    }

    #[inline]
    fn var_cond_join(&mut self, e1: VarId, e2: VarId) {
        self.var_ecrs.cond_join(e1, e2, &mut self.fn_ecrs);
    }

    #[inline]
    fn fn_cond_join(&mut self, e1: FnId, e2: FnId) {
        self.fn_ecrs.cond_join(e1, e2, &mut self.var_ecrs);
    }

    #[inline]
    fn var_join(&mut self, e1: VarId, e2: VarId) {
        self.var_ecrs.join(e1, e2, &mut self.fn_ecrs);
    }
}

lazy_static! {
    static ref NO_OP_C_FNS: HashSet<&'static str> = [
        "memcmp",
        "wmemcmp",
        "strcmp",
        "wcscmp",
        "strcasecmp",
        "wcscasecmp",
        "strncmp",
        "wcsncmp",
        "strncasecmp",
        "wcsncasecmp",
        "strverscmp",
        "bcmp",
        "strtol",
        "wcstol",
        "strtoul",
        "wcstoul",
        "strtoll",
        "wcstoll",
        "strtoq",
        "wcstoq",
        "strtoull",
        "wcstoull",
        "strtouq",
        "wcstouq",
        "strtoimax",
        "wcstoimax",
        "strtoumax",
        "wcstoumax",
        "fputs",
        "fopen",
        "fwrite",
        "__xstat",
        "__assert_fail",
    ]
    .into_iter()
    .collect();
    static ref RET_0_C_FNS: HashSet<&'static str> = [
        "memset",
        "wmemset",
        "memchr",
        "wmemchr",
        "rawmemchr",
        "memrchr",
        "strchr",
        "wcschr",
        "strchrnul",
        "wcschrnul",
        "strrchr",
        "wcsrchr",
        "strstr",
        "wcsstr",
        "wcswcs",
        "strcasestr",
        "memmem",
        "strpbrk",
        "wcspbrk",
        "index",
        "rindex",
        "strtok",
        "wcstok",
        "strtok_r",
        "basename",
        "dirname",
    ]
    .into_iter()
    .collect();
    static ref ALLOC_C_FNS: HashSet<&'static str> = [
        "dcgettext",
        "strdup",
        "wcsdup",
        "strdupa",
        "strndup",
        "strndupa",
        "getenv",
        "signal",
    ]
    .into_iter()
    .collect();
    static ref COPY_C_FNS: HashSet<&'static str> = [
        "memcpy", "wmemcpy", "mempcpy", "wmempcpy", "memmove", "wmemmove", "memccpy", "strcpy",
        "wcscpy", "stpcpy", "wcpcpy", "strncpy", "wcsncpy", "stpncpy", "wcpncpy", "strncat",
        "wcsncat", "strlcpy", "wcslcpy", "strlcat", "wcslcat", "strcat", "wcscat"
    ]
    .into_iter()
    .collect();
}

#[cfg(test)]
mod tests;
