use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use etrace::some_or;
use rustc_middle::mir::Local;

use super::*;

#[derive(Debug, Clone)]
pub enum AbsMem {
    Bot,
    Mem(Graph),
}

impl AbsMem {
    #[inline]
    pub fn top() -> Self {
        Self::Mem(Graph::default())
    }

    #[inline]
    pub fn bot() -> Self {
        Self::Bot
    }

    #[inline]
    pub fn g(&self) -> &Graph {
        match self {
            Self::Bot => panic!(),
            Self::Mem(g) => g,
        }
    }

    #[inline]
    pub fn gm(&mut self) -> &mut Graph {
        match self {
            Self::Bot => panic!(),
            Self::Mem(g) => g,
        }
    }

    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        let Self::Mem(g1) = self else { return other.clone() };
        let Self::Mem(g2) = other else { return self.clone() };
        Self::Mem(g1.join(g2))
    }

    #[inline]
    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bot, _) => true,
            (_, Self::Bot) => false,
            (Self::Mem(g1), Self::Mem(g2)) => g1.ord(g2),
        }
    }
}

type NodeId = usize;

#[derive(Clone, PartialEq, Eq)]
pub struct AbsLoc {
    root: NodeId,
    projection: Vec<AccElem>,
}

impl std::fmt::Debug for AbsLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.root)?;
        if !self.projection.is_empty() {
            for elem in self.projection.iter() {
                write!(f, ".{:?}", elem)?;
            }
        }
        Ok(())
    }
}

impl AbsLoc {
    #[inline]
    pub fn new(root: NodeId, projection: Vec<AccElem>) -> Self {
        Self { root, projection }
    }

    #[inline]
    pub fn new_root(root: NodeId) -> Self {
        Self {
            root,
            projection: vec![],
        }
    }

    #[inline]
    pub fn root(&self) -> NodeId {
        self.root
    }

    #[inline]
    pub fn projection(&self) -> &[AccElem] {
        &self.projection
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Obj {
    Ptr(AbsLoc),
    Compound(HashMap<usize, Obj>),
    Index(HashMap<BTreeSet<Local>, Obj>),
}

impl std::fmt::Debug for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ptr(l) => write!(f, "{:?}", l),
            Self::Compound(fs) => {
                write!(f, "[")?;
                let mut v = fs.keys().copied().collect::<Vec<_>>();
                v.sort();
                for (i, k) in v.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {:?}", k, fs[k])?;
                }
                write!(f, "]")
            }
            Self::Index(fs) => {
                write!(f, "[")?;
                let mut v = fs.keys().cloned().collect::<Vec<_>>();
                v.sort();
                for (i, k) in v.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}: {:?}", k, fs[k])?;
                }
                write!(f, "]")
            }
        }
    }
}

impl Default for Obj {
    #[inline]
    fn default() -> Self {
        Obj::Compound(HashMap::new())
    }
}

impl Obj {
    fn project<'a>(&'a self, proj: &[AccElem]) -> Option<&'a Obj> {
        if let Some(elem) = proj.get(0) {
            let inner = match elem {
                AccElem::Int(n) => {
                    let Obj::Compound(fields) = self else { return None };
                    fields.get(n)?
                }
                AccElem::Symbolic(local1) => {
                    let Obj::Index(fields) = self else { return None };
                    fields.iter().find_map(|(local2, obj)| {
                        if local1.is_disjoint(local2) {
                            None
                        } else {
                            Some(obj)
                        }
                    })?
                }
            };
            inner.project(&proj[1..])
        } else {
            Some(self)
        }
    }

    fn project_mut<'a>(&'a mut self, proj: &[AccElem], write: bool) -> &'a mut Obj {
        if let Some(elem) = proj.get(0) {
            let inner = match elem {
                AccElem::Int(n) => {
                    if !matches!(self, Obj::Compound(_)) {
                        *self = Obj::default();
                    }
                    let Obj::Compound(fields) = self else { unreachable!() };
                    fields.entry(*n).or_insert(Obj::default())
                }
                AccElem::Symbolic(local1) => {
                    if !matches!(self, Obj::Index(_)) {
                        *self =
                            Obj::Index([(local1.clone(), Obj::default())].into_iter().collect());
                    }
                    let Obj::Index(fields) = self else { unreachable!() };
                    match fields.keys().find(|local2| !local1.is_disjoint(local2)) {
                        Some(local2) => {
                            let mut local2 = local2.clone();
                            let obj = fields.remove(&local2).unwrap();
                            local2.extend(local1);
                            if write {
                                fields.clear();
                            }
                            fields.insert(local2.clone(), obj);
                            fields.get_mut(&local2).unwrap()
                        }
                        None => {
                            if write {
                                fields.clear();
                            }
                            fields.insert(local1.clone(), Obj::default());
                            fields.get_mut(local1).unwrap()
                        }
                    }
                }
            };
            inner.project_mut(&proj[1..], write)
        } else {
            self
        }
    }

    fn substitute(&mut self, old_id: NodeId, new_id: NodeId) {
        match self {
            Obj::Ptr(loc) => {
                if loc.root == old_id {
                    assert!(loc.projection.is_empty());
                    loc.root = new_id;
                }
            }
            Obj::Compound(fs) => {
                for obj in fs.values_mut() {
                    obj.substitute(old_id, new_id);
                }
            }
            Obj::Index(fs) => {
                for obj in fs.values_mut() {
                    obj.substitute(old_id, new_id);
                }
            }
        }
    }

    fn extend_loc(&mut self, loc: &AbsLoc) {
        match self {
            Obj::Ptr(curr_loc) => {
                if curr_loc == loc {
                    curr_loc.projection.push(AccElem::Int(0));
                }
            }
            Obj::Compound(fs) => {
                for obj in fs.values_mut() {
                    obj.extend_loc(loc);
                }
            }
            Obj::Index(fs) => {
                for obj in fs.values_mut() {
                    obj.extend_loc(loc);
                }
            }
        }
    }

    fn invalidate_symbolic(&mut self, local: Local) {
        match self {
            Self::Ptr(_) => {}
            Self::Compound(fs) => {
                for obj in fs.values_mut() {
                    obj.invalidate_symbolic(local);
                }
            }
            Self::Index(fs) => {
                while let Some(ls) = fs.keys().find(|ls| ls.contains(&local)) {
                    let mut ls = ls.clone();
                    let obj = fs.remove(&ls).unwrap();
                    ls.remove(&local);
                    if !ls.is_empty() {
                        fs.insert(ls, obj);
                    }
                }
                for obj in fs.values_mut() {
                    obj.invalidate_symbolic(local);
                }
            }
        }
    }

    fn pointing_locations(&self) -> Vec<AbsLoc> {
        match self {
            Self::Ptr(loc) => vec![loc.clone()],
            Self::Compound(fs) => fs
                .values()
                .flat_map(|obj| obj.pointing_locations())
                .collect(),
            Self::Index(fs) => fs
                .values()
                .flat_map(|obj| obj.pointing_locations())
                .collect(),
        }
    }

    pub fn as_ptr(&self) -> &AbsLoc {
        let Obj::Ptr(loc) = self else { panic!() };
        loc
    }

    pub fn field(&self, i: usize) -> &Obj {
        let Obj::Compound(fs) = self else { panic!() };
        fs.get(&i).unwrap()
    }

    pub fn symbolic_obj(&self, index: &[usize]) -> Option<&Obj> {
        let Obj::Index(fs) = self else { panic!() };
        let index = index.iter().copied().map(Local::from_usize).collect();
        fs.get(&index)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Node {
    pub obj: Obj,
    pub at_addr: Option<u128>,
}

impl std::fmt::Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(addr) = self.at_addr {
            write!(f, "{:?}@{:?}", self.obj, addr)
        } else {
            write!(f, "{:?}", self.obj)
        }
    }
}

impl Node {
    #[inline]
    fn new() -> Self {
        Node {
            obj: Obj::default(),
            at_addr: None,
        }
    }

    pub fn as_ptr(&self) -> &AbsLoc {
        self.obj.as_ptr()
    }

    pub fn field(&self, i: usize) -> &Obj {
        self.obj.field(i)
    }

    pub fn symbolic(&self, index: &[usize]) -> Option<&Obj> {
        self.obj.symbolic_obj(index)
    }
}

#[derive(Clone, Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
    locals: HashMap<Local, NodeId>,
    ints: HashMap<u128, NodeId>,
}

impl std::fmt::Debug for Graph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nodes: BTreeMap<_, _> = self.nodes.iter().enumerate().map(|(i, n)| (i, n)).collect();
        let locals: BTreeMap<_, _> = self.locals.iter().map(|(l, n)| (*l, *n)).collect();
        f.debug_struct("Graph")
            .field("nodes", &nodes)
            .field("locals", &locals)
            .finish()
    }
}

impl Graph {
    fn join(&self, other: &Self) -> Self {
        let mut joined = Graph::default();
        let mut id_map = HashMap::new();
        let mut remaining = vec![];

        for (l1, id1) in &self.locals {
            let (_, id2) = some_or!(other.locals.iter().find(|(l2, _)| l1 == *l2), continue);
            let (id, _) = joined.get_local_node_mut(*l1);
            let idp = (*id1, *id2);
            id_map.insert(idp, id);
            remaining.push(idp);
        }

        while let Some((id1, id2)) = remaining.pop() {
            let node1 = &self.nodes[id1];
            let node2 = &other.nodes[id2];
            let id = id_map[&(id1, id2)];

            if let (Some(i1), Some(i2)) = (node1.at_addr, node2.at_addr) {
                if i1 == i2 {
                    joined.nodes[id].at_addr = Some(i1);
                    joined.ints.insert(i1, id);
                }
            }

            let mut obj = Obj::default();
            join_objs(
                &node1.obj,
                &node2.obj,
                &mut obj,
                &mut joined,
                &mut id_map,
                &mut remaining,
            );
            joined.nodes[id].obj = obj;
        }

        joined
    }

    fn ord(&self, other: &Self) -> bool {
        let mut id_set = HashSet::new();
        let mut remaining = vec![];

        for (l2, id2) in &other.locals {
            let (_, id1) = some_or!(self.locals.iter().find(|(l1, _)| *l1 == l2), return false);
            let idp = (*id1, *id2);
            id_set.insert(idp);
            remaining.push(idp);
        }

        while let Some((id1, id2)) = remaining.pop() {
            let node1 = &self.nodes[id1];
            let node2 = &other.nodes[id2];

            match (node1.at_addr, node2.at_addr) {
                (None, Some(_)) => return false,
                (Some(i1), Some(i2)) if i1 != i2 => return false,
                _ => {}
            }

            if !ord_objs(&node1.obj, &node2.obj, &mut id_set, &mut remaining) {
                return false;
            }
        }

        true
    }

    fn add_node(&mut self) -> (NodeId, &mut Node) {
        let id = self.nodes.len();
        self.nodes.push(Node::new());
        (id, &mut self.nodes[id])
    }

    fn get_int_node(&mut self, n: u128) -> NodeId {
        if let Some(id) = self.ints.get(&n) {
            *id
        } else {
            let id = self.nodes.len();
            let mut node = Node::new();
            node.at_addr = Some(n);
            self.nodes.push(node);
            self.ints.insert(n, id);
            id
        }
    }

    fn get_local_node_mut(&mut self, l: Local) -> (NodeId, &mut Node) {
        let id = if let Some(id) = self.locals.get(&l) {
            *id
        } else {
            let (id, _) = self.add_node();
            self.locals.insert(l, id);
            id
        };
        (id, &mut self.nodes[id])
    }

    pub fn assign(&mut self, l: &AccPath, l_deref: bool, r: &OpVal) {
        match r {
            OpVal::Place(r, r_deref) => self.x_eq_y(l, l_deref, r, *r_deref),
            OpVal::Int(n) => self.x_eq_int(l, l_deref, *n),
            OpVal::Other => self.x_eq(l, l_deref),
        }
    }

    pub fn assign_with_suffixes(
        &mut self,
        l: &AccPath,
        l_deref: bool,
        r: &OpVal,
        suffixes: &[Vec<AccElem>],
    ) {
        for suffix in suffixes {
            let l = l.extended(suffix);
            let r = r.extended(suffix);
            self.assign(&l, l_deref, &r);
        }
    }

    pub fn get_obj(&self, x: &AccPath, deref: bool) -> Option<&Obj> {
        if deref {
            let id = self.locals.get(&x.local)?;
            let mut loc = self.get_pointed_loc(*id, &[])?;
            loc.projection.extend(x.projection.to_owned());
            let node = &self.nodes[loc.root];
            node.obj.project(&loc.projection)
        } else {
            let id = self.locals.get(&x.local)?;
            let node = &self.nodes[*id];
            node.obj.project(&x.projection)
        }
    }

    fn lvalue(&mut self, x: &AccPath, deref: bool) -> &mut Obj {
        if deref {
            let (id, _) = self.get_local_node_mut(x.local);
            let mut loc = self.get_pointed_loc_mut(id, &[], true);
            loc.projection.extend(x.projection.to_owned());
            let node = &mut self.nodes[loc.root];
            node.obj.project_mut(&loc.projection, true)
        } else {
            let (_, node) = self.get_local_node_mut(x.local);
            node.obj.project_mut(&x.projection, true)
        }
    }

    fn rvalue(&mut self, x: &AccPath, deref: bool) -> AbsLoc {
        let (id, _) = self.get_local_node_mut(x.local);
        if deref {
            let mut loc = self.get_pointed_loc_mut(id, &[], false);
            loc.projection.extend(x.projection.to_owned());
            self.get_pointed_loc_mut(loc.root, &loc.projection, false)
        } else {
            self.get_pointed_loc_mut(id, &x.projection, false)
        }
    }

    fn x_eq_y(&mut self, x: &AccPath, x_deref: bool, y: &AccPath, y_deref: bool) {
        let loc = self.rvalue(y, y_deref);
        let obj = self.lvalue(x, x_deref);
        *obj = Obj::Ptr(loc);
    }

    fn x_eq_int(&mut self, x: &AccPath, deref: bool, n: u128) {
        let id = self.get_int_node(n);
        let obj = self.lvalue(x, deref);
        *obj = Obj::Ptr(AbsLoc::new(id, vec![]));
    }

    pub fn x_eq(&mut self, x: &AccPath, deref: bool) {
        let obj = self.lvalue(x, deref);
        *obj = Obj::default();
    }

    pub fn x_eq_ref_y(&mut self, x: &AccPath, y: &AccPath, y_deref: bool) {
        let (id, _) = self.get_local_node_mut(y.local);
        let loc = if y_deref {
            let mut loc = self.get_pointed_loc_mut(id, &[], false);
            loc.projection.extend(y.projection.to_owned());
            loc
        } else {
            AbsLoc::new(id, y.projection.to_owned())
        };

        let obj = self.lvalue(x, false);
        *obj = Obj::Ptr(loc);
    }

    pub fn x_eq_offset(&mut self, x: &AccPath, y: &AccPath, idx: OpVal) {
        let (id, _) = self.get_local_node_mut(y.local);
        let loc = self.get_pointed_loc_mut(id, &[], false);
        let mut loc = if loc.projection.is_empty() {
            let Obj::Ptr(loc) = &self.nodes[id].obj else { panic!() };
            let mut loc = loc.clone();
            self.extend_loc(&loc);
            loc.projection.push(AccElem::Int(0));
            self.obj_at_location_mut(&loc, false);
            loc
        } else {
            loc
        };
        let elem = loc.projection.last_mut().unwrap();
        if let AccElem::Int(n) = elem {
            match idx {
                OpVal::Place(idx, idx_deref) => {
                    assert!(idx.projection.is_empty());
                    assert!(!idx_deref);
                    *elem = AccElem::Symbolic(self.find_aliases(idx.local));
                    let obj = self.lvalue(x, false);
                    *obj = Obj::Ptr(loc);
                }
                OpVal::Int(idx) => {
                    *n += idx as usize;
                    let obj = self.lvalue(x, false);
                    *obj = Obj::Ptr(loc);
                }
                OpVal::Other => {
                    let obj = self.lvalue(x, false);
                    *obj = Obj::default();
                }
            }
        } else {
            let obj = self.lvalue(x, false);
            *obj = Obj::default();
        }
    }

    pub fn x_eq_offset_int(&mut self, x: &AccPath, y: &AccPath, idx: u128) {
        let (id, _) = self.get_local_node_mut(y.local);
        let mut loc = self.get_pointed_loc_mut(id, &[], false);
        let obj = self.lvalue(x, false);
        let elem = loc.projection.last_mut().unwrap();
        if let AccElem::Int(n) = elem {
            *n += idx as usize;
            *obj = Obj::Ptr(loc);
        } else {
            *obj = Obj::default();
        }
    }

    pub fn filter_x_int(&mut self, x: &AccPath, deref: bool, n: u128) {
        let ptr = self.set_obj_ptr(|this| this.lvalue(x, deref));
        assert!(ptr.projection.is_empty());
        let id = ptr.root;
        if let Some(n_id) = self.ints.get(&n) {
            let n_id = *n_id;
            self.substitute(id, n_id);
        } else {
            self.nodes[id].at_addr = Some(n);
            self.ints.insert(n, id);
        }
    }

    fn substitute(&mut self, old_id: NodeId, new_id: NodeId) {
        for node in &mut self.nodes {
            node.obj.substitute(old_id, new_id);
        }
    }

    fn extend_loc(&mut self, loc: &AbsLoc) {
        for node in &mut self.nodes {
            node.obj.extend_loc(loc);
        }
    }

    pub fn find_aliases(&self, local: Local) -> BTreeSet<Local> {
        let mut aliases = BTreeSet::new();
        aliases.insert(local);
        let loc1 = some_or!(self.loc_pointed_by_local(local), return aliases);
        for l in self.locals.keys() {
            let loc2 = some_or!(self.loc_pointed_by_local(*l), continue);
            if loc1 == loc2 {
                aliases.insert(*l);
            }
        }
        aliases
    }

    fn loc_pointed_by_local(&self, local: Local) -> Option<&AbsLoc> {
        let id = self.locals.get(&local)?;
        let node = &self.nodes[*id];
        if let Obj::Ptr(loc) = &node.obj {
            Some(loc)
        } else {
            None
        }
    }

    pub fn get_local_as_int(&self, x: usize) -> Option<u128> {
        self.get_x_as_int(&AccPath::new(Local::from_usize(x), vec![]))
    }

    pub fn get_x_as_int(&self, x: &AccPath) -> Option<u128> {
        let id = self.locals.get(&x.local)?;
        let loc = self.get_pointed_loc(*id, &x.projection)?;
        if loc.projection.is_empty() {
            self.nodes[loc.root].at_addr
        } else {
            None
        }
    }

    pub fn get_deref_x_as_int(&self, x: &AccPath) -> Option<u128> {
        let id = self.locals.get(&x.local)?;
        let mut loc = self.get_pointed_loc(*id, &[])?;
        loc.projection.extend(x.projection.to_owned());
        let loc = self.get_pointed_loc(loc.root, &loc.projection)?;
        if loc.projection.is_empty() {
            self.nodes[loc.root].at_addr
        } else {
            None
        }
    }

    pub fn invalidate_symbolic(&mut self, local: Local) {
        for node in &mut self.nodes {
            node.obj.invalidate_symbolic(local);
        }
    }

    fn get_pointed_loc(&self, node_id: NodeId, proj: &[AccElem]) -> Option<AbsLoc> {
        let obj = self.nodes[node_id].obj.project(proj)?;
        let Obj::Ptr(loc) = obj else { return None };
        Some(loc.clone())
    }

    fn get_pointed_loc_mut(&mut self, node_id: NodeId, proj: &[AccElem], write: bool) -> AbsLoc {
        self.set_obj_ptr(|this| this.nodes[node_id].obj.project_mut(proj, write))
    }

    #[inline]
    fn set_obj_ptr<F: Fn(&mut Self) -> &mut Obj>(&mut self, f: F) -> AbsLoc {
        let next_id = self.nodes.len();
        let obj = f(self);
        let loc = if let Obj::Ptr(loc) = obj {
            loc.clone()
        } else {
            let loc = AbsLoc::new(next_id, vec![]);
            *obj = Obj::Ptr(loc.clone());
            loc
        };
        if loc.root == next_id {
            self.nodes.push(Node::new());
        }
        loc
    }

    pub fn deref_local_id(&self, local: Local) -> Option<usize> {
        let id = self.locals.get(&local)?;
        let loc = self.get_pointed_loc(*id, &[])?;
        Some(loc.root)
    }

    fn obj_at_location(&self, loc: &AbsLoc) -> Option<&Obj> {
        self.nodes[loc.root].obj.project(&loc.projection)
    }

    fn obj_at_location_mut(&mut self, loc: &AbsLoc, write: bool) -> &mut Obj {
        self.nodes[loc.root].obj.project_mut(&loc.projection, write)
    }

    pub fn invalidate_deref(&mut self, local: Local, mut depth: usize, opt_id: Option<usize>) {
        let id = *some_or!(self.locals.get(&local), return);
        let mut locs = vec![AbsLoc::new(id, vec![])];
        while !locs.is_empty() {
            if depth == 0 {
                for l in locs {
                    if let Some(id) = opt_id {
                        if id == l.root {
                            continue;
                        }
                    }
                    let obj = self.obj_at_location_mut(&l, false);
                    *obj = Obj::default();
                }
                return;
            }
            locs = locs
                .into_iter()
                .flat_map(|loc| {
                    let obj = some_or!(self.obj_at_location(&loc), return vec![]);
                    obj.pointing_locations()
                })
                .collect();
            depth -= 1;
        }
    }

    pub fn get_local_id(&self, local: usize) -> usize {
        *self.locals.get(&Local::from_usize(local)).unwrap()
    }

    pub fn get_local_node(&self, local: usize) -> &Node {
        &self.nodes[self.get_local_id(local)]
    }
}

fn join_objs(
    obj1: &Obj,
    obj2: &Obj,
    obj: &mut Obj,
    joined: &mut Graph,
    id_map: &mut HashMap<(NodeId, NodeId), NodeId>,
    remaining: &mut Vec<(NodeId, NodeId)>,
) {
    match (obj1, obj2) {
        (Obj::Ptr(l1), Obj::Ptr(l2)) => {
            if let Some(l) = cmp_projection(&l1.projection, &l2.projection) {
                let idp = (l1.root, l2.root);
                let nid = if let Some(id) = id_map.get(&idp) {
                    *id
                } else {
                    let (id, _) = joined.add_node();
                    id_map.insert(idp, id);
                    remaining.push(idp);
                    id
                };
                *obj = Obj::Ptr(AbsLoc::new(nid, l));
            }
        }
        (Obj::Compound(fs1), Obj::Compound(fs2)) => {
            let Obj::Compound(fs) = obj else { unreachable!() };
            for (f, obj1) in fs1 {
                let obj2 = some_or!(fs2.get(f), continue);
                let mut nobj = Obj::default();
                join_objs(obj1, obj2, &mut nobj, joined, id_map, remaining);
                fs.insert(*f, nobj);
            }
        }
        (Obj::Index(fs1), Obj::Index(fs2)) => {
            let mut fs = HashMap::new();
            for (l1, obj1) in fs1 {
                for (l2, obj2) in fs2 {
                    let l: BTreeSet<_> = l1.intersection(l2).copied().collect();
                    if !l.is_empty() {
                        let mut nobj = Obj::default();
                        join_objs(obj1, obj2, &mut nobj, joined, id_map, remaining);
                        fs.insert(l, nobj);
                    }
                }
            }
            *obj = Obj::Index(fs);
        }
        _ => {}
    }
}

fn cmp_projection(proj1: &[AccElem], proj2: &[AccElem]) -> Option<Vec<AccElem>> {
    if proj1.len() != proj2.len() {
        return None;
    }
    let mut proj = vec![];
    for e in proj1.iter().zip(proj2) {
        match e {
            (AccElem::Int(i1), AccElem::Int(i2)) if i1 == i2 => {
                proj.push(AccElem::Int(*i1));
            }
            (AccElem::Symbolic(l1), AccElem::Symbolic(l2)) => {
                let l: BTreeSet<_> = l1.intersection(l2).copied().collect();
                if l.is_empty() {
                    return None;
                }
                proj.push(AccElem::Symbolic(l));
            }
            _ => return None,
        }
    }
    Some(proj)
}

fn ord_objs(
    obj1: &Obj,
    obj2: &Obj,
    id_set: &mut HashSet<(NodeId, NodeId)>,
    remaining: &mut Vec<(NodeId, NodeId)>,
) -> bool {
    match (obj1, obj2) {
        (Obj::Ptr(l1), Obj::Ptr(l2)) => {
            let idp = (l1.root, l2.root);
            if !id_set.contains(&idp) {
                id_set.insert(idp);
                remaining.push(idp);
            }
            ord_projection(&l1.projection, &l2.projection)
        }
        (Obj::Compound(fs1), Obj::Compound(fs2)) => fs2.iter().all(|(f, obj2)| {
            let obj1 = some_or!(fs1.get(f), return false);
            ord_objs(obj1, obj2, id_set, remaining)
        }),
        (Obj::Index(fs1), Obj::Index(fs2)) => fs2.iter().all(|(l2, obj2)| {
            let obj1 = fs1
                .iter()
                .find_map(|(l1, obj1)| if l2.is_subset(l1) { Some(obj1) } else { None });
            let obj1 = some_or!(obj1, return false);
            ord_objs(obj1, obj2, id_set, remaining)
        }),
        _ => false,
    }
}

fn ord_projection(proj1: &[AccElem], proj2: &[AccElem]) -> bool {
    if proj1.len() != proj2.len() {
        return false;
    }
    proj1.iter().zip(proj2).all(|e| match e {
        (AccElem::Int(i1), AccElem::Int(i2)) => i1 == i2,
        (AccElem::Symbolic(l1), AccElem::Symbolic(l2)) => l2.is_subset(l1),
        _ => false,
    })
}
