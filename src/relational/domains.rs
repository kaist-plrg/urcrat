use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use etrace::some_or;
use rustc_index::bit_set::BitSet;
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

    pub fn size(&self) -> (usize, usize) {
        match self {
            Self::Bot => (0, 0),
            Self::Mem(g) => (g.locals.len(), g.nodes.len()),
        }
    }

    pub fn clear_dead_locals(&mut self, dead_locals: &BitSet<Local>) {
        if let Self::Mem(g) = self {
            g.clear_dead_locals(dead_locals);
        }
    }
}

type NodeId = usize;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AccElem {
    Int(u128),
    Symbolic(BTreeSet<Local>),
}

impl std::fmt::Debug for AccElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccElem::Int(i) => write!(f, "{}", i),
            AccElem::Symbolic(s) => write!(f, "{:?}", s),
        }
    }
}

impl AccElem {
    fn equiv(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(n1), Self::Int(n2)) => n1 == n2,
            (Self::Symbolic(l1), Self::Symbolic(l2)) => !l1.is_disjoint(l2),
            _ => false,
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Int(n1), Self::Int(n2)) if n1 == n2 => Self::Int(*n1),
            (Self::Symbolic(l1), Self::Symbolic(l2)) => {
                Self::Symbolic(l1.intersection(l2).cloned().collect())
            }
            _ => Self::Symbolic(BTreeSet::new()),
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(n1), Self::Int(n2)) => n1 == n2,
            (Self::Symbolic(l1), Self::Symbolic(l2)) => l2.is_subset(l1),
            _ => false,
        }
    }

    fn locals(&self) -> HashSet<Local> {
        match self {
            Self::Int(_) => HashSet::new(),
            Self::Symbolic(l) => l.iter().cloned().collect(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
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
    AtAddr(u128),
    Ptr(AbsLoc),
    Compound(HashMap<AccElem, Obj>),
}

impl std::fmt::Debug for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AtAddr(n) => write!(f, "@{}", n),
            Self::Ptr(l) => write!(f, "{:?}", l),
            Self::Compound(fs) => {
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
            let Obj::Compound(fields) = self else { return None };
            let inner = match elem {
                AccElem::Int(n) => fields.get(&AccElem::Int(*n))?,
                AccElem::Symbolic(_) => {
                    fields.iter().find_map(
                        |(field, obj)| {
                            if field.equiv(elem) {
                                Some(obj)
                            } else {
                                None
                            }
                        },
                    )?
                }
            };
            inner.project(&proj[1..])
        } else {
            Some(self)
        }
    }

    fn project_mut<'a>(&'a mut self, proj: &[AccElem], write: bool) -> &'a mut Obj {
        if let Some(elem) = proj.get(0) {
            let fields = match self {
                Obj::Compound(field) => std::mem::take(field),
                _ => HashMap::new(),
            };
            let mut new_fields = HashMap::new();
            let mut exists = false;
            let mut elem = elem.clone();
            for (field, obj) in fields {
                match (&field, &mut elem) {
                    (AccElem::Int(n1), AccElem::Int(n2)) => {
                        if n1 == n2 {
                            exists = true;
                        }
                        new_fields.insert(field, obj);
                    }
                    (AccElem::Symbolic(l1), AccElem::Symbolic(l2)) if !l1.is_disjoint(l2) => {
                        exists = true;
                        l2.extend(l1);
                        new_fields.insert(elem.clone(), obj);
                    }
                    _ => {
                        if !write {
                            new_fields.insert(field, obj);
                        }
                    }
                }
            }
            if !exists {
                new_fields.insert(elem.clone(), Obj::default());
            }
            *self = Obj::Compound(new_fields);
            let Obj::Compound(fields) = self else { unreachable!() };
            let inner = fields.get_mut(&elem).unwrap();
            inner.project_mut(&proj[1..], write)
        } else {
            self
        }
    }

    fn substitute(&mut self, old_loc: &AbsLoc, new_loc: &AbsLoc) {
        match self {
            Self::AtAddr(_) => {}
            Self::Ptr(loc) => {
                if loc == old_loc {
                    *loc = new_loc.clone();
                }
            }
            Self::Compound(fs) => {
                for obj in fs.values_mut() {
                    obj.substitute(old_loc, new_loc);
                }
            }
        }
    }

    fn extend_loc(&mut self, loc: &AbsLoc) {
        match self {
            Self::AtAddr(_) => {}
            Self::Ptr(curr_loc) => {
                if curr_loc == loc {
                    curr_loc.projection.push(AccElem::Int(0));
                }
            }
            Self::Compound(fs) => {
                for obj in fs.values_mut() {
                    obj.extend_loc(loc);
                }
            }
        }
    }

    fn invalidate_symbolic(&mut self, local: Local) {
        match self {
            Self::AtAddr(_) => {}
            Self::Ptr(_) => {}
            Self::Compound(fs) => {
                while let Some(f) = fs.keys().find(|f| {
                    let AccElem::Symbolic(ls) = f else { return false };
                    ls.contains(&local)
                }) {
                    let f = f.clone();
                    let obj = fs.remove(&f).unwrap();
                    let AccElem::Symbolic(mut ls) = f else { unreachable!() };
                    ls.remove(&local);
                    if !ls.is_empty() {
                        fs.insert(AccElem::Symbolic(ls), obj);
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
            Self::AtAddr(_) => vec![],
            Self::Ptr(loc) => vec![loc.clone()],
            Self::Compound(fs) => fs
                .values()
                .flat_map(|obj| obj.pointing_locations())
                .collect(),
        }
    }

    fn locals(&self) -> HashSet<Local> {
        match self {
            Self::AtAddr(_) => HashSet::new(),
            Self::Ptr(loc) => loc
                .projection
                .iter()
                .flat_map(|elem| elem.locals())
                .collect(),
            Self::Compound(fs) => fs
                .iter()
                .flat_map(|(f, obj)| {
                    let mut ls = f.locals();
                    ls.extend(obj.locals());
                    ls
                })
                .collect(),
        }
    }

    pub fn as_ptr(&self) -> &AbsLoc {
        let Obj::Ptr(loc) = self else { panic!() };
        loc
    }

    pub fn field(&self, i: u128) -> &Obj {
        let Obj::Compound(fs) = self else { panic!() };
        fs.get(&AccElem::Int(i)).unwrap()
    }

    pub fn symbolic(&self, index: &[usize]) -> Option<&Obj> {
        let Obj::Compound(fs) = self else { panic!() };
        let index = index.iter().copied().map(Local::from_usize).collect();
        fs.get(&AccElem::Symbolic(index))
    }
}

#[derive(Clone, PartialEq, Eq, Default)]
#[repr(transparent)]
pub struct Node {
    pub obj: Obj,
}

impl std::fmt::Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.obj)
    }
}

impl std::ops::Deref for Node {
    type Target = Obj;

    fn deref(&self) -> &Self::Target {
        &self.obj
    }
}

impl std::ops::DerefMut for Node {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.obj
    }
}

impl Node {
    #[inline]
    fn new(obj: Obj) -> Self {
        Self { obj }
    }
}

#[derive(Clone, Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
    locals: HashMap<Local, NodeId>,
    ints: HashMap<u128, AbsLoc>,
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
            let idp = (AbsLoc::new_root(*id1), AbsLoc::new_root(*id2));
            id_map.insert(idp.clone(), id);
            remaining.push(idp);
        }

        while let Some((loc1, loc2)) = remaining.pop() {
            let obj1 = self.obj_at_location(&loc1);
            let obj2 = other.obj_at_location(&loc2);
            let id = id_map[&(loc1, loc2)];

            let mut obj = Obj::default();
            if let (Some(obj1), Some(obj2)) = (obj1, obj2) {
                join_objs(
                    obj1,
                    obj2,
                    &mut obj,
                    &mut joined,
                    &mut id_map,
                    &mut remaining,
                    AbsLoc::new_root(id),
                );
            }
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

            if !ord_objs(node1, node2, &mut id_set, &mut remaining) {
                return false;
            }
        }

        true
    }

    fn add_node(&mut self) -> (NodeId, &mut Node) {
        let id = self.nodes.len();
        self.nodes.push(Node::default());
        (id, &mut self.nodes[id])
    }

    fn get_int_node(&mut self, n: u128) -> AbsLoc {
        if let Some(id) = self.ints.get(&n) {
            id.clone()
        } else {
            let id = self.nodes.len();
            let node = Node::new(Obj::AtAddr(n));
            self.nodes.push(node);
            let loc = AbsLoc::new_root(id);
            self.ints.insert(n, loc.clone());
            loc
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
            node.project(&loc.projection)
        } else {
            let id = self.locals.get(&x.local)?;
            let node = &self.nodes[*id];
            node.project(&x.projection)
        }
    }

    fn lvalue(&mut self, x: &AccPath, deref: bool) -> &mut Obj {
        if deref {
            let (id, _) = self.get_local_node_mut(x.local);
            let mut loc = self.get_pointed_loc_mut(id, &[], true);
            loc.projection.extend(x.projection.to_owned());
            let node = &mut self.nodes[loc.root];
            node.project_mut(&loc.projection, true)
        } else {
            let (_, node) = self.get_local_node_mut(x.local);
            node.project_mut(&x.projection, true)
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
        let loc = self.get_int_node(n);
        let obj = self.lvalue(x, deref);
        *obj = Obj::Ptr(loc);
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
                    *n += idx;
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
            *n += idx;
            *obj = Obj::Ptr(loc);
        } else {
            *obj = Obj::default();
        }
    }

    pub fn filter_x_int(&mut self, x: &AccPath, deref: bool, n: u128) {
        let ptr_loc = self.set_obj_ptr(|this| this.lvalue(x, deref));
        if let Some(n_loc) = self.ints.get(&n) {
            let n_loc = n_loc.clone();
            self.substitute(&ptr_loc, &n_loc);
        } else {
            let obj = self.obj_at_location_mut(&ptr_loc, false);
            *obj = Obj::AtAddr(n);
            self.ints.insert(n, ptr_loc);
        }
    }

    fn substitute(&mut self, old_loc: &AbsLoc, new_loc: &AbsLoc) {
        for node in &mut self.nodes {
            node.substitute(old_loc, new_loc);
        }
    }

    fn extend_loc(&mut self, loc: &AbsLoc) {
        for node in &mut self.nodes {
            node.extend_loc(loc);
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
        self.get_x_as_int(&AccPath::new(Local::from_usize(x), vec![]), false)
    }

    pub fn get_x_as_int(&self, x: &AccPath, deref: bool) -> Option<u128> {
        let id = self.locals.get(&x.local)?;
        let loc = if deref {
            let mut loc = self.get_pointed_loc(*id, &[])?;
            loc.projection.extend(x.projection.to_owned());
            self.get_pointed_loc(loc.root, &loc.projection)?
        } else {
            self.get_pointed_loc(*id, &x.projection)?
        };
        let obj = self.obj_at_location(&loc)?;
        let Obj::AtAddr(n) = obj else { return None };
        Some(*n)
    }

    pub fn get_deref_x_as_int(&self, x: &AccPath) -> Option<u128> {
        let id = self.locals.get(&x.local)?;
        let mut loc = self.get_pointed_loc(*id, &[])?;
        loc.projection.extend(x.projection.to_owned());
        let loc = self.get_pointed_loc(loc.root, &loc.projection)?;
        let obj = self.obj_at_location(&loc)?;
        let Obj::AtAddr(n) = obj else { return None };
        Some(*n)
    }

    pub fn invalidate_symbolic(&mut self, local: Local) {
        for node in &mut self.nodes {
            node.invalidate_symbolic(local);
        }
    }

    fn get_pointed_loc(&self, node_id: NodeId, proj: &[AccElem]) -> Option<AbsLoc> {
        let obj = self.nodes[node_id].project(proj)?;
        let Obj::Ptr(loc) = obj else { return None };
        Some(loc.clone())
    }

    fn get_pointed_loc_mut(&mut self, node_id: NodeId, proj: &[AccElem], write: bool) -> AbsLoc {
        self.set_obj_ptr(|this| this.nodes[node_id].project_mut(proj, write))
    }

    #[inline]
    fn set_obj_ptr<F: Fn(&mut Self) -> &mut Obj>(&mut self, f: F) -> AbsLoc {
        let obj = f(self);
        if let Obj::Ptr(loc) = obj {
            loc.clone()
        } else {
            let obj: *mut Obj = obj;
            let next_id = self.nodes.len();
            let loc = AbsLoc::new(next_id, vec![AccElem::Int(0)]);
            unsafe {
                *obj = Obj::Ptr(loc.clone());
            }
            let obj = Obj::Compound(HashMap::from_iter([(AccElem::Int(0), Obj::default())]));
            self.nodes.push(Node::new(obj));
            loc
        }
    }

    pub fn deref_local_id(&self, local: Local) -> Option<usize> {
        let id = self.locals.get(&local)?;
        let loc = self.get_pointed_loc(*id, &[])?;
        Some(loc.root)
    }

    pub fn obj_at_location(&self, loc: &AbsLoc) -> Option<&Obj> {
        self.nodes[loc.root].project(&loc.projection)
    }

    fn obj_at_location_mut(&mut self, loc: &AbsLoc, write: bool) -> &mut Obj {
        self.nodes[loc.root].project_mut(&loc.projection, write)
    }

    pub fn invalidate_deref(&mut self, local: Local, mut depth: usize, opt_id: Option<usize>) {
        let id = *some_or!(self.locals.get(&local), return);
        let mut locs = vec![AbsLoc::new_root(id)];
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

    fn clear_dead_locals(&mut self, dead_locals: &BitSet<Local>) {
        let locals: HashSet<_> = self.nodes.iter().flat_map(|node| node.locals()).collect();
        self.locals
            .retain(|local, _| !dead_locals.contains(*local) || locals.contains(local));
    }
}

fn join_objs(
    obj1: &Obj,
    obj2: &Obj,
    obj: &mut Obj,
    joined: &mut Graph,
    id_map: &mut HashMap<(AbsLoc, AbsLoc), NodeId>,
    remaining: &mut Vec<(AbsLoc, AbsLoc)>,
    curr_loc: AbsLoc,
) {
    match (obj1, obj2) {
        (Obj::AtAddr(i1), Obj::AtAddr(i2)) => {
            if i1 == i2 {
                *obj = Obj::AtAddr(*i1);
            }
            joined.ints.insert(*i1, curr_loc);
        }
        (Obj::Ptr(l1), Obj::Ptr(l2)) => {
            let (idp, l) = if let Some(l) = cmp_projection(&l1.projection, &l2.projection) {
                ((AbsLoc::new_root(l1.root), AbsLoc::new_root(l2.root)), l)
            } else {
                ((l1.clone(), l2.clone()), vec![])
            };
            let nid = if let Some(id) = id_map.get(&idp) {
                *id
            } else {
                let (id, _) = joined.add_node();
                id_map.insert(idp.clone(), id);
                remaining.push(idp);
                id
            };
            *obj = Obj::Ptr(AbsLoc::new(nid, l));
        }
        (Obj::Compound(fs1), Obj::Compound(fs2)) => {
            let mut fs = HashMap::new();
            for (f1, obj1) in fs1 {
                for (f2, obj2) in fs2 {
                    let f = f1.join(f2);
                    let mut nobj = Obj::default();
                    let mut curr_loc = curr_loc.clone();
                    curr_loc.projection.push(f.clone());
                    join_objs(obj1, obj2, &mut nobj, joined, id_map, remaining, curr_loc);
                    fs.insert(f, nobj);
                }
            }
            *obj = Obj::Compound(fs);
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
            (AccElem::Int(i1), AccElem::Int(i2)) if i1 == i2 => proj.push(AccElem::Int(*i1)),
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
        (_, Obj::Compound(fs)) if fs.is_empty() => true,
        (Obj::AtAddr(i1), Obj::AtAddr(i2)) => i1 == i2,
        (Obj::Ptr(l1), Obj::Ptr(l2)) => {
            let idp = (l1.root, l2.root);
            if !id_set.contains(&idp) {
                id_set.insert(idp);
                remaining.push(idp);
            }
            ord_projection(&l1.projection, &l2.projection)
        }
        (Obj::Compound(fs1), Obj::Compound(fs2)) => fs2.iter().all(|(f2, obj2)| {
            let obj1 = fs1
                .iter()
                .find_map(|(f1, obj1)| if f1.ord(f2) { Some(obj1) } else { None });
            let obj1 = some_or!(obj1, return false);
            ord_objs(obj1, obj2, id_set, remaining)
        }),
        _ => false,
    }
}

fn ord_projection(proj1: &[AccElem], proj2: &[AccElem]) -> bool {
    if proj1.len() != proj2.len() {
        return true;
    }
    let mut b = true;
    for e in proj1.iter().zip(proj2) {
        match e {
            (AccElem::Int(i1), AccElem::Int(i2)) if i1 == i2 => {}
            (AccElem::Symbolic(l1), AccElem::Symbolic(l2)) => {
                if l1.is_disjoint(l2) {
                    return true;
                }
                if !l2.is_subset(l1) {
                    b = false;
                }
            }
            _ => return true,
        }
    }
    b
}
