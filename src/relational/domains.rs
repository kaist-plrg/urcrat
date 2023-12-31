use std::collections::{HashMap, HashSet};

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
    pub fn graph_mut(&mut self) -> &mut Graph {
        match self {
            Self::Bot => panic!(),
            Self::Mem(g) => g,
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        todo!()
    }

    pub fn ord(&self, other: &Self) -> bool {
        todo!()
    }
}

type NodeId = usize;

#[derive(Debug, Clone)]
pub struct Location {
    root: NodeId,
    projections: Vec<AccProj>,
}

impl Location {
    fn new(root: NodeId, projections: Vec<AccProj>) -> Self {
        Self { root, projections }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Int {
    Signed(i128),
    Unsigned(u128),
}

impl Int {
    pub fn as_usize(self) -> usize {
        match self {
            Self::Signed(x) => x as usize,
            Self::Unsigned(x) => x as usize,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Obj {
    Ptr(Location),
    Compound(HashMap<usize, Obj>),
    SymbolicIndex(HashSet<Local>, Box<Obj>),
}

impl Obj {
    #[inline]
    fn new() -> Self {
        Obj::Compound(HashMap::new())
    }
}

#[derive(Debug, Clone)]
pub struct Node {
    pub obj: Obj,
    pub at_addr: Option<Int>,
}

impl Node {
    #[inline]
    fn new() -> Self {
        Node {
            obj: Obj::new(),
            at_addr: None,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
    pub locals: HashMap<Local, NodeId>,
    pub ints: HashMap<Int, NodeId>,
}

impl Graph {
    fn add_node(&mut self) -> (NodeId, &mut Node) {
        let id = self.nodes.len();
        self.nodes.push(Node::new());
        (id, &mut self.nodes[id])
    }

    fn get_int_node(&mut self, n: Int) -> NodeId {
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

    fn get_local_node(&mut self, l: Local) -> (NodeId, &mut Node) {
        let id = if let Some(id) = self.locals.get(&l) {
            *id
        } else {
            let (id, _) = self.add_node();
            self.locals.insert(l, id);
            id
        };
        (id, &mut self.nodes[id])
    }

    pub fn x_eq_y(&mut self, x: &AccPath, y: &AccPath) {
        let (id, _) = self.get_local_node(y.root);
        let loc = self.get_pointed_loc(id, &y.projections);

        let obj = self.get_obj(x);
        *obj = Obj::Ptr(loc);
    }

    pub fn x_eq_deref_y(&mut self, x: &AccPath, y: &AccPath) {
        let (id, _) = self.get_local_node(y.root);
        let mut loc = self.get_pointed_loc(id, &[]);
        loc.projections.extend(y.projections.to_owned());
        let loc = self.get_pointed_loc(loc.root, &loc.projections);

        let obj = self.get_obj(x);
        *obj = Obj::Ptr(loc);
    }

    pub fn deref_x_eq_y(&mut self, x: &AccPath, y: &AccPath) {
        let (id, _) = self.get_local_node(y.root);
        let loc_y = self.get_pointed_loc(id, &y.projections);

        let (id, _) = self.get_local_node(x.root);
        let mut loc_x = self.get_pointed_loc(id, &[]);
        loc_x.projections.extend(x.projections.to_owned());

        let node = &mut self.nodes[loc_x.root];
        let obj = Self::get_obj_iter(&mut node.obj, &loc_x.projections);
        *obj = Obj::Ptr(loc_y);
    }

    pub fn x_eq_ref_y(&mut self, x: &AccPath, y: &AccPath) {
        let (id, _) = self.get_local_node(y.root);
        let loc = Location::new(id, y.projections.to_owned());

        let obj = self.get_obj(x);
        *obj = Obj::Ptr(loc);
    }

    pub fn x_eq_int(&mut self, x: &AccPath, n: Int) {
        let id = self.get_int_node(n);
        let obj = self.get_obj(x);
        *obj = Obj::Ptr(Location::new(id, vec![]));
    }

    pub fn deref_x_eq_int(&mut self, x: &AccPath, n: Int) {
        let n_id = self.get_int_node(n);
        let (id, _) = self.get_local_node(x.root);
        let mut loc = self.get_pointed_loc(id, &[]);
        loc.projections.extend(x.projections.to_owned());
        let obj = self.get_obj(x);
        *obj = Obj::Ptr(Location::new(n_id, vec![]));
    }

    pub fn x_eq(&mut self, x: &AccPath) {
        let obj = self.get_obj(x);
        *obj = Obj::new();
    }

    pub fn deref_x_eq(&mut self, x: &AccPath) {
        let (id, _) = self.get_local_node(x.root);
        let mut loc = self.get_pointed_loc(id, &[]);
        loc.projections.extend(x.projections.to_owned());
        let obj = self.get_obj(x);
        *obj = Obj::new();
    }

    pub fn get_int_value(&mut self, x: &AccPath) -> Option<Int> {
        let (id, _) = self.get_local_node(x.root);
        let loc = self.get_pointed_loc(id, &x.projections);
        if loc.projections.is_empty() {
            self.nodes[loc.root].at_addr
        } else {
            None
        }
    }

    fn get_pointed_loc(&mut self, node_id: NodeId, projs: &[AccProj]) -> Location {
        let next_id = self.nodes.len();
        let obj = Self::get_obj_iter(&mut self.nodes[node_id].obj, projs);
        let loc = if let Obj::Ptr(loc) = obj {
            loc.clone()
        } else {
            let loc = Location::new(next_id, vec![]);
            *obj = Obj::Ptr(loc.clone());
            loc
        };
        if loc.root == next_id {
            self.nodes.push(Node::new());
        }
        loc
    }

    fn get_obj(&mut self, x: &AccPath) -> &mut Obj {
        let (_, node) = self.get_local_node(x.root);
        Self::get_obj_iter(&mut node.obj, &x.projections)
    }

    fn get_obj_iter<'a>(obj: &'a mut Obj, projs: &[AccProj]) -> &'a mut Obj {
        if let Some(proj) = projs.get(0) {
            let inner = match proj {
                AccProj::Int(n) => {
                    if !matches!(obj, Obj::Compound(_)) {
                        *obj = Obj::new();
                    }
                    let Obj::Compound(fields) = obj else { unreachable!() };
                    fields.entry(*n).or_insert(Obj::new())
                }
                AccProj::Symbolic(local) => {
                    if !matches!(obj, Obj::SymbolicIndex(_, _)) {
                        *obj = Obj::SymbolicIndex(local.clone(), Box::new(Obj::new()));
                    }
                    let Obj::SymbolicIndex(_, box obj) = obj else { unreachable!() };
                    obj
                }
            };
            Self::get_obj_iter(inner, &projs[1..])
        } else {
            obj
        }
    }
}
