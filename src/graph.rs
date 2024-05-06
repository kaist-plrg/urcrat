use std::collections::{HashMap, HashSet};

use etrace::some_or;
use rustc_data_structures::graph::{scc::Sccs, vec_graph::VecGraph};
use rustc_index::Idx;

pub fn transitive_closure<T: Clone + Eq + std::hash::Hash>(
    graph: &HashMap<T, HashSet<T>>,
) -> HashMap<T, HashSet<T>> {
    for succs in graph.values() {
        for succ in succs {
            assert!(graph.contains_key(succ));
        }
    }
    let id_to_v: Vec<_> = graph.keys().cloned().collect();
    let v_to_id: HashMap<_, _> = id_to_v
        .iter()
        .cloned()
        .enumerate()
        .map(|(k, v)| (v, k))
        .collect();
    let len = id_to_v.len();

    let mut reachability = vec![vec![false; len]; len];
    for (v, succs) in graph.iter() {
        for succ in succs {
            reachability[v_to_id[v]][v_to_id[succ]] = true;
        }
    }

    for k in 0..len {
        for i in 0..len {
            for j in 0..len {
                reachability[i][j] =
                    reachability[i][j] || (reachability[i][k] && reachability[k][j]);
            }
        }
    }

    let mut new_graph = HashMap::new();
    for (i, reachability) in reachability.iter().enumerate() {
        let neighbors = reachability
            .iter()
            .enumerate()
            .filter_map(|(to, is_reachable)| {
                if *is_reachable {
                    Some(id_to_v[to].clone())
                } else {
                    None
                }
            })
            .collect();
        new_graph.insert(id_to_v[i].clone(), neighbors);
    }
    new_graph
}

pub fn reachable_vertices<T: Idx + std::hash::Hash>(
    graph: &HashMap<T, HashSet<T>>,
    source: T,
    size: usize,
) -> HashSet<T> {
    let mut dists = vec![usize::MAX; size];
    dists[source.index()] = 0;

    let mut nodes = vec![];
    let mut heap = FibonacciHeap::new();
    for (i, dist) in dists.iter().cloned().enumerate() {
        nodes.push(heap.insert(i, dist));
    }

    while let Some(v) = heap.remove_min() {
        let v_dist = dists[v];
        if v_dist == usize::MAX {
            break;
        }
        let succs = some_or!(graph.get(&T::new(v)), continue);
        for succ in succs {
            let succ = succ.index();
            let dist = v_dist + 1;
            if dist < dists[succ] {
                dists[succ] = dist;
                unsafe {
                    heap.decrease_key(nodes[succ], dist);
                }
            }
        }
    }

    dists
        .into_iter()
        .enumerate()
        .filter_map(|(i, dist)| {
            if dist != usize::MAX {
                Some(T::new(i))
            } else {
                None
            }
        })
        .collect()
}

pub fn inverse<T: Clone + Eq + std::hash::Hash>(
    map: &HashMap<T, HashSet<T>>,
) -> HashMap<T, HashSet<T>> {
    let mut inv: HashMap<_, HashSet<_>> = HashMap::new();
    for node in map.keys() {
        inv.insert(node.clone(), HashSet::new());
    }
    for (node, succs) in map {
        for succ in succs {
            inv.get_mut(succ).unwrap().insert(node.clone());
        }
    }
    inv
}

pub fn compute_sccs<T: Clone + Eq + std::hash::Hash>(
    map: &HashMap<T, HashSet<T>>,
) -> (HashMap<usize, HashSet<usize>>, HashMap<usize, HashSet<T>>) {
    let id_map: HashMap<_, _> = map
        .keys()
        .enumerate()
        .map(|(i, f)| (i, f.clone()))
        .collect();
    let inv_id_map: HashMap<_, _> = id_map.iter().map(|(i, f)| (f.clone(), *i)).collect();
    let edges = map
        .iter()
        .flat_map(|(node, succs)| {
            succs
                .iter()
                .map(|succ| (inv_id_map[node], inv_id_map[succ]))
        })
        .collect();
    let sccs: Sccs<usize, usize> = Sccs::new(&VecGraph::new(map.len(), edges));

    let component_graph: HashMap<_, _> = sccs
        .all_sccs()
        .map(|node| (node, sccs.successors(node).iter().cloned().collect()))
        .collect();

    let mut component_elems: HashMap<_, HashSet<_>> = HashMap::new();
    for i in 0..(map.len()) {
        let scc = sccs.scc(i);
        let node = id_map[&i].clone();
        component_elems.entry(scc).or_default().insert(node);
    }

    (component_graph, component_elems)
}

struct Node<V, K> {
    v: V,
    k: K,
    degree: usize,
    mark: bool,
    parent: *mut Node<V, K>,
    left: *mut Node<V, K>,
    right: *mut Node<V, K>,
    children: *mut Node<V, K>,
}

impl<V, K> Node<V, K> {
    fn new(v: V, k: K) -> *mut Self {
        let node = Self {
            v,
            k,
            degree: 0,
            mark: false,
            parent: std::ptr::null_mut(),
            left: std::ptr::null_mut(),
            right: std::ptr::null_mut(),
            children: std::ptr::null_mut(),
        };
        Box::into_raw(Box::new(node))
    }

    unsafe fn make_list(this: *mut Self) {
        unsafe {
            (*this).left = this;
            (*this).right = this;
        }
    }

    unsafe fn insert(this: *mut Self, node: *mut Self) {
        unsafe {
            (*node).left = (*this).left;
            (*(*this).left).right = node;
            (*this).left = node;
            (*node).right = this;
        }
    }

    unsafe fn remove(this: *mut Self) {
        unsafe {
            (*(*this).left).right = (*this).right;
            (*(*this).right).left = (*this).left;
        }
    }

    fn free(&mut self) {
        let mut x = self.children;
        if x.is_null() {
            return;
        }
        loop {
            let mut node = unsafe { Box::from_raw(x) };
            x = node.right;
            node.free();
            if x == self.children {
                break;
            }
        }
    }
}

struct FibonacciHeap<V, K> {
    min: *mut Node<V, K>,
    n: usize,
}

impl<V, K> Drop for FibonacciHeap<V, K> {
    fn drop(&mut self) {
        let mut x = self.min;
        if x.is_null() {
            return;
        }
        loop {
            let mut node = unsafe { Box::from_raw(x) };
            x = node.right;
            node.free();
            if x == self.min {
                break;
            }
        }
    }
}

impl<V, K: Ord + Copy> FibonacciHeap<V, K> {
    fn new() -> Self {
        Self {
            min: std::ptr::null_mut(),
            n: 0,
        }
    }

    fn insert(&mut self, v: V, k: K) -> *mut Node<V, K> {
        let node = Node::new(v, k);
        if self.min.is_null() {
            unsafe {
                Node::make_list(node);
            }
            self.min = node;
        } else {
            unsafe {
                Node::insert(self.min, node);
            }
            if k < unsafe { (*self.min).k } {
                self.min = node;
            }
        }
        self.n += 1;
        node
    }

    fn remove_min(&mut self) -> Option<V> {
        if self.min.is_null() {
            return None;
        }
        let z = self.min;
        let v = unsafe {
            let mut x = (*z).children;
            if !x.is_null() {
                loop {
                    let next = (*x).right;
                    Node::insert(self.min, x);
                    (*x).parent = std::ptr::null_mut();
                    x = next;
                    if x == (*z).children {
                        break;
                    }
                }
            }
            Node::remove(z);
            if z == (*z).right {
                self.min = std::ptr::null_mut();
            } else {
                self.min = (*z).right;
                self.consolidate();
            }
            Box::into_inner(Box::from_raw(z)).v
        };
        self.n -= 1;
        Some(v)
    }

    fn consolidate(&mut self) {
        let dn = (self.n as f64).log(1.61803).ceil() as usize;
        let mut arr = vec![std::ptr::null_mut::<Node<V, K>>(); dn];
        let mut w = self.min;
        let last = unsafe { (*w).left };
        loop {
            unsafe {
                let next = (*w).right;
                let mut x = w;
                let mut d = (*x).degree;
                while !arr[d].is_null() {
                    let mut y = arr[d];
                    if (*x).k > (*y).k {
                        std::mem::swap(&mut x, &mut y);
                    }
                    self.link(y, x);
                    arr[d] = std::ptr::null_mut();
                    d += 1;
                }
                arr[d] = x;
                if w == last {
                    break;
                }
                w = next;
            }
        }
        self.min = std::ptr::null_mut();
        for x in arr {
            if x.is_null() {
                continue;
            }
            if self.min.is_null() {
                unsafe {
                    Node::make_list(x);
                }
                self.min = x;
            } else {
                unsafe {
                    Node::insert(self.min, x);
                    if (*x).k < (*self.min).k {
                        self.min = x;
                    }
                }
            }
        }
    }

    unsafe fn link(&mut self, y: *mut Node<V, K>, x: *mut Node<V, K>) {
        unsafe {
            Node::remove(y);
            if (*x).children.is_null() {
                (*x).children = y;
                Node::make_list(y);
            } else {
                Node::insert((*x).children, y);
            }
            (*y).parent = x;
            (*y).mark = false;
            (*x).degree += 1;
        }
    }

    unsafe fn decrease_key(&mut self, x: *mut Node<V, K>, k: K) {
        unsafe {
            assert!(k < (*x).k);
            (*x).k = k;
            let y = (*x).parent;
            if !y.is_null() && (*x).k < (*y).k {
                self.cut(x, y);
                self.cascading_cut(y);
            }
            if (*x).k < (*self.min).k {
                self.min = x;
            }
        }
    }

    unsafe fn cut(&mut self, x: *mut Node<V, K>, y: *mut Node<V, K>) {
        unsafe {
            Node::remove(x);
            if x == (*x).right {
                (*y).children = std::ptr::null_mut();
            } else {
                (*y).children = (*x).right;
            }
            Node::insert(self.min, x);
            (*y).degree -= 1;
            (*x).parent = std::ptr::null_mut();
            (*x).mark = false;
        }
    }

    unsafe fn cascading_cut(&mut self, y: *mut Node<V, K>) {
        unsafe {
            let z = (*y).parent;
            if z.is_null() {
                return;
            }
            if !(*y).mark {
                (*y).mark = true;
            } else {
                self.cut(y, z);
                self.cascading_cut(z);
            }
        }
    }
}
