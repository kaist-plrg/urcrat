use std::collections::{HashMap, HashSet};

use etrace::some_or;

use super::*;

#[derive(Debug)]
pub struct Solver {
    solutions: HashMap<Loc, HashSet<Loc>>,
    successors: HashMap<Loc, HashSet<Loc>>,
    constraints: HashMap<(Loc, Loc), HashSet<(Loc, Loc)>>,
    froms: HashMap<Loc, HashSet<(Loc, Vec<usize>)>>,
    tos: HashMap<Loc, HashSet<(Loc, Vec<usize>)>>,
    token_tos: HashMap<Loc, HashSet<(Loc, Vec<usize>)>>,
    worklist: Vec<(Loc, Loc)>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            solutions: HashMap::new(),
            successors: HashMap::new(),
            constraints: HashMap::new(),
            froms: HashMap::new(),
            tos: HashMap::new(),
            token_tos: HashMap::new(),
            worklist: vec![],
        }
    }

    pub fn solutions(self) -> HashMap<Loc, HashSet<Loc>> {
        self.solutions
    }

    pub fn add_token(&mut self, t: Loc, v: Loc) {
        if self
            .solutions
            .entry(v.clone())
            .or_default()
            .insert(t.clone())
        {
            self.worklist.push((t, v));
        }
    }

    pub fn add_edge(&mut self, x: Loc, y: Loc) {
        if x != y
            && self
                .successors
                .entry(x.clone())
                .or_default()
                .insert(y.clone())
        {
            for t in some_or!(self.solutions.get(&x), return).clone() {
                self.add_token(t, y.clone());
            }
        }
    }

    pub fn add_from(&mut self, x: Loc, y: Loc, proj: Vec<usize>) {
        self.froms.entry(x).or_default().insert((y, proj));
    }

    pub fn add_to(&mut self, x: Loc, y: Loc, proj: Vec<usize>) {
        self.tos.entry(x).or_default().insert((y, proj));
    }

    pub fn add_token_to(&mut self, x: Loc, y: Loc, proj: Vec<usize>) {
        self.token_tos.entry(x).or_default().insert((y, proj));
    }

    pub fn propagate(&mut self) {
        while let Some(tx) = self.worklist.pop() {
            if let Some(yzs) = self.constraints.remove(&tx) {
                for (y, z) in yzs {
                    self.add_edge(y, z);
                }
            }
            let (t, x) = tx;
            if let Some(ys) = self.froms.get(&x) {
                for (y, proj) in ys.clone() {
                    self.add_edge(t.clone().extend(proj), y);
                }
            }
            if let Some(ys) = self.tos.get(&x) {
                for (y, proj) in ys.clone() {
                    self.add_edge(y, t.clone().extend(proj));
                }
            }
            if let Some(ys) = self.token_tos.get(&x) {
                for (y, proj) in ys.clone() {
                    self.add_token(t.clone().extend(proj), y);
                }
            }
            if let Some(ys) = self.successors.get(&x) {
                for y in ys.clone() {
                    self.add_token(t.clone(), y);
                }
            }
        }
    }

    pub fn solution(&self, x: &Loc) -> Option<&HashSet<Loc>> {
        self.solutions.get(x)
    }
}
