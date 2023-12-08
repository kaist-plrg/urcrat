use std::cell::Cell;

#[derive(Debug)]
pub struct DisjointSet<'a, T> {
    pub id: T,
    parent: Cell<Option<&'a DisjointSet<'a, T>>>,
    rank: Cell<usize>,
}

impl<'a, T> DisjointSet<'a, T> {
    pub fn new(id: T) -> Self {
        DisjointSet {
            id,
            parent: Cell::new(None),
            rank: Cell::new(0),
        }
    }

    pub fn union(&'a self, other: &'a Self) {
        self.find_set().link(other.find_set());
    }

    fn link(&'a self, other: &'a Self) {
        if self.rank > other.rank {
            other.parent.set(Some(self));
        } else {
            self.parent.set(Some(other));
            if self.rank == other.rank {
                other.rank.set(other.rank.get() + 1);
            }
        }
    }

    pub fn find_set(&self) -> &Self {
        let parent = self.parent.get();
        match parent {
            None => self,
            Some(parent) => {
                let new_parent = parent.find_set();
                self.parent.set(Some(new_parent));
                new_parent
            }
        }
    }
}
