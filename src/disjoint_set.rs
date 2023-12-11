use std::cell::Cell;

#[derive(Debug)]
pub struct DisjointSet<'a, T> {
    id: T,
    parent: Cell<Option<&'a DisjointSet<'a, T>>>,
    rank: Cell<usize>,
}

impl<T> PartialEq for DisjointSet<'_, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl<T> Eq for DisjointSet<'_, T> {}

impl<'a, T> DisjointSet<'a, T> {
    #[inline]
    pub fn new(id: T) -> Self {
        DisjointSet {
            id,
            parent: Cell::new(None),
            rank: Cell::new(0),
        }
    }

    pub fn find_set(&self) -> &Self {
        match self.parent.get() {
            None => self,
            Some(parent) => {
                let new_parent = parent.find_set();
                self.parent.set(Some(new_parent));
                new_parent
            }
        }
    }

    #[inline]
    pub fn union(&'a self, other: &'a Self) -> &'a Self {
        let this = self.find_set();
        let that = other.find_set();
        assert!(this != that);
        this.link(that)
    }

    fn link(&'a self, other: &'a Self) -> &'a Self {
        if self.rank > other.rank {
            other.parent.set(Some(self));
            self
        } else {
            self.parent.set(Some(other));
            if self.rank == other.rank {
                other.rank.set(other.rank.get() + 1);
            }
            other
        }
    }
}

impl<T: Copy> DisjointSet<'_, T> {
    #[inline]
    pub fn id(&self) -> T {
        self.find_set().id
    }
}
