use std::collections::HashMap;
use std::default::Default;
use std::hash::Hash;

#[derive(PartialEq, Eq, Debug, Default, Clone)]
pub(crate) struct MultiSet<T: Hash + Eq>(pub(crate) HashMap<T, usize>);

impl<T: Hash + Eq> MultiSet<T> {
    pub(crate) fn new() -> Self {
        Self(Default::default())
    }
    pub(crate) fn add(&mut self, element: T) {
        *self.0.entry(element).or_insert(0) += 1;
    }

    pub(crate) fn get(&self, element: &T) -> Option<usize> {
        self.0.get(element).copied()
    }
}
