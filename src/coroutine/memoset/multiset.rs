use std::collections::HashMap;
use std::default::Default;
use std::hash::Hash;

#[derive(PartialEq, Eq, Debug, Default, Clone)]
pub(crate) struct MultiSet<T: Hash + Eq> {
    map: HashMap<T, usize>,
    cardinality: usize,
}

impl<T: Hash + Eq> MultiSet<T> {
    pub(crate) fn new() -> Self {
        Self {
            map: Default::default(),
            cardinality: 0,
        }
    }
    pub(crate) fn add(&mut self, element: T) {
        *self.map.entry(element).or_insert(0) += 1;
        self.cardinality += 1;
    }

    pub(crate) fn get(&self, element: &T) -> Option<usize> {
        self.map.get(element).copied()
    }

    #[allow(dead_code)]
    pub(crate) fn cardinality(&self) -> usize {
        self.cardinality
    }

    #[allow(dead_code)]
    pub(crate) fn len(&self) -> usize {
        self.map.len()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_multiset() {
        let mut m = MultiSet::<usize>::new();
        let mut c = 0;
        let n = 5;

        for i in 1..n {
            for _ in 0..i {
                m.add(i);
            }
            c += i;
            assert_eq!(i, m.len());
            assert_eq!(c, m.cardinality());
            assert_eq!(Some(i), m.get(&i));
            assert_eq!(None, m.get(&(i + n)));
        }
    }
}
