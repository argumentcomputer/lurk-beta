//! Congruence Closure
//!
//! As described in [Fast Decision Procedures Based on Congruence Closure](https://dl.acm.org/doi/10.1145/322186.322198)

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use tracing::info;

use indexmap::IndexSet;

pub trait LabelTrait: PartialEq + Clone + Display + Debug + Eq {}
pub trait MetaData: PartialEq + Clone + Debug + Default {}

impl MetaData for () {}

pub type Id = usize;
pub type SimpleLabel = &'static str;
impl LabelTrait for SimpleLabel {}

#[derive(Debug, Default, Eq, Clone, PartialEq)]
pub struct Vertex<T: MetaData, L: LabelTrait> {
    id: Id,
    label: L,
    metadata: T,
    predecessors: RefCell<IndexSet<Id>>,
    successors: RefCell<Vec<Id>>,
    equiv: RefCell<Id>,
}

impl<T: MetaData, L: LabelTrait> Display for Vertex<T, L> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}: {}", self.label, self.id)
    }
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub struct Vert {
    id: Id,
}

impl From<Id> for Vert {
    fn from(id: Id) -> Self {
        Self::new(id)
    }
}

impl Vert {
    pub fn new(id: Id) -> Self {
        Self { id }
    }
    pub fn vertex<'a, T: MetaData, L: LabelTrait>(&'a self, g: &'a Graph<T, L>) -> &Vertex<T, L> {
        g.vertex(self.id)
    }
    pub fn id(&self) -> Id {
        self.id
    }
    pub fn congruent<T: MetaData, L: LabelTrait>(&self, g: &Graph<T, L>, other: &Self) -> bool {
        g.congruent(self.id(), other.id())
    }
    pub fn merge<T: MetaData, L: LabelTrait>(&self, g: &mut Graph<T, L>, other: &Self) {
        g.merge(self.id(), other.id())
    }
    pub fn connect<'a, V: IntoIterator<Item = &'a Vert>, T: MetaData, L: LabelTrait>(
        &self,
        g: &mut Graph<T, L>,
        targets: V,
    ) {
        g.connect(self, targets)
    }
    pub fn find<T: MetaData, L: LabelTrait>(&self, g: &Graph<T, L>) -> Id {
        g.find(self.id())
    }
    pub fn find_vertex<'a, T: MetaData, L: LabelTrait>(
        &'a self,
        g: &'a Graph<T, L>,
    ) -> &Vertex<T, L> {
        let id = self.find(g);
        g.vertex(id)
    }
}

impl From<&Vert> for Id {
    fn from(v: &Vert) -> Id {
        v.id
    }
}
impl<T: MetaData, L: LabelTrait> From<&Vertex<T, L>> for Id {
    fn from(v: &Vertex<T, L>) -> Id {
        v.id
    }
}

impl<T: MetaData, L: LabelTrait> Vertex<T, L> {
    pub fn new(id: Id, label: L, metadata: T) -> Self {
        Self {
            id,
            label,
            metadata,
            successors: Default::default(),
            predecessors: Default::default(),
            equiv: RefCell::new(id),
        }
    }

    pub fn id(&self) -> usize {
        self.id
    }

    pub fn vert(&self) -> Vert {
        Vert::new(self.id)
    }

    pub fn label(&self) -> &L {
        &self.label
    }

    pub fn arity(&self) -> usize {
        self.successors.borrow().len()
    }

    pub fn metadata(&self) -> &T {
        &self.metadata
    }

    pub fn predecessors(&self) -> RefCell<IndexSet<Id>> {
        self.predecessors.clone()
    }

    pub fn predecessors_owned(&self) -> IndexSet<Id> {
        self.predecessors.borrow().clone()
    }

    pub fn find_predecessor<'a, P: FnMut(&Vertex<T, L>) -> bool>(
        &'a self,
        g: &'a Graph<T, L>,
        mut predicate: P,
    ) -> Option<&Vertex<T, L>> {
        for id in self.predecessors.borrow().iter() {
            let vertex = g.vertex(*id);
            if predicate(vertex) {
                return Some(vertex);
            }
        }
        None
    }

    pub fn successors(&self) -> RefCell<Vec<Id>> {
        self.successors.clone()
    }

    pub fn successor(&self, n: usize) -> Option<Id> {
        self.successors.borrow().get(n).copied()
    }

    pub fn equiv(&self) -> Id {
        *self.equiv.borrow()
    }

    pub fn set_equiv(&self, id: Id) {
        *(self.equiv.borrow_mut()) = id;
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Graph<T: MetaData, L: LabelTrait> {
    vertices: Vec<Vertex<T, L>>,
    union_called: bool,
}

impl<T: MetaData, L: LabelTrait> Default for Graph<T, L> {
    fn default() -> Self {
        Self {
            vertices: Default::default(),
            union_called: false,
        }
    }
}

impl<'a, T: MetaData, L: LabelTrait> Graph<T, L> {
    pub fn alloc<LL: Into<L>>(&'a mut self, label: LL, metadata: T) -> Vert {
        // Vertices can never be removed,
        let new_id = self.vertices.len();
        self.vertices
            .push(Vertex::new(new_id, label.into(), metadata));

        Vert::new(new_id)
    }

    pub fn connect<V: IntoIterator<Item = &'a Vert>>(&self, source: &Vert, targets: V) {
        // union coalesces predecessors into the class representative,
        // so the graph must not be modified once it has been called.
        assert!(!self.union_called, "connect must not be called after union");

        let source_id = source.id();
        let target_ids: Vec<Id> = targets
            .into_iter()
            .map(|target_vert| {
                // NOTE: We use the target's class representative via find.
                let target_find = target_vert.find_vertex(self);

                //target_ids.push(target_find.id());
                target_find.predecessors.borrow_mut().insert(source_id);

                target_find.id()
            })
            .collect();

        // Replace any existing successors. `connect` is not cumulative.
        *(source.vertex(self).successors.borrow_mut()) = target_ids;
    }

    pub fn vertices(&self) -> &Vec<Vertex<T, L>> {
        &self.vertices
    }

    pub fn vertex(&self, id: Id) -> &Vertex<T, L> {
        &self.vertices[id]
    }

    pub fn partition(&self) -> Partition<T, L> {
        self.into()
    }

    /// Returns a vector of triples, each represnting the following per equivalence class:
    /// - The `Id` of its representative member.
    /// - A vector of its members' Vertex's descriptive strings.
    /// - An optional vector of its ordered successors, if any.
    /// Successor vectors include the `Id` of the class representative at each position, rather than that originally
    /// specified.
    pub fn class_info(
        &self,
        p: Option<Partition<T, L>>,
    ) -> Vec<(Id, Vec<String>, Option<Vec<Id>>)> {
        let p = p.unwrap_or_else(|| self.partition());

        let mut classes = p.classes().iter().collect::<Vec<_>>();
        classes.sort_by_key(|(id, _)| *id);

        classes
            .iter()
            .map(|(id, set)| {
                let mut class = set
                    .iter()
                    .map(|id| (id, format!("{}", self.vertex(*id)), None::<Option<Vec<Id>>>))
                    .collect::<Vec<_>>();

                class.sort_by_key(|x| *x.0);
                (
                    **id,
                    class.into_iter().map(|x| x.1).collect(),
                    p.successors(**id),
                )
            })
            .collect()
    }

    pub fn find(&self, mut id: Id) -> Id {
        // let input_id = id;
        loop {
            let old_id = id;
            let v = self.vertex(id);
            id = v.equiv();

            if id == old_id {
                break;
            }
        }
        // info!("find(id{input_id}) => {id}");
        id
    }

    pub fn union(&mut self, u: Id, v: Id) {
        self.union_called = true;

        let find_u = self.find(u);
        let uu = self.vertex(find_u);

        let find_v = self.find(v);
        let vv = self.vertex(find_v);

        let l = vv.predecessors.borrow().len();
        for pred in vv.predecessors.borrow_mut().drain(0..l) {
            uu.predecessors.borrow_mut().insert(pred);
        }

        vv.set_equiv(find_u);
    }

    pub fn merge(&mut self, u: Id, v: Id) {
        info!("merging {} and {}", self.vertex(u), self.vertex(v));
        let find_u = self.find(u);
        let find_v = self.find(v);

        if find_u == find_v {
            return;
        }

        let p_u = self.vertex(find_u).predecessors().borrow().clone();
        let p_v = self.vertex(find_v).predecessors().borrow().clone();
        info!(
            "num predecessors: {}={} and {}={}",
            self.vertex(find_u),
            p_u.len(),
            self.vertex(find_v),
            p_v.len()
        );
        self.union(u, v);

        for x in p_u.iter() {
            for y in p_v.iter() {
                info!(
                    "checking predecesor congruence: {} and {}",
                    self.vertex(*x),
                    self.vertex(*y)
                );
                let find_x = self.find(*x);
                let find_y = self.find(*y);

                if find_x != find_y && self.congruent(*x, *y) {
                    info!("recursive merge");
                    // TODO: We might need or want an explicit stack rather than recursive call.
                    self.merge(*x, *y)
                }
            }
        }
    }

    pub fn congruent(&self, u: Id, v: Id) -> bool {
        info!(
            "checking congruence of {} and {}",
            self.vertex(u),
            self.vertex(v)
        );
        let u_succ = self.vertex(u).successors();
        let v_succ = self.vertex(v).successors();

        let labels_equal = self.vertex(u).label == self.vertex(v).label;

        let result = labels_equal
            && u_succ.borrow().len() == v_succ.borrow().len()
            && u_succ
                .borrow()
                .iter()
                .zip(v_succ.borrow().iter())
                .all(|(x, y)| self.find(*x) == self.find(*y));
        if result {
            info!("congruent")
        } else {
            info!("not congruent")
        }
        result
    }

    /// Partition `self` (a `Graph`), filtering vertices to those for which `predicate` is true.
    pub fn to_partition<F: Fn(&Vertex<T, L>) -> bool>(&self, predicate: F) -> Partition<T, L> {
        let mut classes: HashMap<Id, IndexSet<Id>> = Default::default();
        let mut index: HashMap<Id, Id> = Default::default();
        let mut successors: HashMap<Id, Vec<Id>> = Default::default();
        let mut labels: HashMap<Id, L> = Default::default();
        let mut metadata: HashMap<Id, T> = Default::default();

        for (id, _v) in self
            .vertices
            .iter()
            .enumerate()
            .filter(|(_, v)| predicate(*v))
        {
            let find_v = self.find(id);
            let vertex = self.vertex(id);
            let successor_ids = vertex
                .successors()
                .borrow()
                .iter()
                .map(|id| self.find(*id))
                .collect::<Vec<_>>();

            if !successor_ids.is_empty() {
                successors.insert(find_v, successor_ids);

                // The label we want is that of the original vertex that has successors. By definition, this must be the
                // same for all such vertices in an equivalence class.
                labels.insert(find_v, vertex.label().clone());

                // Same goes for the metadata.
                metadata.insert(find_v, vertex.metadata().clone());
                info!(
                    "partition, assigning {id} to class {find_v} with label {:?} and metadata {:?}",
                    vertex.label(),
                    vertex.metadata()
                );
            } else {
                info!("partition, assigning {id} to class {find_v}",);
            }
            classes
                .entry(find_v)
                .and_modify(|set| {
                    (*set).insert(id);
                })
                .or_insert_with(|| IndexSet::from([find_v, id]));
            index.insert(id, find_v);
        }
        Partition {
            classes,
            index,
            successors,
            labels,
            metadata,
        }
    }
}

#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct Partition<T: MetaData, L: LabelTrait> {
    // mapping from unique representative to all members of equivalence classes
    pub classes: HashMap<Id, IndexSet<Id>>,
    // mapping from members to the unique representative indexing the class
    pub index: HashMap<Id, Id>,
    // successors of the class, indexed by representative
    // all successors are themselves class representatives (via find).
    pub successors: HashMap<Id, Vec<Id>>,
    pub labels: HashMap<Id, L>,
    pub metadata: HashMap<Id, T>,
}

impl<T: MetaData, L: LabelTrait> Partition<T, L> {
    pub fn class(&self, id: Id) -> Option<&IndexSet<Id>> {
        self.index
            .get(&id)
            .and_then(|index| self.classes.get(index))
    }

    pub fn classes(&self) -> &HashMap<Id, IndexSet<Id>> {
        &self.classes
    }

    pub fn index(&self) -> &HashMap<Id, Id> {
        &self.index
    }
    pub fn successors(&self, id: Id) -> Option<Vec<Id>> {
        self.successors.get(&id).cloned()
    }
    pub fn label(&self, id: Id) -> Option<&L> {
        self.labels.get(&id)
    }

    pub fn metadata(&self, id: Id) -> Option<&T> {
        self.metadata.get(&id)
    }

    pub fn size(&self) -> usize {
        self.index.len()
    }

    pub fn find(&self, id: Id) -> Id {
        *self.index.get(&id).expect("invalid id")
    }
}

impl<T: MetaData, L: LabelTrait> From<&Graph<T, L>> for Partition<T, L> {
    fn from(g: &Graph<T, L>) -> Self {
        g.to_partition(|_| true)
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;

    pub(crate) type IdVec = Vec<Id>;
    pub(crate) fn assert_expected_classes(
        expected: &[(Id, Vec<&str>, Option<IdVec>)],
        actual: &[(Id, Vec<String>, Option<IdVec>)],
    ) {
        assert_eq!(expected.len(), actual.len());
        for ((expected_id, expected_class, expected_successors), (id, class, successors)) in
            expected.iter().zip(actual.iter())
        {
            assert_eq!(expected_id, id);
            for (expected_member, member) in expected_class.iter().zip(class.iter()) {
                assert_eq!(expected_member, &member);
            }
            assert_eq!(expected_successors, successors);
        }
    }

    #[test]
    fn test_congruence() {
        let g = &mut Graph::<(), SimpleLabel>::default();

        // See Figure 1 of the paper.
        //
        //   f<--f
        //  / \ /
        // a   b
        let v1 = g.alloc("f", ());
        let v2 = g.alloc("f", ());
        let v3 = g.alloc("a", ());
        let v4 = g.alloc("b", ());

        v1.connect(g, &[v2, v4]);
        v2.connect(g, &[v3, v4]);

        {
            let partition = g.partition();

            assert_eq!(partition.class(0), Some(&IndexSet::from([0])));
            assert_eq!(partition.class(1), Some(&IndexSet::from([1])));
            assert_eq!(partition.class(2), Some(&IndexSet::from([2])));
            assert_eq!(partition.class(3), Some(&IndexSet::from([3])));
        }
        assert!(!v1.congruent(g, &v2));
        assert!(!v1.congruent(g, &v3));
        assert!(!v1.congruent(g, &v4));
        assert!(!v2.congruent(g, &v3));
        assert!(!v2.congruent(g, &v4));
        assert!(!v3.congruent(g, &v4));

        v2.merge(g, &v3);

        {
            let partition = dbg!(g.partition());

            assert_eq!(partition.class(0), Some(&IndexSet::from([0, 1, 2])));
            assert_eq!(partition.class(1), Some(&IndexSet::from([0, 1, 2])));
            assert_eq!(partition.class(2), Some(&IndexSet::from([0, 1, 2])));
            assert_eq!(partition.class(3), Some(&IndexSet::from([3])));
        }

        assert!(v1.congruent(g, &v2));
        assert_eq!(g.find(v2.id()), g.find(v3.id()));
        assert!(!v3.congruent(g, &v4));
    }
}
