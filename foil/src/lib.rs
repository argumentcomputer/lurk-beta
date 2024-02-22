#![allow(dead_code)]

//! FOIL
//! Flat Optimization Intermediate Language
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use tracing::{info, warn};

use anyhow::{bail, Error};
use indexmap::IndexSet;

pub mod circuit;
pub mod coil;
pub mod congruence;
pub mod constructors;

pub use circuit::Relation;
pub use congruence::{Graph, Id, LabelTrait, MetaData, Vert};

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Func<M: MetaData> {
    name: String,
    projectors: Option<Vec<Self>>,
    // For now, we need to keep metadata with Funcs so it can be reproduced when automatically allocating new
    // constructors and projectors. This is basically due to Funcs in the Schema acting as prototypes.
    metadata: M,
}

impl<M: MetaData> Display for Func<M> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}", self.name)
    }
}

#[derive(Debug, Default, Clone, Hash, PartialEq, Eq)]
pub struct Schema<T: MetaData> {
    equivalences: Vec<Func<T>>,
    constructors: Vec<Func<T>>,
}

impl<T: MetaData> Schema<T> {
    pub fn equivalences(&self) -> Vec<Func<T>> {
        self.equivalences.clone()
    }
    pub fn constructors(&self) -> Vec<Func<T>> {
        self.constructors.clone()
    }
    pub fn add_constructor(&mut self, constructor: Func<T>, _metadata: &T) {
        self.constructors.push(constructor)
    }
}

impl<T: MetaData> Func<T> {
    pub fn new<S: Into<String>>(name: S) -> Self {
        Self {
            name: name.into(),
            projectors: None,
            metadata: T::default(),
        }
    }
    pub fn new_with_metadata<S: Into<String>>(name: S, metadata: T) -> Self {
        Self {
            name: name.into(),
            projectors: None,
            metadata,
        }
    }
    pub fn constructor<S: Into<String>>(name: S, projectors: Vec<Self>, metadata: T) -> Self {
        Self {
            name: name.into(),
            projectors: Some(projectors),
            metadata,
        }
    }
    pub fn name(&self) -> &String {
        &self.name
    }
    pub fn metadata(&self) -> &T {
        &self.metadata
    }
    pub fn projectors(&self) -> Option<&Vec<Self>> {
        self.projectors.as_ref()
    }
}

#[derive(Debug, Eq, Clone, Hash, PartialEq)]
pub struct FoilConfig {
    /// If `dedup_var_names` is `true`, `Var`s with identical names will be merged when finalizing.
    /// This option may be removed if it becomes clear that one setting is preferred.
    dedup_var_names: bool,
}

impl Default for FoilConfig {
    fn default() -> Self {
        Self {
            dedup_var_names: true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Foil<T: PartialEq, M: MetaData> {
    graph: G<M>,
    merge_queue: VecDeque<(Id, Id)>,
    fun_map: HashMap<String, IndexSet<Id>>,
    var_map: HashMap<Var, IndexSet<Id>>,
    var_counter: usize,
    constants: HashMap<Var, T>,
    schema: Schema<M>,
    state: State,
    config: FoilConfig,
}

#[derive(Debug, Default, Eq, Clone, Hash, PartialEq)]
pub struct Var(pub String, pub Option<usize>);

impl Var {
    pub fn new<S: Into<String>>(name: S) -> Self {
        Self(name.into(), None)
    }
}

impl Display for Var {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let res = write!(fmt, "Var({})", self.0);
        if let Some(id) = self.1 {
            write!(fmt, "[{}]", id)
        } else {
            res
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq)]
pub enum Label {
    F(String),
    V(String, Option<usize>),
}

impl Eq for Label {}

impl Label {
    pub fn var<S: Into<String>>(name: S) -> Self {
        Var(name.into(), None).into()
    }
}

impl Display for Label {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::F(f) => std::fmt::Display::fmt(&f, fmt),
            Self::V(_, _) => std::fmt::Display::fmt(&Var::from(self), fmt),
        }
    }
}

impl LabelTrait for Label {}

impl From<Var> for Label {
    fn from(v: Var) -> Self {
        Self::V(v.0, v.1)
    }
}
impl From<&Var> for Label {
    fn from(v: &Var) -> Self {
        Self::V(v.0.clone(), v.1)
    }
}

impl From<Label> for Var {
    fn from(label: Label) -> Self {
        Self::from(&label)
    }
}
impl From<&Label> for Var {
    fn from(label: &Label) -> Self {
        match label {
            Label::V(v, id) => Self(v.clone(), *id),
            Label::F(f) => Self(f.clone(), None),
        }
    }
}

impl<T: MetaData> From<Func<T>> for Var {
    fn from(f: Func<T>) -> Self {
        Self::from(&f)
    }
}

impl<T: MetaData> From<&Func<T>> for Var {
    fn from(f: &Func<T>) -> Self {
        Self(f.name().into(), None)
    }
}

impl<T: MetaData> From<Func<T>> for Label {
    fn from(f: Func<T>) -> Self {
        Self::from(&f)
    }
}

impl<T: MetaData> From<&Func<T>> for Label {
    fn from(f: &Func<T>) -> Self {
        Self::F(f.name().into())
    }
}

#[derive(Eq, PartialEq, Clone, Debug, Default)]
pub struct Meta {}

impl MetaData for Meta {}

type G<M> = Graph<M, Label>;

////////////////////////////////////////////////////////////////////////////////
// Foil

impl<T: PartialEq + Clone, M: MetaData> Default for Foil<T, M> {
    fn default() -> Self {
        Self {
            graph: Default::default(),
            merge_queue: Default::default(),
            fun_map: Default::default(),
            var_map: Default::default(),
            var_counter: 0,
            constants: Default::default(),
            schema: Default::default(),
            state: Default::default(),
            config: Default::default(),
        }
    }
}

impl<T: PartialEq + Clone, M: MetaData> Foil<T, M> {
    fn new<F: Into<Schema<M>>>(schema: F, config: FoilConfig) -> Self {
        let schema = schema.into();
        Self {
            graph: Default::default(),
            merge_queue: Default::default(),
            fun_map: Default::default(),
            var_map: Default::default(),
            var_counter: 0,
            constants: Default::default(),
            schema,
            state: Default::default(),
            config,
        }
    }

    fn add_constructor(&mut self, constructor: Func<M>, _metadata: &M) {
        self.schema.constructors.push(constructor)
    }

    pub fn graph(&self) -> &G<M> {
        &self.graph
    }
    pub fn graph_mut(&mut self) -> &mut G<M> {
        &mut self.graph
    }
    pub fn alloc<L: Into<Label>>(&mut self, label: L) -> Vert {
        let l = label.into();
        let vert = self.graph.alloc(l.clone(), M::default());
        self.register(&l, &vert);
        vert
    }
    pub fn alloc_var(&mut self, name: &'static str) -> Vert {
        self.alloc(Var::new(name))
    }
    pub fn alloc_unique_var<S: Into<String>>(&mut self, name: S) -> Vert {
        let var = self.unique_var(name);
        self.alloc(var)
    }
    pub fn alloc_with_meta<L: Into<Label>, MM: Into<M>>(&mut self, label: L, meta: MM) -> Vert {
        let l = label.into();
        let meta = meta.into();
        let vert = self.graph.alloc(l.clone(), meta);
        self.register(&l, &vert);
        vert
    }
    pub fn alloc_var_with_meta<MM: Into<M>, S: Into<String>>(&mut self, name: S, meta: MM) -> Vert {
        self.alloc_with_meta(Var::new(name), meta)
    }
    pub fn alloc_unique_var_with_meta<MM: Into<M>, S: Into<String>>(
        &mut self,
        name: S,
        meta: MM,
    ) -> Vert {
        let var = self.unique_var(name);
        self.alloc_with_meta(var, meta)
    }
    pub fn connect<'a, V: IntoIterator<Item = &'a Vert>>(&self, source: &Vert, targets: V) {
        self.graph.connect(source, targets)
    }

    pub fn add<F: Into<Func<M>>>(&mut self, head: F, successors: &[Vert]) -> Vert {
        let allocated_head = self.alloc(Label::from(head.into()));
        self.connect(&allocated_head, successors);
        allocated_head
    }
    pub fn add_with_meta<F: Into<Func<M>>>(
        &mut self,
        head: F,
        successors: &[Vert],
        meta: M,
    ) -> Vert {
        let allocated_head = self.alloc_with_meta(Label::from(head.into()), meta);
        self.connect(&allocated_head, successors);
        allocated_head
    }

    ////////////////////////////////////////////////////////////////////////////////

    pub fn merge(&mut self, u: Id, v: Id) {
        self.graph.merge(u, v)
    }
    pub fn register(&mut self, label: &Label, vert: &Vert) {
        match label {
            Label::F(fun) => {
                self.fun_map
                    .entry(fun.clone())
                    .and_modify(|set| {
                        (*set).insert(vert.id());
                    })
                    .or_insert_with(|| IndexSet::from([vert.id()]));
            }
            Label::V(_var, _id) => {
                self.var_map
                    .entry(Var::from(label))
                    .and_modify(|set| {
                        (*set).insert(vert.id());
                    })
                    .or_insert_with(|| IndexSet::from([vert.id()]));
            }
        }
    }
    pub fn intern_constant(&mut self, name: &'static str, value: T) -> Result<Var, Error> {
        let (var, _vert) = self.intern_var(name);
        if let Some(found) = self.constants.get(&var) {
            if *found != value {
                bail!("constant var already to different value");
            }
        } else {
            let _ = self.constants.insert(var.clone(), value);
        }
        Ok(var)
    }
    pub fn intern_var(&mut self, name: &'static str) -> (Var, Vert) {
        self.intern_var_by_label(Var::new(name))
    }
    pub fn intern_var_by_label<L: Into<Label>>(&mut self, label: L) -> (Var, Vert) {
        let label = label.into();
        let var = Var::from(label.clone());
        if let Some(id) = self.var_map.get(&var).and_then(|ids| ids.first()) {
            (var, (*id).into())
        } else {
            let vert = self.alloc(label);
            (var, vert)
        }
    }
    pub fn unique_var<S: Into<String>>(&mut self, name: S) -> Var {
        let id = self.var_counter;
        self.var_counter += 1;
        Var(name.into(), Some(id))
    }

    fn enqueue_merge<'a, U: Into<&'a Id>, V: Into<&'a Id>>(&mut self, u: Option<U>, v: Option<V>) {
        if let (Some(u), Some(v)) = (u, v) {
            let u = u.into();
            let v = v.into();
            info!(
                "will merge {} and {}",
                self.graph.vertex(*u),
                &self.graph.vertex(*v)
            );

            self.merge_queue.push_back((*u, *v))
        }
    }
    fn merge_pending(&mut self) {
        while let Some((u, v)) = self.merge_queue.pop_front() {
            info!(
                "merging {} and {}",
                &self.graph.vertex(u),
                &self.graph.vertex(v)
            );
            self.merge(u, v);
        }
    }

    fn enqueue_var_equivalences_for_merge(&mut self) {
        {
            // All vars of the same name are equivalent and must be merged.
            let mut tmp_merge_queue = VecDeque::default();

            for (var, ids) in self.var_map.iter() {
                if let Some(first) = ids.first() {
                    info!("merging vars labeled {var}");
                    for id in ids.iter().skip(1) {
                        info!("merging var {var}-{first} with {var}-{id}");
                        tmp_merge_queue.push_back((*first, *id));
                    }
                }
            }

            self.merge_queue.extend(tmp_merge_queue);
        }
    }

    fn enqueue_equivalences_for_merge(&mut self) {
        for equality_func in self.schema.equivalences().iter() {
            if let Some(equivalences) = self.fun_map.get(equality_func.name()) {
                for equivalence in equivalences {
                    let u = self.graph.vertex(*equivalence).successor(0);
                    let v = self.graph.vertex(*equivalence).successor(1);
                    info!(
                        "processing equivalence: {}",
                        self.graph.vertex(*equivalence)
                    );

                    if let (Some(u), Some(v)) = (u, v) {
                        info!(
                            "will merge {} and {}",
                            self.graph.vertex(u),
                            &self.graph.vertex(v)
                        );

                        self.merge_queue.push_back((u, v));
                    } else {
                        warn!("incomplete binding: ({u:?}, {v:?})");
                    }
                }
            }
        }
    }

    fn add_all_missing_constructors(&mut self) {
        info!("adding all missing constructors");
        for constructor in self.schema.constructors() {
            let metadata = constructor.metadata.clone();
            self.add_missing_constructors(&constructor, &metadata);
        }
    }

    fn alloc_projection(&mut self, projector: &Func<M>) -> Vert {
        if self.config.dedup_var_names {
            // If we are deduping var names generally, we still need to ensure the projections are unique.
            // Arguably, we can *always* do this, but for now only do so when demanded.
            self.alloc_unique_var(Label::from(projector).to_string())
        } else {
            self.alloc(Label::from(Var::from(projector)))
        }
    }

    fn add_missing_constructors(&mut self, constructor: &Func<M>, metadata: &M) {
        let Some(projectors) = constructor.projectors() else {
            return;
        };
        let mut needs_constructor = Vec::new();

        info!("adding missing constructors");
        for projector in projectors.iter() {
            info!("checking projector {projector:}");
            if let Some(projector_ids) = self.fun_map.get(projector.name()) {
                for projector_id in projector_ids {
                    info!("checking projector_id: {projector_id}");
                    if let Some(maybe_constructor) = self.graph.vertex(*projector_id).successor(0) {
                        if self.graph.vertex(maybe_constructor).label() != &Label::from(constructor)
                        {
                            needs_constructor.push(maybe_constructor);
                        }
                    }
                }
            }
        }
        for needs in needs_constructor.iter() {
            info!("adding constructor for {}", &self.graph.vertex(*needs));
            let constructor = self.alloc_with_meta(Label::from(constructor), metadata.clone());
            let projection_verts = projectors
                .iter()
                .map(|projector| self.alloc_projection(projector))
                .collect::<Vec<_>>();
            info!("added constructor, {}", &constructor.vertex(&self.graph));
            self.connect(&constructor, &projection_verts);
            self.enqueue_merge(Some(needs), Some(&constructor.id()));
        }
    }

    fn process_all_constructors(&mut self) {
        info!("process all constructors");
        for constructor in self.schema.constructors() {
            self.process_constructors(&constructor);
        }
    }

    fn process_constructors(&mut self, constructor: &Func<M>) {
        let Some(projectors) = constructor.projectors() else {
            return;
        };

        let mut projectors_to_add = Vec::new();

        if let Some(constructors) = self.fun_map.get(constructor.name()) {
            for constructor_id in constructors {
                info!(
                    "processing constructor, {}",
                    &self.graph.vertex(*constructor_id)
                );

                let constructor_vertex = self.graph.vertex(*constructor_id);

                let mut projector_metadata = Vec::with_capacity(projectors.len());
                let projection_ids = projectors
                    .iter()
                    .enumerate()
                    .map(|(i, projector)| {
                        projector_metadata.push(projector.metadata.clone());
                        constructor_vertex.successor(i)
                    })
                    .collect::<Vec<_>>();

                projectors_to_add.push((*constructor_id, projection_ids, projector_metadata));
            }
        }
        for (constructor, projection_ids, projector_metadata) in projectors_to_add.iter() {
            let projector_ids = projectors
                .iter()
                .zip(projector_metadata.iter())
                .map(|(projector, metadata)| {
                    // TODO: We just cloned metadata above -- shouldn't need to do it again.
                    self.alloc_with_meta(Label::from(projector), metadata.clone())
                })
                .collect::<Vec<_>>();

            let constructor_vert = Vert::new(*constructor);

            for (projector_vert, projection_id) in projector_ids.iter().zip(projection_ids.iter()) {
                info!("added projector {}", projector_vert.vertex(&self.graph));
                if let Some(projection_id) = projection_id {
                    info!(
                        "connecting to projection {}",
                        self.graph.vertex(*projection_id)
                    );
                } else {
                    info!("missing projection so not connecting");
                }
                self.connect(projector_vert, &[constructor_vert]);

                self.enqueue_merge((*projection_id).as_ref(), Some(&projector_vert.id()));
            }
        }
    }

    pub fn finalize_for_schema(&mut self) {
        // See comment in test, [crate::foil::constructors::test_var_equivalence].
        if self.config.dedup_var_names {
            self.enqueue_var_equivalences_for_merge();
        }

        self.add_all_missing_constructors();
        self.process_all_constructors();
        self.enqueue_equivalences_for_merge();
    }

    pub fn finalize(&mut self) {
        if self.is_finalized() {
            info!("Already finalized, skipping.");
        } else {
            info!("Finalizing");
            self.finalize_for_schema();
            self.merge_pending();
            self.state = State::Finalized;
        }
    }

    pub fn minimize(&mut self) -> Self {
        self.finalize();
        self.minimal()
    }

    pub fn minimal(&self) -> Self {
        assert!(self.is_finalized());

        let mut new_graph = G::default();

        let defunct_equivalence_func_ids = self
            .schema
            .equivalences()
            .iter()
            .flat_map(|fun| {
                self.fun_map
                    .get(fun.name())
                    .iter()
                    .flat_map(|id_set| {
                        id_set.iter().filter(|id| {
                            let successors = self.graph.vertex(**id).successors().borrow().clone();

                            // If an equivalence func has exactly two successors, and they are now in the same
                            // equivalence class, then it is defunct. It now expresses a tautology.
                            successors.len() == 2
                                && self.graph.find(successors[0]) == self.graph.find(successors[1])
                        })
                    })
                    .collect::<HashSet<_>>()
            })
            .collect::<HashSet<_>>();

        // Partition the graph, excluding vertices corresponding to defunct equivalence funcs.
        let partition = self
            .graph
            .to_partition(|v| !defunct_equivalence_func_ids.contains(&v.id()));

        let mut classes = partition.classes().iter().collect::<Vec<_>>();

        classes.sort_by_key(|(id, _)| *id);

        let mut new_ids: HashMap<Id, Id> = Default::default();

        // We need two passes.
        // In the first pass, we create the mapping from old ids to new ids, which we will need in the second pass.
        for (representative, _) in classes.iter() {
            let rep_vertex = self.graph.vertex(**representative);

            let label = partition
                .label(**representative)
                .unwrap_or_else(|| rep_vertex.label());

            let metadata = partition
                .metadata(**representative)
                .unwrap_or_else(|| rep_vertex.metadata());

            info!(
                "adding minimized vertex with label: {}; and metadata: {:?}",
                label, metadata
            );

            let new_vert = new_graph.alloc(label.clone(), metadata.clone());

            new_ids.insert(rep_vertex.into(), new_vert.id());
        }

        // In the second pass, we use the mapping from old to new ids to record the updated successors.
        // We do this by calling `connect` on the new ids and their corresponding new successors.
        for (representative, _) in classes.iter() {
            let new_rep_id = new_ids
                .get(*representative)
                .expect("new representative id missing");

            if let Some(successors) = partition.successors(**representative) {
                let successor_verts = successors
                    .iter()
                    .map(|s| {
                        let new_succ = new_ids.get(s).expect("new successor id missing");
                        Vert::new(*new_succ)
                    })
                    .collect::<Vec<_>>();

                new_graph.connect(&Vert::new(*new_rep_id), &successor_verts);
            }
        }

        let mut new_foil = Foil::new(self.schema.clone(), Default::default());

        new_foil.graph = new_graph;

        new_foil.state = State::Minimized;

        new_foil
    }

    pub fn is_finalized(&self) -> bool {
        self.state.is_finalized()
    }

    pub fn is_minimized(&self) -> bool {
        self.state.is_minimized()
    }
}

#[derive(Debug, Default, Clone, Hash, PartialEq, Eq)]
enum State {
    #[default]
    Initial,
    Finalized,
    Closed,
    Minimized,
}

impl State {
    pub(crate) fn is_initial(&self) -> bool {
        matches!(self, Self::Initial)
    }
    pub(crate) fn is_finalized(&self) -> bool {
        matches!(self, Self::Finalized)
    }
    pub(crate) fn is_closed(&self) -> bool {
        matches!(self, Self::Closed)
    }
    pub(crate) fn is_minimized(&self) -> bool {
        matches!(self, Self::Minimized)
    }
}

pub trait MetaMapper<M: MetaData, T> {
    fn find(&self, meta: &M) -> Option<&T>;
}

pub struct MappedFoil<T: PartialEq + Clone, M: MetaData, X, MM: MetaMapper<M, X>> {
    foil: Foil<T, M>,
    mapper: MM,
    _p: PhantomData<X>,
}

impl<T: PartialEq + Clone, M: MetaData, X, MM: MetaMapper<M, X>> MappedFoil<T, M, X, MM> {
    pub fn new(foil: Foil<T, M>, mapper: MM) -> Self {
        Self {
            foil,
            mapper,
            _p: Default::default(),
        }
    }

    pub fn find(&self, meta: &M) -> Option<&X> {
        self.mapper.find(meta)
    }
}
