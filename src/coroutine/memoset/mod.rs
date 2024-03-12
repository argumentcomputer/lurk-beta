//! The `memoset` module implements a `MemoSet`.
//!
//! A `MemoSet` is an abstraction we use to memoize deferred proof of (potentially mutually-recursive) query results.
//! Whenever a computation being proved needs the result of a query, the prover non-deterministically supplies the
//! correct result. The resulting key-value pair is then added to a multiset representing deferred proofs. The
//! dependent proof now must not be accepted until every element in the deferred-proof multiset has been proved.
//!
//! Implementation depends on a cryptographic multiset -- for example, ECMH or LogUp (implemented here). This allows us
//! to prove that every element added to to the multiset is later removed only after having been proved. The
//! cryptographic assumption is that it is infeasible to fraudulently demonstrate multiset equality.
//!
//! Our use of the LogUp (logarithmic derivative) technique in the `LogMemo` implementation of `MemoSet` unfortunately
//! requires that the entire history of insertions and removals be committed to in advance -- so that Fiat-Shamir
//! randomness derived from the transcript can be used when mapping field elements to multiset elements. We use Lurk
//! data to assemble the transcript, so that the final randomness is the hash/value component of a `ZPtr` to the
//! content-addressed data structure representing the transcript as assembled.
//!
//! Transcript elements represent deferred proofs that are either added to (when their results are used) or removed from
//! (when correctness of those results is proved) the 'deferred proof' multiset. Insertions are recorded in the
//! transcript as key-value pairs (Lurk data: `(key . value)`); and removals further include the removal multiplicity
//! (Lurk data: `((key . value) . multiplicity)`). It is critical that the multiplicity be included in the transcript,
//! since if free to choose it after the randomness has been derived, the prover can trivially falsify the contents of
//! the multiset -- decoupling claimed truths from those actually proved.
//!
//! Bookkeeping required to correctly build the transcript after evaluation but before proving is maintained by the
//! `Scope`. This allows us to accumulate queries and the subqueries on which they depend, along with the memoized query
//! results computed 'naturally' during evaluation. We then separate and sort in an order matching that which the NIVC
//! prover will follow when provably maintaining the multiset accumulator and Fiat-Shamir transcript in the circuit.

use indexmap::IndexMap;
use itertools::Itertools;
use std::collections::HashSet;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::sync::Arc;

use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use once_cell::sync::OnceCell;

use crate::circuit::gadgets::{
    constraints::{enforce_equal, enforce_equal_zero, invert, sub},
    pointer::AllocatedPtr,
};
use crate::coprocessor::gadgets::{
    construct_cons, construct_list, construct_provenance, deconstruct_provenance,
};
use crate::field::LurkField;
use crate::lem::circuit::GlobalAllocator;
use crate::lem::tag::Tag;
use crate::lem::{
    pointers::Ptr,
    store::{Store, WithStore},
};
use crate::symbol::Symbol;
use crate::tag::{ExprTag, Tag as XTag};
use crate::z_ptr::ZPtr;

use multiset::MultiSet;
pub use query::{CircuitQuery, Query};

mod demo;
mod env;
mod multiset;
pub mod prove;
mod query;

#[derive(Debug)]
pub enum MemoSetError {
    QueryDependenciesMissing,
    QueryResultMissing,
}

#[derive(Clone, Debug)]
pub struct Transcript<F> {
    acc: Ptr,
    _p: PhantomData<F>,
}

impl<F: LurkField> Transcript<F> {
    fn new(s: &Store<F>) -> Self {
        let nil = s.intern_nil();
        Self {
            acc: nil,
            _p: Default::default(),
        }
    }

    fn add(&mut self, s: &Store<F>, item: Ptr) {
        self.acc = s.cons(item, self.acc);
    }

    fn make_kv(s: &Store<F>, key: Ptr, value: Ptr) -> Ptr {
        s.cons(key, value)
    }

    fn make_provenance_count(s: &Store<F>, provenance: Ptr, count: usize) -> Ptr {
        let count_num = s.num(F::from_u64(count as u64));
        s.cons(provenance, count_num)
    }

    /// Since the transcript is just a content-addressed Lurk list, its randomness is the hash value of the associated
    /// top-level `Cons`. This function sanity-checks the type and extracts that field element.
    fn r(&self, s: &Store<F>) -> F {
        let z_ptr = s.hash_ptr(&self.acc);
        assert_eq!(Tag::Expr(ExprTag::Cons), *z_ptr.tag());
        *z_ptr.value()
    }

    #[allow(dead_code)]
    fn dbg(&self, s: &Store<F>) {
        tracing::debug!("transcript: {}", self.acc.fmt_to_string_simple(s));
    }

    #[allow(dead_code)]
    fn fmt_to_string_simple(&self, s: &Store<F>) -> String {
        self.acc.fmt_to_string_simple(s)
    }
}

#[derive(Clone, Debug)]
pub struct CircuitTranscript<F: LurkField> {
    acc: AllocatedPtr<F>,
}

impl<F: LurkField> CircuitTranscript<F> {
    fn new<CS: ConstraintSystem<F>>(cs: &mut CS, g: &GlobalAllocator<F>, s: &Store<F>) -> Self {
        let nil = s.intern_nil();
        let allocated_nil = g.alloc_ptr(cs, &nil, s);
        Self {
            acc: allocated_nil.clone(),
        }
    }

    pub fn pick<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        condition: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError> {
        let picked = AllocatedPtr::pick(cs, condition, &a.acc, &b.acc)?;
        Ok(Self { acc: picked })
    }

    fn add<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        item: &AllocatedPtr<F>,
    ) -> Result<Self, SynthesisError> {
        let acc = construct_cons(cs, g, s, item, &self.acc)?;

        Ok(Self { acc })
    }

    fn make_provenance_count<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        provenance: &AllocatedPtr<F>,
        count: u64,
    ) -> Result<(AllocatedPtr<F>, AllocatedNum<F>), SynthesisError> {
        let allocated_count = { AllocatedNum::alloc(ns!(cs, "count"), || Ok(F::from_u64(count)))? };
        let count_ptr = AllocatedPtr::alloc_tag(
            ns!(cs, "count_ptr"),
            ExprTag::Num.to_field(),
            allocated_count.clone(),
        )?;

        Ok((
            construct_cons(cs, g, s, provenance, &count_ptr)?,
            allocated_count,
        ))
    }

    fn r(&self) -> &AllocatedNum<F> {
        self.acc.hash()
    }

    #[allow(dead_code)]
    fn dbg(&self, s: &Store<F>) {
        let z = self.acc.get_value::<Tag>().unwrap();
        let transcript = s.to_ptr(&z);

        tracing::debug!("transcript: {}", transcript.fmt_to_string_simple(s));
    }
}

#[derive(Debug)]
pub struct Provenance {
    ptr: OnceCell<Ptr>,
    query: Ptr,
    result: Ptr,
    // Dependencies is an ordered list of provenance(Ptr)s on which this depends.
    dependencies: Vec<Ptr>,
}

impl Provenance {
    fn new(
        query: Ptr,
        result: Ptr,
        // Provenances on which this depends.
        dependencies: Vec<Ptr>,
    ) -> Self {
        Self {
            ptr: OnceCell::new(),
            query,
            result,
            dependencies,
        }
    }

    fn dummy<F: LurkField>(store: &Store<F>) -> Self {
        let nil = store.intern_nil();
        let sym = store.intern_symbol(&Symbol::sym(&["lurk", "query", "dummy"]));
        let query = store.cons(sym, nil);
        Self::new(query, nil, vec![])
    }

    fn to_ptr<F: LurkField>(&self, store: &Store<F>) -> &Ptr {
        self.ptr.get_or_init(|| {
            let dependencies_list = if self.dependencies.len() == 1 {
                self.dependencies[0]
            } else {
                store.list(self.dependencies.clone())
            };

            store.intern_provenance(self.query, self.result, dependencies_list)
        })
    }
}

#[derive(Debug)]
pub struct AllocatedProvenance<F: LurkField> {
    ptr: OnceCell<AllocatedPtr<F>>,
    query: AllocatedPtr<F>,
    result: AllocatedPtr<F>,
    // Dependencies is an ordered list of provenance(Ptr)s on which this depends.
    dependencies: Vec<AllocatedPtr<F>>,
}

impl<F: LurkField> AllocatedProvenance<F> {
    fn new(
        query: AllocatedPtr<F>,
        result: AllocatedPtr<F>,
        // Provenances on which this depends.
        dependencies: Vec<AllocatedPtr<F>>,
    ) -> Self {
        Self {
            ptr: OnceCell::new(),
            query,
            result,
            dependencies,
        }
    }

    fn to_ptr<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
    ) -> Result<&AllocatedPtr<F>, SynthesisError> {
        self.ptr.get_or_try_init(|| {
            let deps = {
                let arity = self.dependencies.len();

                if arity == 1 {
                    self.dependencies[0].clone()
                } else {
                    // TODO: Use a hash of exactly `arity` instead of a Lurk list.
                    construct_list(ns!(cs, "dependencies_list"), g, s, &self.dependencies, None)?
                }
            };

            construct_provenance(
                ns!(cs, "provenance"),
                g,
                s,
                self.query.hash(),
                &self.result,
                deps.hash(),
            )
        })
    }
}

type PW<'a, F> = WithStore<'a, F, Provenance>;

impl<'a, F: LurkField> Debug for PW<'a, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let p = self.inner();
        let s = self.store();

        f.debug_struct("Provenance")
            .field("full", &p.to_ptr(s).fmt_to_string_simple(s))
            .field("query", &p.query.fmt_to_string_simple(s))
            .field(
                "dependencies",
                &p.dependencies
                    .iter()
                    .map(|ptr| ptr.fmt_to_string_simple(s))
                    .join(", "),
            )
            .finish()
    }
}

#[derive(Clone, Debug)]
/// A `Scope` tracks the queries made while evaluating, including the subqueries that result from evaluating other
/// queries -- then makes use of the bookkeeping performed at evaluation time to synthesize proof of each query
/// performed.
pub struct Scope<Q: Query<F>, M, F: LurkField> {
    memoset: M,
    /// k => v
    queries: IndexMap<Ptr, Ptr>,
    /// k => ordered subqueries
    dependencies: IndexMap<Ptr, Vec<Q>>,
    /// inverse of dependencies
    dependents: IndexMap<Ptr, HashSet<Ptr>>,
    /// kv pairs
    toplevel_insertions: Vec<Ptr>,
    /// internally-inserted keys
    internal_insertions: Vec<Ptr>,
    /// unique keys: query-index -> [key]
    unique_inserted_keys: IndexMap<usize, Vec<Ptr>>,
    // This may become an explicit map or something allowing more fine-grained control.
    provenances: OnceCell<IndexMap<ZPtr<Tag, F>, ZPtr<Tag, F>>>,
    default_rc: usize,
    pub(crate) store: Arc<Store<F>>,
    pub(crate) runtime_data: Q::RD,
}

const DEFAULT_RC_FOR_QUERY: usize = 1;

impl<F: LurkField, Q: Query<F>> Scope<Q, LogMemo<F>, F> {
    #[allow(dead_code)]
    pub fn new(default_rc: usize, store: Arc<Store<F>>, runtime_data: Q::RD) -> Self {
        Self {
            memoset: Default::default(),
            queries: Default::default(),
            dependencies: Default::default(),
            dependents: Default::default(),
            toplevel_insertions: Default::default(),
            internal_insertions: Default::default(),
            unique_inserted_keys: Default::default(),
            provenances: Default::default(),
            default_rc,
            runtime_data,
            store,
        }
    }

    fn provenance(&self, query: Ptr) -> Result<Provenance, MemoSetError> {
        let store = self.store.as_ref();
        let query_dependencies = self.dependencies.get(&query);
        let result = self
            .queries
            .get(&query)
            .ok_or(MemoSetError::QueryResultMissing)?;

        let dependencies = if let Some(deps) = query_dependencies {
            Ok(deps
                .iter()
                .map(|query| {
                    let ptr = query.to_ptr(store);
                    *self.provenance(ptr).unwrap().to_ptr(store)
                })
                .collect())
        } else {
            Err(MemoSetError::QueryDependenciesMissing)
        }?;

        Ok(Provenance::new(query, *result, dependencies))
    }

    fn provenance_from_kv(&self, kv: Ptr) -> Result<Provenance, MemoSetError> {
        let store = self.store.as_ref();
        let (query, result) = store.car_cdr(&kv).expect("kv missing");
        let query_dependencies = self.dependencies.get(&query);

        let dependencies = if let Some(deps) = query_dependencies {
            Ok(deps
                .iter()
                .map(|query| {
                    let ptr = query.to_ptr(store);
                    *self.provenance(ptr).unwrap().to_ptr(store)
                })
                .collect())
        } else {
            Ok(Vec::new())
        }?;

        Ok(Provenance::new(query, result, dependencies))
    }

    fn init_memoset(&self) -> Ptr {
        let s = self.store.as_ref();
        let mut memoset = s.num(F::ZERO);
        for kv in self.toplevel_insertions.iter() {
            let provenance = self.provenance_from_kv(*kv).unwrap();
            memoset = self.memoset.acc_add(&memoset, provenance.to_ptr(s), s);
        }
        memoset
    }

    fn init_transcript(&self) -> Ptr {
        let s = self.store.as_ref();
        let mut transcript = Transcript::new(s);
        for kv in self.toplevel_insertions.iter() {
            let provenance = self.provenance_from_kv(*kv).unwrap();
            transcript.add(s, *provenance.to_ptr(s));
        }
        transcript.acc
    }
}

#[derive(Debug, Clone)]
pub struct CircuitScope<'a, F: LurkField, CM, RD> {
    memoset: CM, // CircuitMemoSet
    /// k -> allocated v
    transcript: CircuitTranscript<F>,
    /// k -> prov
    provenances: Option<&'a IndexMap<ZPtr<Tag, F>, ZPtr<Tag, F>>>,
    acc: Option<AllocatedPtr<F>>,
    pub(crate) runtime_data: RD,
}

#[derive(Clone)]
pub struct CoroutineCircuit<'a, F: LurkField, M, Q: Query<F>> {
    query_index: usize,
    rc: usize,
    store: &'a Store<F>,
    runtime_data: &'a Q::RD,
    // `None` for circuit synthesis
    // `Some` for witness generation
    witness_data: Option<WitnessData<'a, F, M>>,
}

#[derive(Clone, Copy)]
struct WitnessData<'a, F: LurkField, M> {
    keys: &'a [Ptr],
    memoset: &'a M,
    provenances: &'a IndexMap<ZPtr<Tag, F>, ZPtr<Tag, F>>,
    next_query_index: usize,
}

impl<'a, F: LurkField, M, Q: Query<F>> CoroutineCircuit<'a, F, M, Q> {
    pub fn blank(
        query_index: usize,
        rc: usize,
        store: &'a Store<F>,
        runtime_data: &'a Q::RD,
    ) -> Self {
        Self {
            query_index,
            store,
            rc,
            runtime_data,
            witness_data: None,
        }
    }

    fn witness_data(&self) -> Option<&WitnessData<'a, F, M>> {
        self.witness_data.as_ref()
    }
}

// TODO: Make this generic rather than specialized to LogMemo.
// That will require a CircuitScopeTrait.
impl<'a, F: LurkField, Q: Query<F>> CoroutineCircuit<'a, F, LogMemo<F>, Q> {
    pub fn new(
        scope: &'a Scope<Q, LogMemo<F>, F>,
        keys: &'a [Ptr],
        query_index: usize,
        next_query_index: usize,
        rc: usize,
    ) -> Self {
        assert!(keys.len() <= rc);
        let memoset = &scope.memoset;
        let provenances = scope.provenances();
        Self {
            rc,
            query_index,
            store: &scope.store,
            runtime_data: &scope.runtime_data,
            witness_data: Some(WitnessData {
                keys,
                memoset,
                provenances,
                next_query_index,
            }),
        }
    }

    // This is a supernova::StepCircuit method.
    // // TODO: we need to create a supernova::StepCircuit that will prove up to a fixed number of queries of a given type.
    pub(crate) fn supernova_synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedPtr<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedPtr<F>>), SynthesisError> {
        let g = &GlobalAllocator::<F>::default();

        assert_eq!(6, z.len());
        let [c, e, k, memoset_acc, transcript, r] = z else {
            unreachable!()
        };

        let multiset = self.witness_data().map(|w| &w.memoset.multiset);
        let memoset = LogMemoCircuit {
            multiset,
            r: r.hash().clone(),
        };
        let provenances = self.witness_data().map(|w| w.provenances);
        let mut circuit_scope: CircuitScope<'_, F, LogMemoCircuit<'_, F>, Q::RD> =
            CircuitScope::new(
                cs,
                g,
                self.store,
                memoset,
                provenances,
                self.runtime_data.clone(),
            );
        circuit_scope.update_from_io(memoset_acc.clone(), transcript.clone(), r);

        let keys: &[Ptr] = self.witness_data().map_or(&[], |w| w.keys);
        for (i, key) in keys
            .iter()
            .map(Some)
            .pad_using(self.rc, |_| None)
            .enumerate()
        {
            let cs = ns!(cs, format!("internal-{i}"));
            circuit_scope.synthesize_prove_key_query::<_, Q>(
                cs,
                g,
                self.store,
                key,
                self.query_index,
            )?;
        }

        let (memoset_acc, transcript, r_num) = circuit_scope.io();
        let r = AllocatedPtr::alloc_tag(ns!(cs, "r"), ExprTag::Cons.to_field(), r_num)?;

        let z_out = vec![c.clone(), e.clone(), k.clone(), memoset_acc, transcript, r];

        let next_pc = AllocatedNum::alloc_infallible(&mut cs.namespace(|| "next_pc"), || {
            let index = self.witness_data().unwrap().next_query_index;
            F::from_u64(index as u64)
        });
        Ok((Some(next_pc), z_out))
    }
}

impl<F: LurkField, Q: Query<F>> Scope<Q, LogMemo<F>, F> {
    pub fn query(&mut self, form: Ptr) -> Ptr {
        let (result, kv_ptr) = self.query_aux(form);

        self.toplevel_insertions.push(kv_ptr);

        result
    }

    fn query_recursively(&mut self, parent: &Q, child: Q) -> Ptr {
        let s = self.store.as_ref();
        let form = child.to_ptr(s);

        self.internal_insertions.push(form);

        let (result, _) = self.query_aux(form);

        self.register_dependency(parent, child);
        result
    }

    fn register_dependency(&mut self, parent: &Q, child: Q) {
        let s = self.store.as_ref();
        let parent_ptr = parent.to_ptr(s);

        self.dependents
            .entry(child.to_ptr(s))
            .and_modify(|parents| {
                parents.insert(parent_ptr);
            })
            .or_insert_with(|| {
                let mut set = HashSet::new();
                set.insert(parent_ptr);
                set
            });

        self.dependencies
            .entry(parent_ptr)
            .and_modify(|children| children.push(child.clone()))
            .or_insert_with(|| vec![child]);
    }

    fn query_aux(&mut self, form: Ptr) -> (Ptr, Ptr) {
        // Ensure base-case queries explicitly contain no dependencies.
        self.dependencies.entry(form).or_insert_with(|| Vec::new());

        let result = self.queries.get(&form).cloned().unwrap_or_else(|| {
            let s = self.store.as_ref();
            let query = Q::from_ptr(&self.runtime_data, s, &form).expect("invalid query");

            let evaluated = query.eval(self);

            self.queries.insert(form, evaluated);
            evaluated
        });
        let s = self.store.as_ref();

        let kv = Transcript::make_kv(s, form, result);

        // FIXME: The memoset should hold the provenances, not the kvs.
        self.memoset.add(kv);

        (result, kv)
    }

    pub(crate) fn finalize_transcript(&mut self) -> Transcript<F> {
        let s = self.store.as_ref();
        let (transcript, insertions) = self.build_transcript();
        self.memoset.finalize_transcript(s, transcript.clone());
        self.unique_inserted_keys = insertions;

        transcript
    }

    fn provenances(&self) -> &IndexMap<ZPtr<Tag, F>, ZPtr<Tag, F>> {
        self.provenances.get_or_init(|| self.compute_provenances())
    }

    // Retain for use when debugging.
    //
    // fn dbg_provenances(&self, store: &Store<F>) {
    //     Self::dbg_provenances_zptrs(store, self.provenances(store));
    // }

    // fn dbg_provenances_ptrs(store: &Store<F>, provenances: &IndexMap<Ptr, Ptr>) {
    //     for provenance in provenances.values() {
    //         dbg!(provenance.fmt_to_string_simple(store));
    //     }
    // }

    // fn dbg_provenances_zptrs(store: &Store<F>, provenances: &IndexMap<ZPtr<Tag, F>, ZPtr<Tag, F>>) {
    //     for (q, provenance) in provenances {
    //         dbg!(
    //             store.to_ptr(q).fmt_to_string_simple(store),
    //             store.to_ptr(provenance).fmt_to_string_simple(store)
    //         );
    //     }
    // }

    fn compute_provenances(&self) -> IndexMap<ZPtr<Tag, F>, ZPtr<Tag, F>> {
        let mut provenances = IndexMap::default();
        let mut ready = HashSet::new();

        let mut missing_dependency_counts: IndexMap<&Ptr, usize> = self
            .queries
            .keys()
            .map(|key| {
                let dep_count = self.dependencies.get(key).map_or(0, |x| x.len());

                if dep_count == 0 {
                    // Queries are ready if they have no missing dependencies.
                    // Initially, this will be the base cases -- which have no dependencies.
                    ready.insert(key);
                }
                (key, dep_count)
            })
            .collect();

        while !ready.is_empty() {
            ready =
                self.extend_provenances(&mut provenances, ready, &mut missing_dependency_counts);
        }

        assert_eq!(
            self.queries.len(),
            provenances.len(),
            "incomplete provenance computation (probably a forbidden cyclic query)"
        );

        let store = self.store.as_ref();
        provenances
            .iter()
            .map(|(k, v)| (store.hash_ptr(k), store.hash_ptr(v)))
            .collect()
    }

    fn extend_provenances<'a>(
        &'a self,
        provenances: &mut IndexMap<Ptr, Ptr>,
        ready: HashSet<&Ptr>,
        missing_dependency_counts: &mut IndexMap<&'a Ptr, usize>,
    ) -> HashSet<&Ptr> {
        let mut next = HashSet::new();
        for query in ready.into_iter() {
            if provenances.get(query).is_some() {
                // Skip if already complete. This should not happen if called by `compute_provenances` when computing
                // all provenances from scratch, but it could happen if we compute more incrementally in the future.
                continue;
            };

            let store = self.store.as_ref();
            let sub_provenances = self
                .dependencies
                .get(query)
                .expect("dependencies missing")
                .iter()
                .map(|dep| provenances.get(&dep.to_ptr(store)).unwrap())
                .cloned()
                .collect::<Vec<_>>();

            let result = self.queries.get(query).expect("result missing");
            let p = Provenance::new(*query, *result, sub_provenances);
            let provenance = p.to_ptr(store);

            // Insert new provenance before decrementing `missing_dependency_counts`.
            provenances.insert(*query, *provenance);

            if let Some(dependents) = self.dependents.get(query) {
                for dependent in dependents {
                    missing_dependency_counts
                        .entry(dependent)
                        .and_modify(|missing_count| {
                            // NOTE: A query only becomes the `dependent` here when one of its dependencies is
                            // processed. Any query with `missing_count` 0 has no unprocessed dependencies to trigger
                            // the following update. Therefore, the underflow guarded against below should never occur
                            // if the implicit topological sort worked correctly. Any failure suggests the algorithm has
                            // been broken accidentally.
                            *missing_count = missing_count
                                .checked_sub(1)
                                .expect("topological sort has been broken; a dependency was processed out of order");
                            if *missing_count == 0 {
                                next.insert(dependent);
                            }
                        });
                }
            };
        }

        next
    }

    fn ensure_transcript_finalized(&mut self) {
        if !self.memoset.is_finalized() {
            self.finalize_transcript();
        }
    }

    fn build_transcript(&self) -> (Transcript<F>, IndexMap<usize, Vec<Ptr>>) {
        let s = self.store.as_ref();
        let mut transcript = Transcript::new(s);

        // k -> kv
        let mut kvs_by_key: IndexMap<Ptr, Ptr> = IndexMap::new();
        let mut unique_keys: IndexMap<usize, Vec<Ptr>> = Default::default();

        let mut record_kv = |kv: &Ptr| {
            let key = s.car_cdr(kv).unwrap().0;
            let kv1 = kvs_by_key.entry(key).or_insert_with(|| {
                let index = Q::from_ptr(&self.runtime_data, s, &key)
                    .expect("bad query")
                    .index(&self.runtime_data);

                // We only add to `unique_keys` inside this closure, which only happens once per key. This accomplishes
                // the 'deduplication' referred to below.
                unique_keys
                    .entry(index)
                    .and_modify(|keys| keys.push(key))
                    .or_insert_with(|| vec![key]);

                *kv
            });

            assert_eq!(*kv, *kv1);
        };

        for kv in &self.toplevel_insertions {
            record_kv(kv);
        }

        self.internal_insertions.iter().for_each(|key| {
            let value = self.queries.get(key).expect("value missing for key");
            let kv = Transcript::make_kv(s, *key, *value);

            record_kv(&kv)
        });

        for kv in self.toplevel_insertions.iter() {
            let provenance = self.provenance_from_kv(*kv).unwrap();
            transcript.add(s, *provenance.to_ptr(s));
        }

        // Then add insertions and removals interleaved, sorted by query type. We interleave insertions and removals
        // because when proving later, each query's proof must record that its subquery proofs are being deferred
        // (insertions) before then proving itself (making use of any subquery results) and removing the now-proved
        // deferral from the MemoSet.
        for index in 0..Q::count(&self.runtime_data) {
            if let Some(keys) = unique_keys.get(&index) {
                let rc = self.rc_for_query(index);

                for chunk in &keys.iter().chunks(rc) {
                    for key in chunk.map(Some).pad_using(rc, |_| None) {
                        let (provenance, count) = if let Some(key) = key {
                            // This should not fail: `kv` was added in `record` above, when the key was added to
                            // `unique_keys`.
                            let kv = kvs_by_key.get(key).expect("kv missing");
                            let count = self.memoset.count(kv);
                            let provenance = self.provenance_from_kv(*kv).unwrap();
                            (provenance, count)
                        } else {
                            (Provenance::dummy(s), 0)
                        };
                        let prov = provenance.to_ptr(s);
                        let prov_count = Transcript::make_provenance_count(s, *prov, count);

                        // Add removal for the query identified by `key`. The queries being removed here were deduplicated
                        // above, so each is removed only once. However, we freely choose the multiplicity (`count`) of the
                        // removal to match the total number of insertions actually made (considering dependencies).
                        transcript.add(s, prov_count);
                    }
                }
            }
        }

        (transcript, unique_keys)
    }

    pub fn synthesize<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
    ) -> Result<(), SynthesisError> {
        self.ensure_transcript_finalized();
        let s = self.store.as_ref();
        // FIXME: Do we need to allocate a new GlobalAllocator here?
        // Is it okay for this memoset circuit to be shared between all CoroutineCircuits?
        let r = self.memoset.allocated_r(ns!(cs, "memoset_allocated_r"));
        let memoset_circuit = LogMemoCircuit {
            multiset: Some(&self.memoset.multiset),
            r,
        };

        let mut circuit_scope = CircuitScope::new(
            ns!(cs, "transcript"),
            g,
            s,
            memoset_circuit.clone(),
            Some(self.provenances()),
            self.runtime_data.clone(),
        );

        circuit_scope.init(cs, g, s);
        {
            circuit_scope.synthesize_insert_toplevel_queries(self, cs, g)?;

            {
                let s = self.store.as_ref();
                let (memoset_acc, transcript, r_num) = circuit_scope.io();
                let r = AllocatedPtr::from_parts(g.alloc_tag(cs, &ExprTag::Num).clone(), r_num);
                let dummy = g.alloc_ptr(cs, &s.intern_nil(), s);
                let mut z = vec![
                    dummy.clone(),
                    dummy.clone(),
                    dummy.clone(),
                    memoset_acc,
                    transcript,
                    r,
                ];
                for (index, keys) in self.unique_inserted_keys.iter() {
                    let cs = ns!(cs, format!("query-index-{index}"));

                    let rc = self.rc_for_query(*index);

                    for (i, chunk) in keys.chunks(rc).enumerate() {
                        // This namespace exists only because we are putting multiple 'chunks' into a single, larger circuit (as a stage in development).
                        // It shouldn't exist, when instead we have only the single NIVC circuit repeated multiple times.
                        let cs = ns!(cs, format!("chunk-{i}"));

                        // `next_query_index` is only relevant for SuperNova
                        let next_query_index = 0;
                        let circuit: CoroutineCircuit<'_, F, LogMemo<F>, Q> =
                            CoroutineCircuit::new(self, chunk, *index, next_query_index, rc);

                        let (_next_pc, z_out) = circuit.supernova_synthesize(cs, &z)?;
                        {
                            let memoset_acc = &z_out[3];
                            let transcript = &z_out[4];
                            let r = &z_out[5];

                            circuit_scope.update_from_io(
                                memoset_acc.clone(),
                                transcript.clone(),
                                r,
                            );

                            z = z_out;
                        }
                    }
                }
            }
        }

        circuit_scope.finalize(cs, g);

        Ok(())
    }

    fn rc_for_query(&self, _index: usize) -> usize {
        self.default_rc
    }
}

impl<'a, F: LurkField, RD> CircuitScope<'a, F, LogMemoCircuit<'a, F>, RD> {
    fn new<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        memoset: LogMemoCircuit<'a, F>,
        provenances: Option<&'a IndexMap<ZPtr<Tag, F>, ZPtr<Tag, F>>>,
        runtime_data: RD,
    ) -> Self {
        Self {
            memoset,
            provenances,
            transcript: CircuitTranscript::new(cs, g, s),
            acc: Default::default(),
            runtime_data,
        }
    }

    fn init<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, g: &GlobalAllocator<F>, s: &Store<F>) {
        self.acc =
            Some(AllocatedPtr::alloc_constant(ns!(cs, "acc"), s.hash_ptr(&s.num_u64(0))).unwrap());

        self.transcript = CircuitTranscript::new(cs, g, s);
    }

    fn io(&self) -> (AllocatedPtr<F>, AllocatedPtr<F>, AllocatedNum<F>) {
        (
            self.acc.as_ref().unwrap().clone(),
            self.transcript.acc.clone(),
            self.memoset.r.clone(),
        )
    }

    fn update_from_io(
        &mut self,
        acc: AllocatedPtr<F>,
        transcript: AllocatedPtr<F>,
        r: &AllocatedPtr<F>,
    ) {
        self.acc = Some(acc);
        self.transcript.acc = transcript;
        self.memoset.r = r.hash().clone();
    }

    fn synthesize_insert_query<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        acc: &AllocatedPtr<F>,
        transcript: &CircuitTranscript<F>,
        provenance: &AllocatedPtr<F>,
    ) -> Result<(AllocatedPtr<F>, CircuitTranscript<F>), SynthesisError> {
        let new_transcript = transcript.add(ns!(cs, "new_transcript"), g, s, provenance)?;

        let acc_v = acc.hash();

        let new_acc_v = self
            .memoset
            .synthesize_add(ns!(cs, "new_acc_v"), acc_v, provenance)?;

        let new_acc =
            AllocatedPtr::alloc_tag(ns!(cs, "new_acc"), ExprTag::Num.to_field(), new_acc_v)?;

        Ok((new_acc, new_transcript))
    }

    fn synthesize_insert_internal_query<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        acc: &AllocatedPtr<F>,
        provenance: &AllocatedPtr<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let acc_v = acc.hash();

        let new_acc_v = self
            .memoset
            .synthesize_add(ns!(cs, "new_acc_v"), acc_v, provenance)?;

        let new_acc =
            AllocatedPtr::alloc_tag(ns!(cs, "new_acc"), ExprTag::Num.to_field(), new_acc_v)?;

        Ok(new_acc)
    }

    fn synthesize_remove<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        acc: &AllocatedPtr<F>,
        transcript: &CircuitTranscript<F>,
        key: &AllocatedPtr<F>,
        value: &AllocatedPtr<F>,
        provenance: &AllocatedPtr<F>,
        not_dummy: &Boolean,
    ) -> Result<(AllocatedPtr<F>, CircuitTranscript<F>), SynthesisError> {
        let raw_count = match not_dummy.get_value() {
            // dummy case: count must be zero -- since we will actually constrain a removal
            Some(false) => 0,
            _ => match (key.get_value(), value.get_value()) {
                (Some(k), Some(v)) => {
                    // FIXME: Memoset should hold the actual provenances, not the kvs.
                    let kv = s.cons(s.to_ptr(&k), s.to_ptr(&v));
                    self.memoset.count(&kv) as u64
                }
                _ => unreachable!(),
            },
        };

        let dummy_provenance =
            g.alloc_ptr(ns!(cs, "dummy_query"), Provenance::dummy(s).to_ptr(s), s);

        let effective_provenance = AllocatedPtr::pick(
            ns!(cs, "effective_provenance"),
            not_dummy,
            provenance,
            &dummy_provenance,
        )?;

        let (provenance_count, count) = CircuitTranscript::make_provenance_count(
            ns!(cs, "kv count"),
            g,
            s,
            &effective_provenance,
            raw_count,
        )?;

        let new_transcript =
            transcript.add(ns!(cs, "new_removal_transcript"), g, s, &provenance_count)?;

        let new_acc_v = self.memoset.synthesize_remove_n(
            ns!(cs, "new_acc_v"),
            acc.hash(),
            provenance,
            &count,
        )?;

        let new_acc =
            AllocatedPtr::alloc_tag(ns!(cs, "new_acc"), ExprTag::Num.to_field(), new_acc_v)?;
        Ok((new_acc, new_transcript))
    }

    fn finalize<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, _g: &GlobalAllocator<F>) {
        let r = self.memoset.allocated_r();
        enforce_equal(cs, || "r_matches_transcript", self.transcript.r(), &r);
        enforce_equal_zero(cs, || "acc_is_zero", self.acc.clone().unwrap().hash());
    }

    fn synthesize_query<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        key: &AllocatedPtr<F>,
        acc: &AllocatedPtr<F>,
        transcript: &CircuitTranscript<F>,
        not_dummy: &Boolean,
    ) -> Result<
        (
            (AllocatedPtr<F>, AllocatedPtr<F>),
            AllocatedPtr<F>,
            CircuitTranscript<F>,
        ),
        SynthesisError,
    > {
        let ((result, provenance), new_acc, new_insertion_transcript) =
            self.synthesize_query_aux(cs, g, store, key, acc, Some(transcript), not_dummy, true)?;

        Ok((
            (result, provenance),
            new_acc,
            new_insertion_transcript.unwrap(),
        ))
    }

    pub(crate) fn synthesize_internal_query<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        key: &AllocatedPtr<F>,
        acc: &AllocatedPtr<F>,
        not_dummy: &Boolean,
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError> {
        let ((result, provenance), new_acc, new_insertion_transcript) =
            self.synthesize_query_aux(cs, g, store, key, acc, None, not_dummy, false)?;

        assert!(new_insertion_transcript.is_none());

        Ok(((result, provenance), new_acc))
    }

    fn synthesize_query_aux<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        key: &AllocatedPtr<F>,
        acc: &AllocatedPtr<F>,
        transcript: Option<&CircuitTranscript<F>>,
        not_dummy: &Boolean, // TODO: use this more deeply?
        is_toplevel: bool,
    ) -> Result<
        (
            (AllocatedPtr<F>, AllocatedPtr<F>),
            AllocatedPtr<F>,
            Option<CircuitTranscript<F>>,
        ),
        SynthesisError,
    > {
        let provenance = AllocatedPtr::alloc(ns!(cs, "provenance"), || {
            Ok(if not_dummy.get_value() == Some(true) {
                *key.get_value()
                    .and_then(|k| self.provenances.unwrap().get(&k))
                    .ok_or(SynthesisError::AssignmentMissing)?
            } else {
                // Dummy value that will not be used.
                store.hash_ptr(&store.intern_nil())
            })
        })?;

        let (_query, result, _deps) = deconstruct_provenance(
            ns!(cs, "decons provenance"),
            store,
            not_dummy,
            provenance.hash(),
        )?;

        if is_toplevel {
            let (new_acc, new_insertion_transcript) = self.synthesize_insert_query(
                cs,
                g,
                store,
                acc,
                transcript.expect("transcript missing"),
                &provenance,
            )?;
            Ok((
                (result, provenance),
                new_acc,
                Some(new_insertion_transcript),
            ))
        } else {
            let new_acc = self.synthesize_insert_internal_query(cs, acc, &provenance)?;
            Ok(((result, provenance), new_acc, None))
        }
    }

    fn synthesize_insert_toplevel_queries<CS: ConstraintSystem<F>, Q: Query<F>>(
        &mut self,
        scope: &Scope<Q, LogMemo<F>, F>,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
    ) -> Result<(), SynthesisError> {
        for (i, kv) in scope.toplevel_insertions.iter().enumerate() {
            let s = scope.store.as_ref();
            let cs = ns!(cs, format!("toplevel_insertion-{i}"));
            let (key, value) = s.car_cdr(kv).expect("kv missing");
            // NOTE: This is an unconstrained allocation, but when actually hooked up to Lurk reduction, it must be
            // constrained appropriately.
            let allocated_key =
                AllocatedPtr::alloc(ns!(cs, "allocated_key"), || Ok(s.hash_ptr(&key))).unwrap();
            // NOTE: The returned value is unused here, but when actually hooked up to Lurk reduction, it must be used
            // as the result of evaluating the query.
            let _allocated_value =
                self.synthesize_toplevel_query(cs, g, s, i, &allocated_key, value)?;
        }
        Ok(())
    }

    fn synthesize_toplevel_query<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        i: usize,
        allocated_key: &AllocatedPtr<F>,
        value: Ptr,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let cs = ns!(cs, format!("toplevel-{i}"));

        let acc = self.acc.clone().unwrap();
        let insertion_transcript = self.transcript.clone();

        let ((val, _provenance), new_acc, new_transcript) = self.synthesize_query(
            cs,
            g,
            s,
            allocated_key,
            &acc,
            &insertion_transcript,
            &Boolean::Constant(true),
        )?;

        if let Some(val_ptr) = val.get_value().map(|x| s.to_ptr(&x)) {
            assert_eq!(value, val_ptr);
        }

        self.acc = Some(new_acc);
        self.transcript = new_transcript;
        Ok(val)
    }

    fn synthesize_prove_key_query<CS: ConstraintSystem<F>, Q: Query<F, RD = RD>>(
        &mut self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        key: Option<&Ptr>,
        index: usize,
    ) -> Result<(), SynthesisError> {
        let not_dummy = Boolean::Is(AllocatedBit::alloc(
            cs.namespace(|| "not_dummy"),
            Some(key.is_some()),
        )?);

        let circuit_query = if let Some(key) = key {
            let query = Q::from_ptr(&self.runtime_data, s, key).unwrap();
            assert_eq!(index, query.index(&self.runtime_data));
            query.to_circuit(ns!(cs, "circuit_query"), s)
        } else {
            let query = Q::dummy_from_index(&self.runtime_data, s, index);
            query.to_circuit(ns!(cs, "circuit_query"), s)
        };

        let allocated_key = circuit_query.synthesize_query(ns!(cs, "allocated_key"), g, s)?;

        self.synthesize_prove_query::<_, Q::CQ>(
            cs,
            g,
            s,
            &allocated_key,
            &circuit_query,
            &not_dummy,
        )?;
        Ok(())
    }

    fn synthesize_prove_query<CS: ConstraintSystem<F>, CQ: CircuitQuery<F, RD = RD>>(
        &mut self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        allocated_key: &AllocatedPtr<F>,
        circuit_query: &CQ,
        not_dummy: &Boolean,
    ) -> Result<(), SynthesisError> {
        let acc = self.acc.clone().unwrap();

        let ((val, provenance), new_acc) = circuit_query
            .synthesize_eval(ns!(cs, "eval"), g, s, self, &acc, allocated_key)
            .unwrap();

        let (new_acc, new_transcript) = self.synthesize_remove(
            cs,
            g,
            s,
            &new_acc,
            &self.transcript,
            allocated_key,
            &val,
            &provenance,
            not_dummy,
        )?;

        // Prover can choose non-deterministically whether or not a given query is a dummy, to allow for padding.
        let final_acc = AllocatedPtr::pick(
            ns!(cs, "final_acc"),
            not_dummy,
            &new_acc,
            self.acc.as_ref().expect("acc missing"),
        )?;

        self.transcript = new_transcript;
        self.acc = Some(final_acc);
        Ok(())
    }

    #[allow(dead_code)]
    fn dbg_transcript(&self, s: &Store<F>) {
        self.transcript.dbg(s);
    }
}

pub trait CircuitMemoSet<F: LurkField>: Clone {
    fn synthesize_remove_n<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        acc: &AllocatedNum<F>,
        kv: &AllocatedPtr<F>,
        count: &AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError>;

    fn allocated_r(&self) -> AllocatedNum<F>;

    // x is H(k,v) = hash part of (cons k v)
    fn synthesize_map_to_element<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        x: AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError>;

    fn synthesize_add<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        acc: &AllocatedNum<F>,
        kv: &AllocatedPtr<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError>;

    fn count(&self, form: &Ptr) -> usize;
}

pub trait MemoSet<F: LurkField>: Clone {
    fn is_finalized(&self) -> bool;
    fn finalize_transcript(&mut self, s: &Store<F>, transcript: Transcript<F>);
    fn r(&self) -> Option<&F>;
    fn map_to_element(&self, x: F) -> Option<F>;
    fn add(&mut self, kv: Ptr);
    fn count(&self, form: &Ptr) -> usize;
}

#[derive(Debug, Clone)]
pub struct LogMemo<F: LurkField> {
    // {kv, ...}
    multiset: MultiSet<Ptr>,
    r: OnceCell<F>,
    transcript: OnceCell<Transcript<F>>,

    // Allocated only after transcript has been finalized.
    allocated_r: OnceCell<Option<AllocatedNum<F>>>,
}

#[derive(Debug, Clone)]
pub struct LogMemoCircuit<'a, F: LurkField> {
    multiset: Option<&'a MultiSet<Ptr>>,
    r: AllocatedNum<F>,
}

impl<F: LurkField> Default for LogMemo<F> {
    fn default() -> Self {
        // Be explicit.
        Self {
            multiset: MultiSet::new(),
            r: Default::default(),
            transcript: Default::default(),
            allocated_r: Default::default(),
        }
    }
}
impl<F: LurkField> LogMemo<F> {
    fn allocated_r<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> AllocatedNum<F> {
        self.allocated_r
            .get_or_init(|| {
                self.r()
                    .map(|r| AllocatedNum::alloc_infallible(ns!(cs, "r"), || *r))
            })
            .clone()
            .unwrap()
    }

    fn acc_add(&self, acc: &Ptr, kv: &Ptr, store: &Store<F>) -> Ptr {
        let acc_num = store.expect_f(acc.get_atom().unwrap());
        let kv_num = store.hash_raw_ptr(kv.raw()).0;
        let element = self.map_to_element(kv_num).unwrap();
        store.num(*acc_num + element)
    }
}

impl<F: LurkField> MemoSet<F> for LogMemo<F> {
    fn count(&self, form: &Ptr) -> usize {
        self.multiset.get(form).unwrap_or(0)
    }

    fn is_finalized(&self) -> bool {
        self.transcript.get().is_some()
    }
    fn finalize_transcript(&mut self, s: &Store<F>, transcript: Transcript<F>) {
        let r = transcript.r(s);

        self.r.set(r).expect("r has already been set");
        self.transcript
            .set(transcript)
            .expect("transcript already finalized");
    }

    fn r(&self) -> Option<&F> {
        self.r.get()
    }

    // x is H(k,v) = hash part of (cons k v)
    fn map_to_element(&self, x: F) -> Option<F> {
        self.r().and_then(|r| {
            let d = *r + x;
            d.invert().into()
        })
    }

    fn add(&mut self, kv: Ptr) {
        self.multiset.add(kv);
    }
}

impl<'a, F: LurkField> CircuitMemoSet<F> for LogMemoCircuit<'a, F> {
    fn allocated_r(&self) -> AllocatedNum<F> {
        self.r.clone()
    }

    fn synthesize_add<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        acc: &AllocatedNum<F>,
        provenance: &AllocatedPtr<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let provenance_num = provenance.hash().clone();
        let element = self.synthesize_map_to_element(ns!(cs, "element"), provenance_num)?;
        acc.add(ns!(cs, "add to acc"), &element)
    }

    fn synthesize_remove_n<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        acc: &AllocatedNum<F>,
        provenance: &AllocatedPtr<F>,
        count: &AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let provenance_num = provenance.hash().clone();
        let element = self.synthesize_map_to_element(ns!(cs, "element"), provenance_num)?;
        let scaled = element.mul(ns!(cs, "scaled"), count)?;
        sub(ns!(cs, "add to acc"), acc, &scaled)
    }

    // x is H(provenance) = hash part of (cons (cons k v) sub-provenances)
    // 1 / r + x
    fn synthesize_map_to_element<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        x: AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let r = self.r.clone();
        let r_plus_x = r.add(ns!(cs, "r+x"), &x)?;

        invert(ns!(cs, "invert(r+x)"), &r_plus_x)
    }

    fn count(&self, form: &Ptr) -> usize {
        self.multiset.and_then(|m| m.get(form)).unwrap_or(0)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::state::State;
    use bellpepper_core::{test_cs::TestConstraintSystem, Comparable};
    use demo::DemoQuery;
    use expect_test::{expect, Expect};
    use halo2curves::bn256::Fr as F;
    use std::default::Default;

    #[test]
    fn test_query() {
        test_query_aux(
            expect!["9451"],
            expect!["9497"],
            expect!["10034"],
            expect!["10087"],
            1,
        );
        test_query_aux(
            expect!["11191"],
            expect!["11241"],
            expect!["11774"],
            expect!["11831"],
            3,
        );
        test_query_aux(
            expect!["18239"],
            expect!["18316"],
            expect!["18822"],
            expect!["18906"],
            10,
        )
    }

    fn test_query_aux(
        expected_constraints_simple: Expect,
        expected_aux_simple: Expect,
        expected_constraints_compound: Expect,
        expected_aux_compound: Expect,
        circuit_query_rc: usize,
    ) {
        let s = Arc::new(Store::<F>::default());
        let state = State::init_lurk_state();

        let fact_4 = s.read_with_default_state("(factorial . 4)").unwrap();
        let fact_3 = s.read_with_default_state("(factorial . 3)").unwrap();

        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };

        let mut scope: Scope<DemoQuery<F>, LogMemo<F>, F> =
            Scope::new(circuit_query_rc, s.clone(), ());
        {
            scope.query(fact_4);

            for (k, v) in scope.queries.iter() {
                println!("k: {}", k.fmt_to_string(&s, &state));
                println!("v: {}", v.fmt_to_string(&s, &state));
            }
            // Factorial 4 will memoize calls to:
            // fact(4), fact(3), fact(2), fact(1), and fact(0)
            assert_eq!(5, scope.queries.len());
            assert_eq!(1, scope.toplevel_insertions.len());
            assert_eq!(4, scope.internal_insertions.len());

            scope.finalize_transcript();

            let cs = &mut TestConstraintSystem::new();
            let g = &GlobalAllocator::default();

            scope.synthesize(cs, g).unwrap();

            println!(
                "transcript: {}",
                scope
                    .memoset
                    .transcript
                    .get()
                    .unwrap()
                    .fmt_to_string_simple(&s)
            );

            expect_eq(cs.num_constraints(), expected_constraints_simple);
            expect_eq(cs.aux().len(), expected_aux_simple);

            let unsat = cs.which_is_unsatisfied();

            if unsat.is_some() {
                dbg!(unsat);
            }
            assert!(cs.is_satisfied());
        }

        {
            let mut scope: Scope<DemoQuery<F>, LogMemo<F>, F> =
                Scope::new(circuit_query_rc, s.clone(), ());
            scope.query(fact_4);
            scope.query(fact_3);

            // // No new queries.
            assert_eq!(5, scope.queries.len());
            // // One new top-level insertion.
            assert_eq!(2, scope.toplevel_insertions.len());
            // // No new internal insertions.
            assert_eq!(4, scope.internal_insertions.len());

            scope.finalize_transcript();

            let cs = &mut TestConstraintSystem::new();
            let g = &GlobalAllocator::default();

            scope.synthesize(cs, g).unwrap();

            println!(
                "transcript: {}",
                scope
                    .memoset
                    .transcript
                    .get()
                    .unwrap()
                    .fmt_to_string_simple(&s)
            );

            expect_eq(cs.num_constraints(), expected_constraints_compound);
            expect_eq(cs.aux().len(), expected_aux_compound);

            let unsat = cs.which_is_unsatisfied();
            if unsat.is_some() {
                dbg!(unsat);
            }
            assert!(cs.is_satisfied());
        }
    }
}
