//! The `memoset` module implements a MemoSet.

use std::collections::HashMap;
use std::marker::PhantomData;

use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use itertools::Itertools;
use once_cell::sync::OnceCell;

use super::gadgets::construct_cons;
use crate::circuit::gadgets::{
    constraints::{enforce_equal, enforce_equal_zero, invert, sub},
    pointer::AllocatedPtr,
};
use crate::field::LurkField;
use crate::lem::circuit::GlobalAllocator;
use crate::lem::tag::Tag;
use crate::lem::{pointers::Ptr, store::Store};
use crate::tag::{ExprTag, Tag as XTag};
use crate::z_ptr::ZPtr;

use multiset::MultiSet;
use query::{CircuitQuery, DemoQuery, Query};

mod multiset;
mod query;

type ScopeQuery<F> = DemoQuery<F>;
type ScopeCircuitQuery<F> = <DemoQuery<F> as Query<F>>::C;

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

    #[allow(dead_code)]
    fn zptr(&self, s: &Store<F>) -> ZPtr<Tag, F> {
        s.hash_ptr(&self.acc)
    }

    fn add(&mut self, s: &Store<F>, item: Ptr) {
        self.acc = s.cons(item, self.acc);
    }

    fn make_kv(s: &Store<F>, key: Ptr, value: Ptr) -> Ptr {
        s.cons(key, value)
    }

    fn make_kv_count(s: &Store<F>, kv: Ptr, count: usize) -> Ptr {
        let count_num = s.num(F::from_u64(count as u64));
        s.cons(kv, count_num)
    }

    #[allow(dead_code)]
    fn dbg(&self, s: &Store<F>) {
        dbg!(self.acc.fmt_to_string_simple(s));
        // dbg!(transcript.fmt_to_string_simple(s));
        tracing::debug!("transcript: {}", self.acc.fmt_to_string_simple(s));
    }

    fn fmt_to_string_simple(&self, s: &Store<F>) -> String {
        self.acc.fmt_to_string_simple(s)
    }
}

#[derive(Debug, Default)]
/// A `Scope` tracks the queries made while evaluating, including the subqueries that result from evaluating other
/// queries -- then makes use of the bookkeeping performed at evaluation time to synthesize proof of each query
/// performed.
pub struct Scope<F, Q, M> {
    memoset: M,
    /// k => v
    queries: HashMap<Ptr, Ptr>,
    /// k => ordered subqueries
    dependencies: HashMap<Ptr, Vec<Q>>,
    /// kv pairs
    toplevel_insertions: Vec<Ptr>,
    /// internally-inserted keys
    internal_insertions: Vec<Ptr>,
    /// unique keys
    all_insertions: Vec<Ptr>,
    _p: PhantomData<(F, Q)>,
}

impl<F: LurkField> Default for Scope<F, ScopeQuery<F>, LogMemo<F>> {
    fn default() -> Self {
        Self {
            memoset: Default::default(),
            queries: Default::default(),
            dependencies: Default::default(),
            toplevel_insertions: Default::default(),
            internal_insertions: Default::default(),
            all_insertions: Default::default(),
            _p: Default::default(),
        }
    }
}

pub struct CircuitScope<F: LurkField, Q: Query<F>, M: MemoSet<F>> {
    memoset: M,
    /// k -> v
    queries: HashMap<ZPtr<Tag, F>, ZPtr<Tag, F>>,
    /// k -> allocated v
    queries_alloc: HashMap<ZPtr<Tag, F>, AllocatedPtr<F>>,
    transcript: Option<AllocatedPtr<F>>,
    acc: Option<AllocatedPtr<F>>,
    _p: PhantomData<Q>,
}

impl<F: LurkField> Scope<F, ScopeQuery<F>, LogMemo<F>> {
    pub fn query(&mut self, s: &Store<F>, form: Ptr) -> Ptr {
        let (response, kv_ptr) = self.query_aux(s, form);

        self.toplevel_insertions.push(kv_ptr);

        response
    }

    fn query_recursively(
        &mut self,
        s: &Store<F>,
        parent: &ScopeQuery<F>,
        child: ScopeQuery<F>,
    ) -> Ptr {
        let form = child.to_ptr(s);
        self.internal_insertions.push(form);

        let (response, _) = self.query_aux(s, form);

        self.dependencies
            .entry(parent.to_ptr(s))
            .and_modify(|children| children.push(child.clone()))
            .or_insert_with(|| vec![child]);

        response
    }

    fn query_aux(&mut self, s: &Store<F>, form: Ptr) -> (Ptr, Ptr) {
        let response = self.queries.get(&form).cloned().unwrap_or_else(|| {
            let query = ScopeQuery::from_ptr(s, &form).expect("invalid query");

            let evaluated = query.eval(s, self);

            self.queries.insert(form, evaluated);
            evaluated
        });

        let kv = Transcript::make_kv(s, form, response);
        self.memoset.add(kv);

        (response, kv)
    }

    fn finalize_transcript(&mut self, s: &Store<F>) -> Transcript<F> {
        let (transcript, insertions) = self.build_transcript(s);
        self.memoset.finalize_transcript(s, transcript.clone());
        self.all_insertions = insertions;
        transcript
    }

    fn ensure_transcript_finalized(&mut self, s: &Store<F>) {
        if !self.memoset.is_finalized() {
            self.finalize_transcript(s);
        }
    }

    fn build_transcript(&self, s: &Store<F>) -> (Transcript<F>, Vec<Ptr>) {
        let mut transcript = Transcript::new(s);

        let internal_insertions_kv = self.internal_insertions.iter().map(|key| {
            let value = self.queries.get(key).expect("value missing for key");
            Transcript::make_kv(s, *key, *value)
        });

        let mut insertions =
            Vec::with_capacity(self.toplevel_insertions.len() + self.internal_insertions.len());
        insertions.extend(&self.toplevel_insertions);
        insertions.extend(internal_insertions_kv);

        // Sort insertions by query type (index) for processing. This is because the transcript will be constructed
        // sequentially by the circuits, and we potentially batch queries of the same type in a single coprocessor
        // circuit.
        insertions.sort_by_key(|kv| {
            let (key, _) = s.car_cdr(kv).unwrap();

            ScopeQuery::<F>::from_ptr(s, &key)
                .expect("invalid query")
                .index()
        });

        for kv in self.toplevel_insertions.iter() {
            transcript.add(s, *kv);
        }

        // Then add insertions and removals interleaved, sorted by query type. We interleave insertions and removals
        // because when proving later, each query's proof must record that its subquery proofs are being deferred
        // (insertions) before then proving itself (making use of any subquery results) and removing the now-proved
        // deferral from the MemoSet.
        let unique_keys = insertions
            .iter()
            .dedup() // We need to process every key's dependencies once.
            .map(|kv| {
                let key = s.car_cdr(kv).unwrap().0;

                if let Some(dependencies) = self.dependencies.get(&key) {
                  dependencies
                        .iter()
                        .for_each(|dependency| {
                            let k = dependency.to_ptr(s);
                            let v = self
                                .queries
                                .get(&k)
                                .expect("value missing for dependency key");
                            // Add an insertion for each dependency (subquery) of the query identified by `key`. Notice
                            // that these keys might already have been inserted before, but we need to repeat if so
                            // because the proof must do so each time a query is used.
                            let kv= Transcript::make_kv(s, k, *v);
                              transcript.add(s, kv)
                        })
                };
                let count = self.memoset.count(kv);
                let kv_count = Transcript::make_kv_count(s, *kv, count);

                // Add removal for the query identified by `key`. The queries being removed here were deduplicated
                // above, so each is removed only once. However, we freely choose the multiplicity (`count`) of the
                // removal to match the total number of insertions actually made (considering dependencies).
                transcript.add(s, kv_count);

                key
            })
            .collect::<Vec<_>>();

        (transcript, unique_keys)
    }

    pub fn synthesize<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &mut GlobalAllocator<F>,
        s: &Store<F>,
    ) -> Result<(), SynthesisError> {
        self.ensure_transcript_finalized(s);

        {
            let circuit_scope = &mut CircuitScope::from_scope(s, self);
            circuit_scope.init(cs, g, s);
            {
                self.synthesize_insert_toplevel_queries(circuit_scope, cs, g, s)?;
                self.synthesize_prove_all_queries(circuit_scope, cs, g, s)?;
            }
            circuit_scope.finalize(cs, g);
            Ok(())
        }
    }

    fn synthesize_insert_toplevel_queries<CS: ConstraintSystem<F>>(
        &mut self,
        circuit_scope: &mut CircuitScope<F, ScopeQuery<F>, LogMemo<F>>,
        cs: &mut CS,
        g: &mut GlobalAllocator<F>,
        s: &Store<F>,
    ) -> Result<(), SynthesisError> {
        for (i, kv) in self.toplevel_insertions.iter().enumerate() {
            circuit_scope.synthesize_toplevel_query(cs, g, s, i, kv)?;
        }
        Ok(())
    }

    fn synthesize_prove_all_queries<CS: ConstraintSystem<F>>(
        &mut self,
        circuit_scope: &mut CircuitScope<F, ScopeQuery<F>, LogMemo<F>>,
        cs: &mut CS,
        g: &mut GlobalAllocator<F>,
        s: &Store<F>,
    ) -> Result<(), SynthesisError> {
        for (i, kv) in self.all_insertions.iter().enumerate() {
            circuit_scope.synthesize_prove_query(cs, g, s, i, kv)?;
        }
        Ok(())
    }
}

impl<F: LurkField, Q: Query<F>> CircuitScope<F, Q, LogMemo<F>> {
    fn from_scope(s: &Store<F>, scope: &Scope<F, Q, LogMemo<F>>) -> Self {
        let queries = scope
            .queries
            .iter()
            .map(|(k, v)| (s.hash_ptr(k), s.hash_ptr(v)))
            .collect();
        Self {
            memoset: scope.memoset.clone(),
            queries,
            queries_alloc: Default::default(),
            transcript: Default::default(),
            acc: Default::default(),
            _p: Default::default(),
        }
    }

    fn init<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &mut GlobalAllocator<F>,
        s: &Store<F>,
    ) {
        g.alloc_tag(cs, &ExprTag::Cons);
        g.alloc_z_ptr(cs, s.hash_ptr(&s.intern_nil()));

        self.acc = Some(
            AllocatedPtr::alloc_constant(&mut cs.namespace(|| "acc"), s.hash_ptr(&s.num_u64(0)))
                .unwrap(),
        );
        let nil = s.intern_nil();
        let allocated_nil = g.alloc_ptr(cs, &nil, s);

        self.transcript = Some(allocated_nil.clone());
    }

    fn synthesize_insert_query<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        acc: &AllocatedPtr<F>,
        transcript: &AllocatedPtr<F>,
        key: &AllocatedPtr<F>,
        value: &AllocatedPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
        let kv = construct_cons(&mut cs.namespace(|| "kv"), g, s, key, value)?;
        let new_transcript = construct_cons(
            &mut cs.namespace(|| "new_transcript"),
            g,
            s,
            &kv,
            transcript,
        )?;

        let acc_v = acc.hash();

        let new_acc_v =
            self.memoset
                .synthesize_add(&mut cs.namespace(|| "new_acc_v"), acc_v, &kv)?;

        let new_acc = AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "new_acc"),
            ExprTag::Num.to_field(),
            new_acc_v,
        )?;

        Ok((new_acc, new_transcript))
    }

    // TODO: Rename
    fn synthesize_remove_n<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        acc: &AllocatedPtr<F>,
        transcript: &AllocatedPtr<F>,
        key: &AllocatedPtr<F>,
        value: &AllocatedPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
        let kv = construct_cons(&mut cs.namespace(|| "kv"), g, s, key, value)?;
        let count = {
            // Get kv zptr or use Nil as arbitrary dummy.
            let zptr = kv.get_value().unwrap_or(s.hash_ptr(&s.intern_nil()));
            AllocatedNum::alloc(&mut cs.namespace(|| "count"), || {
                Ok(F::from_u64(self.memoset.count(&s.to_ptr(&zptr)) as u64))
            })?
        };
        let count_ptr = AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "count_ptr"),
            ExprTag::Num.to_field(),
            count.clone(),
        )?;

        let kv_count = construct_cons(&mut cs.namespace(|| "kv_count"), g, s, &kv, &count_ptr)?;

        let new_transcript = construct_cons(
            &mut cs.namespace(|| "new_removal_transcript"),
            g,
            s,
            &kv_count,
            transcript,
        )?;

        let new_acc_v = self.memoset.synthesize_remove_n(
            &mut cs.namespace(|| "new_acc_v"),
            acc.hash(),
            &kv,
            &count,
        )?;

        let new_acc = AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "new_acc"),
            ExprTag::Num.to_field(),
            new_acc_v,
        )?;
        Ok((new_acc, new_transcript))
    }

    fn finalize<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, _g: &mut GlobalAllocator<F>) {
        let r = self.memoset.allocated_r(cs);
        enforce_equal(
            cs,
            || "r_matches_transcript",
            self.transcript.clone().unwrap().hash(),
            &r,
        );
        enforce_equal_zero(cs, || "acc_is_zero", self.acc.clone().unwrap().hash());
    }

    fn synthesize_query<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        key: &AllocatedPtr<F>,
        acc: &AllocatedPtr<F>,
        transcript: &AllocatedPtr<F>,
        not_dummy: &Boolean, // TODO: use this more deeply?
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
        let value = key
            .get_value()
            .map(|k| {
                self.queries_alloc
                    .entry(k)
                    .or_insert_with(|| {
                        AllocatedPtr::alloc(&mut cs.namespace(|| "value"), || {
                            Ok(if not_dummy.get_value() == Some(true) {
                                *self
                                    .queries
                                    .get(&k)
                                    .ok_or(SynthesisError::AssignmentMissing)?
                            } else {
                                // Dummy value that will not be used.
                                k
                            })
                        })
                        .unwrap()
                    })
                    .clone()
            })
            .ok_or(SynthesisError::AssignmentMissing)?;

        let (new_acc, new_insertion_transcript) =
            self.synthesize_insert_query(cs, g, store, acc, transcript, key, &value)?;

        Ok((value, new_acc, new_insertion_transcript))
    }
}

impl<F: LurkField> CircuitScope<F, ScopeQuery<F>, LogMemo<F>> {
    fn synthesize_toplevel_query<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &mut GlobalAllocator<F>,
        s: &Store<F>,
        i: usize,
        kv: &Ptr,
    ) -> Result<(), SynthesisError> {
        let (key, value) = s.car_cdr(kv).unwrap();
        let cs = &mut cs.namespace(|| format!("toplevel-{i}"));
        let allocated_key = AllocatedPtr::alloc(&mut cs.namespace(|| "allocated_key"), || {
            Ok(s.hash_ptr(&key))
        })
        .unwrap();

        let acc = self.acc.clone().unwrap();
        let insertion_transcript = self.transcript.clone().unwrap();

        let (val, new_acc, new_transcript) = self.synthesize_query(
            cs,
            g,
            s,
            &allocated_key,
            &acc,
            &insertion_transcript,
            &Boolean::Constant(true),
        )?;

        if let Some(val_ptr) = val.get_value().map(|x| s.to_ptr(&x)) {
            assert_eq!(value, val_ptr);
        }

        self.acc = Some(new_acc);
        self.transcript = Some(new_transcript);
        Ok(())
    }

    fn synthesize_prove_query<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        g: &mut GlobalAllocator<F>,
        s: &Store<F>,
        i: usize,
        key: &Ptr,
    ) -> Result<(), SynthesisError> {
        let cs = &mut cs.namespace(|| format!("internal-{i}"));

        let allocated_key =
            AllocatedPtr::alloc(
                &mut cs.namespace(|| "allocated_key"),
                || Ok(s.hash_ptr(key)),
            )
            .unwrap();

        let circuit_query =
            ScopeCircuitQuery::from_ptr(&mut cs.namespace(|| "circuit_query"), s, key).unwrap();

        let acc = self.acc.clone().unwrap();
        let transcript = self.transcript.clone().unwrap();

        let (val, new_acc, new_transcript) = circuit_query
            .expect("not a query form")
            .synthesize_eval(&mut cs.namespace(|| "eval"), g, s, self, &acc, &transcript)
            .unwrap();

        let (new_acc, new_transcript) =
            self.synthesize_remove_n(cs, g, s, &new_acc, &new_transcript, &allocated_key, &val)?;

        self.acc = Some(new_acc);
        self.transcript = Some(new_transcript);

        Ok(())
    }

    #[allow(dead_code)]
    fn dbg_transcript(&self, s: &Store<F>) {
        let z = self.transcript.clone().unwrap().get_value::<Tag>().unwrap();
        let transcript = s.to_ptr(&z);
        // dbg!(transcript.fmt_to_string_simple(s));
        tracing::debug!("transcript: {}", transcript.fmt_to_string_simple(s));
    }
}

pub trait MemoSet<F: LurkField>: Clone {
    fn is_finalized(&self) -> bool;
    fn finalize_transcript(&mut self, s: &Store<F>, transcript: Transcript<F>);
    fn r(&self) -> Option<&F>;
    fn map_to_element(&self, x: F) -> Option<F>;
    fn add(&mut self, kv: Ptr);
    fn synthesize_remove_n<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        acc: &AllocatedNum<F>,
        kv: &AllocatedPtr<F>,
        count: &AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError>;
    fn count(&self, form: &Ptr) -> usize;

    // Circuit

    fn allocated_r<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> AllocatedNum<F>;

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
}

#[derive(Debug, Clone)]
pub struct LogMemo<F: LurkField> {
    multiset: MultiSet<Ptr>,
    r: OnceCell<F>,
    transcript: OnceCell<Transcript<F>>,

    allocated_r: OnceCell<Option<AllocatedNum<F>>>,
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

impl<F: LurkField> MemoSet<F> for LogMemo<F> {
    fn count(&self, form: &Ptr) -> usize {
        self.multiset.get(form).unwrap_or(0)
    }

    fn is_finalized(&self) -> bool {
        self.transcript.get().is_some()
    }
    fn finalize_transcript(&mut self, s: &Store<F>, transcript: Transcript<F>) {
        let z_ptr = s.hash_ptr(&transcript.acc);

        assert_eq!(Tag::Expr(ExprTag::Cons), *z_ptr.tag());
        self.r.set(*z_ptr.value()).expect("r has already been set");

        self.transcript
            .set(transcript)
            .expect("transcript already finalized");
    }

    fn r(&self) -> Option<&F> {
        self.r.get()
    }

    fn allocated_r<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> AllocatedNum<F> {
        self.allocated_r
            .get_or_init(|| {
                self.r()
                    .map(|r| AllocatedNum::alloc_infallible(&mut cs.namespace(|| "r"), || *r))
            })
            .clone()
            .unwrap()
    }

    // x is H(k,v) = hash part of (cons k v)
    fn map_to_element(&self, x: F) -> Option<F> {
        self.r().and_then(|r| {
            let d = *r + x;
            d.invert().into()
        })
    }

    // x is H(k,v) = hash part of (cons k v)
    // 1 / r + x
    fn synthesize_map_to_element<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        x: AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let r = self.allocated_r(cs);
        let r_plus_x = r.add(&mut cs.namespace(|| "r+x"), &x)?;

        invert(&mut cs.namespace(|| "invert(r+x)"), &r_plus_x)
    }

    fn add(&mut self, kv: Ptr) {
        self.multiset.add(kv);
    }

    fn synthesize_add<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        acc: &AllocatedNum<F>,
        kv: &AllocatedPtr<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let kv_num = kv.hash().clone();
        let element = self.synthesize_map_to_element(&mut cs.namespace(|| "element"), kv_num)?;
        acc.add(&mut cs.namespace(|| "add to acc"), &element)
    }

    fn synthesize_remove_n<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        acc: &AllocatedNum<F>,
        kv: &AllocatedPtr<F>,
        count: &AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let kv_num = kv.hash().clone();
        let element = self.synthesize_map_to_element(&mut cs.namespace(|| "element"), kv_num)?;
        let scaled = element.mul(&mut cs.namespace(|| "scaled"), count)?;
        sub(&mut cs.namespace(|| "add to acc"), acc, &scaled)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::state::State;
    use bellpepper_core::{test_cs::TestConstraintSystem, Comparable};
    use expect_test::{expect, Expect};
    use pasta_curves::pallas::Scalar as F;
    use std::default::Default;

    #[test]
    fn test_query() {
        let s = &Store::<F>::default();
        let mut scope: Scope<F, ScopeQuery<F>, LogMemo<F>> = Scope::default();
        let state = State::init_lurk_state();

        let fact_4 = s.read_with_default_state("(factorial 4)").unwrap();
        let fact_3 = s.read_with_default_state("(factorial 3)").unwrap();

        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };

        {
            scope.query(s, fact_4);

            for (k, v) in scope.queries.iter() {
                println!("k: {}", k.fmt_to_string(s, &state));
                println!("v: {}", v.fmt_to_string(s, &state));
            }
            // Factorial 4 will memoize calls to:
            // fact(4), fact(3), fact(2), fact(1), and fact(0)
            assert_eq!(5, scope.queries.len());
            assert_eq!(1, scope.toplevel_insertions.len());
            assert_eq!(4, scope.internal_insertions.len());

            scope.finalize_transcript(s);

            let cs = &mut TestConstraintSystem::new();
            let g = &mut GlobalAllocator::default();

            scope.synthesize(cs, g, s).unwrap();

            println!(
                "transcript: {}",
                scope
                    .memoset
                    .transcript
                    .get()
                    .unwrap()
                    .fmt_to_string_simple(s)
            );

            expect_eq(cs.num_constraints(), expect!["10826"]);
            expect_eq(cs.aux().len(), expect!["10859"]);

            assert_eq!(10826, cs.num_constraints());
            assert_eq!(10859, cs.aux().len());

            let unsat = cs.which_is_unsatisfied();

            if unsat.is_some() {
                dbg!(unsat);
            }
            assert!(cs.is_satisfied());
        }
        {
            let mut scope: Scope<F, ScopeQuery<F>, LogMemo<F>> = Scope::default();
            scope.query(s, fact_4);
            scope.query(s, fact_3);

            // // No new queries.
            assert_eq!(5, scope.queries.len());
            // // One new top-level insertion.
            assert_eq!(2, scope.toplevel_insertions.len());
            // // No new internal insertions.
            assert_eq!(4, scope.internal_insertions.len());

            scope.finalize_transcript(s);

            let cs = &mut TestConstraintSystem::new();
            let g = &mut GlobalAllocator::default();

            scope.synthesize(cs, g, s).unwrap();

            expect_eq(cs.num_constraints(), expect!["11408"]);
            expect_eq(cs.aux().len(), expect!["11443"]);

            let unsat = cs.which_is_unsatisfied();
            if unsat.is_some() {
                dbg!(unsat);
            }
            assert!(cs.is_satisfied());
        }
    }
}
