use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};

use super::{AllocatedProvenance, CircuitScope, LogMemo, LogMemoCircuit, Scope};
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coprocessor::gadgets::construct_cons;
use crate::field::LurkField;
use crate::lem::circuit::GlobalAllocator;
use crate::lem::{pointers::Ptr, store::Store};
use crate::symbol::Symbol;

pub trait Query<F: LurkField>
where
    Self: Sized + Clone,
{
    type C: Clone + Send + Sync;
    type CQ: CircuitQuery<F, C = Self::C>;

    fn eval(&self, scope: &mut Scope<Self, LogMemo<F>, F>) -> Ptr;
    fn recursive_eval(&self, scope: &mut Scope<Self, LogMemo<F>, F>, subquery: Self) -> Ptr {
        scope.query_recursively(self, subquery)
    }
    fn from_ptr(c: &Self::C, s: &Store<F>, ptr: &Ptr) -> Option<Self>;
    fn to_ptr(&self, s: &Store<F>) -> Ptr;
    fn to_circuit<CS: ConstraintSystem<F>>(&self, cs: &mut CS, s: &Store<F>) -> Self::CQ;
    fn dummy_from_index(c: &Self::C, s: &Store<F>, index: usize) -> Self;

    fn symbol(&self) -> Symbol;
    fn symbol_ptr(&self, s: &Store<F>) -> Ptr {
        s.intern_symbol(&self.symbol())
    }

    /// What is this queries index? Used for ordering circuits and transcripts, grouped by query type.
    fn index(&self, c: &Self::C) -> usize;
    /// How many types of query are provided?
    fn count(c: &Self::C) -> usize;
}

pub trait CircuitQuery<F: LurkField>
where
    Self: Sized + Clone,
{
    type C: Clone + Send + Sync;
    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>, Self::C>,
        acc: &AllocatedPtr<F>,
        allocated_key: &AllocatedPtr<F>,
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError>;

    fn symbol(&self) -> Symbol;

    fn symbol_ptr(&self, s: &Store<F>) -> Ptr {
        s.intern_symbol(&self.symbol())
    }

    fn from_ptr<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, ptr: &Ptr) -> Option<Self>;

    fn dummy_from_index<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, index: usize) -> Self;

    fn synthesize_args<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError>;

    fn synthesize_query<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let symbol = g.alloc_ptr(ns!(cs, "symbol_"), &self.symbol_ptr(store), store);
        let args = self.synthesize_args(ns!(cs, "args"), g, store)?;
        construct_cons(ns!(cs, "query"), g, store, &symbol, &args)
    }

    fn synthesize_provenance<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        result: AllocatedPtr<F>,
        dependency_provenances: Vec<AllocatedPtr<F>>,
        allocated_key: &AllocatedPtr<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let query = allocated_key.clone();
        let p = AllocatedProvenance::new(query, result, dependency_provenances);

        Ok(p.to_ptr(cs, g, store)?.clone())
    }
}

pub(crate) trait RecursiveQuery<F: LurkField>: CircuitQuery<F> {
    fn post_recursion<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        subquery_results: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError>;

    fn recurse<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>, Self::C>,
        subqueries: &[Self],
        is_recursive: &Boolean,
        immediate: (&AllocatedPtr<F>, &AllocatedPtr<F>),
        allocated_key: &AllocatedPtr<F>,
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError> {
        let is_immediate = is_recursive.not();
        let nil = g.alloc_ptr(ns!(cs, "nil"), &store.intern_nil(), store);

        let mut sub_results = vec![];
        let mut dependency_provenances = vec![];
        let mut new_acc = immediate.1.clone();
        for subquery in subqueries {
            let subquery = subquery.synthesize_query(cs, g, store)?;
            let ((sub_result, sub_provenance), next_acc) = scope.synthesize_internal_query(
                ns!(cs, "recursive query"),
                g,
                store,
                &subquery,
                &new_acc,
                is_recursive,
            )?;
            let dependency_provenance = AllocatedPtr::pick(
                ns!(cs, "dependency provenance"),
                &is_immediate,
                &nil,
                &sub_provenance,
            )?;
            sub_results.push(sub_result);
            dependency_provenances.push(dependency_provenance);
            new_acc = next_acc;
        }

        let (recursive_result, recursive_acc) = (self.post_recursion(cs, &sub_results)?, new_acc);

        let value = AllocatedPtr::pick(
            ns!(cs, "pick value"),
            &is_immediate,
            immediate.0,
            &recursive_result,
        )?;

        let acc = AllocatedPtr::pick(
            ns!(cs, "pick acc"),
            &is_immediate,
            immediate.1,
            &recursive_acc,
        )?;

        let provenance = self.synthesize_provenance(
            ns!(cs, "provenance"),
            g,
            store,
            value.clone(),
            dependency_provenances,
            allocated_key,
        )?;

        Ok(((value, provenance.clone()), acc))
    }
}
