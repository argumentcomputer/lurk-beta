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
    type CQ: CircuitQuery<F>;

    fn eval(&self, s: &Store<F>, scope: &mut Scope<Self, LogMemo<F>, F>) -> Ptr;
    fn recursive_eval(
        &self,
        scope: &mut Scope<Self, LogMemo<F>, F>,
        s: &Store<F>,
        subquery: Self,
    ) -> Ptr {
        scope.query_recursively(s, self, subquery)
    }
    fn from_ptr(s: &Store<F>, ptr: &Ptr) -> Option<Self>;
    fn to_ptr(&self, s: &Store<F>) -> Ptr;
    fn to_circuit<CS: ConstraintSystem<F>>(&self, cs: &mut CS, s: &Store<F>) -> Self::CQ;
    fn dummy_from_index(s: &Store<F>, index: usize) -> Self;

    fn symbol(&self) -> Symbol;
    fn symbol_ptr(&self, s: &Store<F>) -> Ptr {
        s.intern_symbol(&self.symbol())
    }

    /// What is this queries index? Used for ordering circuits and transcripts, grouped by query type.
    fn index(&self) -> usize;
    /// How many types of query are provided?
    fn count() -> usize;
}

pub trait CircuitQuery<F: LurkField>
where
    Self: Sized + Clone,
{
    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>>,
        acc: &AllocatedPtr<F>,
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError>;

    fn symbol(&self) -> Symbol;

    fn symbol_ptr(&self, s: &Store<F>) -> Ptr {
        s.intern_symbol(&self.symbol())
    }

    fn from_ptr<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, ptr: &Ptr) -> Option<Self>;

    fn dummy_from_index<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, index: usize) -> Self;
}

pub(crate) trait RecursiveQuery<F: LurkField>: CircuitQuery<F> {
    fn post_recursion<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        subquery_result: AllocatedPtr<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        Ok(subquery_result)
    }

    fn recurse<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>>,
        query: &AllocatedPtr<F>,
        args: &AllocatedPtr<F>,
        is_recursive: &Boolean,
        immediate: (&AllocatedPtr<F>, &AllocatedPtr<F>),
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError> {
        let is_immediate = is_recursive.not();

        let subquery = {
            let symbol = g.alloc_ptr(ns!(cs, "symbol"), &self.symbol_ptr(store), store);
            construct_cons(ns!(cs, "subquery"), g, store, &symbol, args)?
        };

        let ((sub_result, sub_provenance), new_acc) = scope.synthesize_internal_query(
            ns!(cs, "recursive query"),
            g,
            store,
            &subquery,
            immediate.1,
            is_recursive,
        )?;

        let (recursive_result, recursive_acc) = (self.post_recursion(cs, sub_result)?, new_acc);

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

        let nil = g.alloc_ptr(ns!(cs, "nil"), &store.intern_nil(), store);

        let dependency_provenance = AllocatedPtr::pick(
            ns!(cs, "dependency provenance"),
            &is_immediate,
            &nil,
            &sub_provenance,
        )?;

        let p = AllocatedProvenance::new(
            query.clone(),
            value.clone(),
            vec![dependency_provenance.clone()],
        );

        let provenance = p.to_ptr(cs, g, store)?;

        Ok(((value, provenance.clone()), acc))
    }
}
