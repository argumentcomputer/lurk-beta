use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};

use super::{CircuitScope, CircuitTranscript, LogMemo, LogMemoCircuit, Scope};
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

    fn eval(&self, s: &Store<F>, scope: &mut Scope<Self, LogMemo<F>>) -> Ptr;
    fn recursive_eval(
        &self,
        scope: &mut Scope<Self, LogMemo<F>>,
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
        transcript: &CircuitTranscript<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, CircuitTranscript<F>), SynthesisError>;

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
        args: &AllocatedPtr<F>,
        is_recursive: &Boolean,
        immediate: (&AllocatedPtr<F>, &AllocatedPtr<F>, &CircuitTranscript<F>),
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, CircuitTranscript<F>), SynthesisError> {
        let is_immediate = is_recursive.not();

        let subquery = {
            let symbol = g.alloc_ptr(
                &mut cs.namespace(|| "symbol"),
                &self.symbol_ptr(store),
                store,
            );
            construct_cons(&mut cs.namespace(|| "subquery"), g, store, &symbol, args)?
        };

        let (sub_result, new_acc, new_transcript) = scope.synthesize_internal_query(
            &mut cs.namespace(|| "recursive query"),
            g,
            store,
            &subquery,
            immediate.1,
            immediate.2,
            is_recursive,
        )?;

        let (recursive_result, recursive_acc, recursive_transcript) = (
            self.post_recursion(cs, sub_result)?,
            new_acc,
            new_transcript,
        );

        let value = AllocatedPtr::pick(
            &mut cs.namespace(|| "pick value"),
            &is_immediate,
            immediate.0,
            &recursive_result,
        )?;

        let acc = AllocatedPtr::pick(
            &mut cs.namespace(|| "pick acc"),
            &is_immediate,
            immediate.1,
            &recursive_acc,
        )?;

        let transcript = CircuitTranscript::pick(
            &mut cs.namespace(|| "pick recursive_transcript"),
            &is_immediate,
            immediate.2,
            &recursive_transcript,
        )?;

        Ok((value, acc, transcript))
    }
}
