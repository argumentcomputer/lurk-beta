use bellpepper_core::{ConstraintSystem, SynthesisError};

use super::{CircuitScope, CircuitTranscript, LogMemo, Scope};
use crate::circuit::gadgets::pointer::AllocatedPtr;
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
    ) -> Ptr;
    fn from_ptr(s: &Store<F>, ptr: &Ptr) -> Option<Self>;
    fn to_ptr(&self, s: &Store<F>) -> Ptr;
    fn symbol(&self) -> Symbol;
    fn symbol_ptr(&self, s: &Store<F>) -> Ptr {
        s.intern_symbol(&self.symbol())
    }

    fn index(&self) -> usize;
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
        scope: &mut CircuitScope<F, LogMemo<F>>,
        acc: &AllocatedPtr<F>,
        transcript: &CircuitTranscript<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, CircuitTranscript<F>), SynthesisError>;

    fn symbol(&self) -> Symbol;

    fn symbol_ptr(&self, s: &Store<F>) -> Ptr {
        s.intern_symbol(&self.symbol())
    }

    fn from_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        s: &Store<F>,
        ptr: &Ptr,
    ) -> Result<Option<Self>, SynthesisError>;
}
