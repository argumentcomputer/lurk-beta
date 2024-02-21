#![allow(unused_variables)]
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coroutine::memoset::{
    CircuitQuery, CircuitScope, LogMemo, LogMemoCircuit, Query, Scope,
};
use crate::field::LurkField;
use crate::lem::{circuit::GlobalAllocator, pointers::Ptr, store::Store, Func};
use crate::symbol::Symbol;

use bellpepper_core::{ConstraintSystem, SynthesisError};
use indexmap::IndexMap;
use std::marker::PhantomData;

#[derive(Clone)]
pub struct Coroutine<F> {
    pub func: Func,
    pub index: usize,
    pub rc: usize,
    pub _p: PhantomData<F>,
}

#[derive(Clone)]
pub struct Toplevel<F>(IndexMap<Symbol, Coroutine<F>>);

impl<F> Toplevel<F> {
    pub fn new(funcs: &[Func]) -> Self {
        todo!()
    }
}

#[derive(Clone)]
pub struct ToplevelQuery<F> {
    pub name: Symbol,
    pub args: Ptr,
    pub toplevel: Toplevel<F>,
}

impl<F: LurkField> Query<F> for ToplevelQuery<F> {
    type CQ = Self;
    fn eval(&self, s: &Store<F>, scope: &mut Scope<Self, LogMemo<F>, F>) -> Ptr {
        todo!()
    }
    fn from_ptr(s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        todo!()
    }
    fn to_ptr(&self, s: &Store<F>) -> Ptr {
        todo!()
    }
    fn to_circuit<CS: ConstraintSystem<F>>(&self, cs: &mut CS, s: &Store<F>) -> Self::CQ {
        todo!()
    }
    fn dummy_from_index(s: &Store<F>, index: usize) -> Self {
        todo!()
    }
    fn symbol(&self) -> Symbol {
        todo!()
    }
    fn index(&self) -> usize {
        todo!()
    }
    fn count() -> usize {
        todo!()
    }
}

impl<F: LurkField> CircuitQuery<F> for ToplevelQuery<F> {
    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>>,
        acc: &AllocatedPtr<F>,
        allocated_key: &AllocatedPtr<F>,
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError> {
        todo!()
    }

    fn symbol(&self) -> Symbol {
        todo!()
    }

    fn from_ptr<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        todo!()
    }

    fn dummy_from_index<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, index: usize) -> Self {
        todo!()
    }

    fn synthesize_args<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        todo!()
    }
}
