#![allow(unused_variables)]
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coroutine::memoset::{
    CircuitQuery, CircuitScope, LogMemo, LogMemoCircuit, Query, Scope,
};
use crate::field::LurkField;
use crate::lem::{circuit::GlobalAllocator, pointers::Ptr, store::Store, Func};
use crate::symbol::Symbol;

use anyhow::{bail, Context, Result};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use indexmap::IndexMap;
use std::marker::PhantomData;
use std::sync::Arc;

#[derive(Clone)]
pub struct Coroutine<F> {
    pub func: Func,
    pub rc: usize,
    pub _p: PhantomData<F>,
}

#[derive(Clone)]
pub struct Toplevel<F>(IndexMap<Symbol, Coroutine<F>>);

fn compute_rc(_func: &Func) -> usize {
    // TODO
    1
}

impl<F> Toplevel<F> {
    pub fn new(funcs: Vec<(Symbol, Func)>) -> Self {
        let mut toplevel = IndexMap::new();
        for (name, func) in funcs.into_iter() {
            let rc = compute_rc(&func);
            let _p = PhantomData;
            toplevel.insert(name, Coroutine { func, rc, _p });
        }
        Toplevel(toplevel)
    }
}

#[derive(Clone)]
pub struct ToplevelQuery<F> {
    name: Symbol,
    args: Vec<Ptr>,
    _p: PhantomData<F>,
}

impl<F> ToplevelQuery<F> {
    pub fn new(name: Symbol, args: Vec<Ptr>, toplevel: &Toplevel<F>) -> Result<Self> {
        let msg = || format!("`{name}` not found in the toplevel");
        let coroutine = toplevel.0.get(&name).with_context(msg)?;
        let input_size = coroutine.func.input_params.len();
        if args.len() != input_size {
            bail!(
                "Wrong number of arguments. Expected {}, found {}",
                args.len(),
                input_size
            )
        }
        let _p = PhantomData;
        let query = ToplevelQuery { name, args, _p };
        Ok(query)
    }
}

impl<F: LurkField> Query<F> for ToplevelQuery<F> {
    type CQ = Self;
    type C = Arc<Toplevel<F>>;
    fn eval(&self, scope: &mut Scope<Self, LogMemo<F>, F>) -> Ptr {
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
        self.name.clone()
    }
    fn index(&self, toplevel: &Self::C) -> usize {
        toplevel.0.get_index_of(&self.name).unwrap()
    }
    fn count(toplevel: &Self::C) -> usize {
        toplevel.0.len()
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
