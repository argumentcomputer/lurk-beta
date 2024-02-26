#![allow(unused_variables)]
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coprocessor::gadgets::construct_cons;
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

    pub fn get(&self, name: &Symbol) -> Option<&Coroutine<F>> {
        self.0.get(name)
    }
}

#[derive(Clone)]
pub struct ToplevelQuery<F> {
    pub(crate) name: Symbol,
    pub(crate) args: Vec<Ptr>,
    pub(crate) _p: PhantomData<F>,
}

#[derive(Clone)]
pub struct ToplevelCircuitQuery<F: LurkField> {
    pub(crate) name: Symbol,
    pub(crate) args: Vec<AllocatedPtr<F>>,
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
    type CQ = ToplevelCircuitQuery<F>;
    type C = Arc<Toplevel<F>>;
    fn eval(&self, scope: &mut Scope<Self, LogMemo<F>, F>) -> Ptr {
        todo!()
    }
    fn to_circuit<CS: ConstraintSystem<F>>(&self, cs: &mut CS, s: &Store<F>) -> Self::CQ {
        let name = self.name.clone();
        let mut args = vec![];
        for (i, arg) in self.args.iter().enumerate() {
            let cs = ns!(cs, format!("arg:{i}"));
            let alloc = AllocatedPtr::alloc_infallible(cs, || s.hash_ptr(arg));
            args.push(alloc);
        }
        ToplevelCircuitQuery { name, args }
    }
    fn from_ptr(s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        let (head, mut acc) = s.car_cdr(ptr).expect("query should be cons");
        let name = s.fetch_sym(&head).expect("head should be sym");
        let mut args = vec![];
        let _p = PhantomData;
        if acc.is_nil() {
            return Some(ToplevelQuery { name, args, _p });
        }
        // TODO: we must do this destructuring until we have exactly the number of
        // arguments the query needs, otherwise we might run into the problem of
        // destructuring too much (the last argument might be a cons)
        while acc.is_cons() {
            let (arg, rest) = s.car_cdr(&acc).expect("can't find image for cons");
            args.push(arg);
            acc = rest;
        }
        args.push(acc);
        Some(ToplevelQuery { name, args, _p })
    }
    fn to_ptr(&self, s: &Store<F>) -> Ptr {
        let args = if self.args.is_empty() {
            s.intern_nil()
        } else {
            // Iterator from last to first
            let mut iter = self.args.iter().rev();
            let mut args = *iter.next().unwrap();
            for arg in iter {
                args = s.cons(*arg, args);
            }
            args
        };
        let name = s.intern_symbol(&self.name);
        s.cons(name, args)
    }
    fn dummy_from_index(toplevel: &Self::C, s: &Store<F>, index: usize) -> Self {
        let (name, coroutine) = toplevel.0.get_index(index).unwrap();
        let name = name.clone();
        let args_size = coroutine.func.input_params.len();
        let args = vec![s.num(0.into()); args_size];
        let _p = PhantomData;
        ToplevelQuery { name, args, _p }
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

impl<F: LurkField> CircuitQuery<F> for ToplevelCircuitQuery<F> {
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
        self.name.clone()
    }

    fn from_ptr<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        ToplevelQuery::from_ptr(s, ptr).map(|q| q.to_circuit(cs, s))
    }

    fn dummy_from_index<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, index: usize) -> Self {
        unimplemented!()
    }

    fn synthesize_args<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        if self.args.is_empty() {
            let nil = store.intern_nil();
            let allocated_nil = g.alloc_ptr(cs, &nil, store);
            return Ok(allocated_nil);
        }
        // Iterator from last to first. Enumerate indices used for namespaces
        let mut iter = self.args.iter().rev();
        let mut args = iter.next().unwrap().clone();
        for (i, arg) in iter.enumerate() {
            let cs = ns!(cs, format!("arg:{i}"));
            args = construct_cons(cs, g, store, arg, &args)?;
        }
        Ok(args)
    }
}
