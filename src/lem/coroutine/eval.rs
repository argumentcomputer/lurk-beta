#![allow(unused_variables)]
use super::toplevel::{Toplevel, ToplevelQuery};

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

fn eval<F: LurkField>(
    query: &ToplevelQuery<F>,
    scope: &mut Scope<ToplevelQuery<F>, LogMemo<F>, F>,
) -> Ptr {
    let name = &query.name;
    let args = &query.args;
    let toplevel = scope.content.as_ref();
    let coroutine = toplevel.get(name).unwrap();
    todo!()
}
