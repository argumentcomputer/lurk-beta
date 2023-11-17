use crate::field::LurkField;
use crate::lurk_sym_ptr;
use crate::ptr::Ptr;
use crate::store::Store;

use std::cmp::PartialEq;
use std::marker::PhantomData;

pub mod lang;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Frame<T: Copy, W: Copy, F: LurkField, C> {
    pub input: T,
    pub output: T,
    pub i: usize,
    pub witness: W,
    pub _p: PhantomData<(C, F)>,
}

#[inline]
pub fn empty_sym_env<F: LurkField>(store: &Store<F>) -> Ptr<F> {
    lurk_sym_ptr!(store, nil)
}
