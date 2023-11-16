use crate::field::LurkField;
use crate::hash_witness::{ConsWitness, ContWitness};
use crate::ptr::{ContPtr, Ptr};
use crate::store::Store;
use crate::z_ptr::ZExprPtr;

use std::cmp::PartialEq;
use std::marker::PhantomData;

pub mod lang;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Meta<F: LurkField> {
    #[default]
    Lurk,
    Coprocessor(ZExprPtr<F>),
}

impl<F: LurkField> Meta<F> {
    pub fn is_coprocessor(&self) -> bool {
        matches!(self, Self::Coprocessor(_))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Frame<T: Copy, W: Copy, F: LurkField, C> {
    pub input: T,
    pub output: T,
    pub i: usize,
    pub witness: W,
    pub meta: Meta<F>,
    pub _p: PhantomData<C>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Witness<F: LurkField> {
    pub(crate) prethunk_output_expr: Ptr<F>,
    pub(crate) prethunk_output_env: Ptr<F>,
    pub(crate) prethunk_output_cont: ContPtr<F>,

    pub(crate) closure_to_extend: Option<Ptr<F>>,
    pub(crate) apply_continuation_cont: Option<ContPtr<F>>,
    pub(crate) conses: ConsWitness<F>,
    pub(crate) conts: ContWitness<F>,
}

#[inline]
pub fn empty_sym_env<F: LurkField>(store: &Store<F>) -> Ptr<F> {
    lurk_sym_ptr!(store, nil)
}
