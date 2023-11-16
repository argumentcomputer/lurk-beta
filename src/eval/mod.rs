use crate::field::LurkField;
use crate::hash_witness::{ConsWitness, ContWitness};
use crate::ptr::{ContPtr, Ptr};
use crate::store::Store;
use crate::tag::ContTag;
use crate::z_ptr::ZExprPtr;

#[cfg(not(target_arch = "wasm32"))]
use lurk_macros::serde_test;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};
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

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), serde_test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Status {
    Terminal,
    Error,
    Incomplete,
}

impl Default for Status {
    fn default() -> Self {
        Self::Incomplete
    }
}

impl Status {
    pub fn is_complete(&self) -> bool {
        match self {
            Self::Terminal | Self::Error => true,
            Self::Incomplete => false,
        }
    }

    pub fn is_terminal(&self) -> bool {
        match self {
            Self::Terminal => true,
            Self::Incomplete | Self::Error => false,
        }
    }

    pub fn is_error(&self) -> bool {
        match self {
            Self::Error => true,
            Self::Terminal | Self::Incomplete => false,
        }
    }

    pub fn to_cont<F: LurkField>(&self, s: &Store<F>) -> Option<ContPtr<F>> {
        match self {
            Self::Terminal => Some(s.intern_cont_terminal()),
            Self::Error => Some(s.intern_cont_error()),
            Self::Incomplete => None,
        }
    }
}

impl<F: LurkField> From<ContPtr<F>> for Status {
    fn from(cont: ContPtr<F>) -> Self {
        match cont.tag {
            ContTag::Terminal => Self::Terminal,
            ContTag::Error => Self::Error,
            _ => Self::Incomplete,
        }
    }
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
