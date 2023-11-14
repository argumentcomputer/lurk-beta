use crate::coprocessor::Coprocessor;
use crate::expr::Expression;
use crate::field::LurkField;
use crate::hash_witness::{ConsWitness, ContWitness};
use crate::ptr::{ContPtr, Ptr};
use crate::state::State;
use crate::store::Store;
use crate::tag::ContTag;
use crate::writer::Write;
use crate::z_ptr::ZExprPtr;
use crate::{lurk_sym_ptr, store};

#[cfg(not(target_arch = "wasm32"))]
use lurk_macros::serde_test;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};
use std::cmp::PartialEq;
use std::marker::PhantomData;

pub mod lang;

#[derive(Clone, Debug, PartialEq, Copy, Eq)]
pub struct IO<F: LurkField> {
    pub expr: Ptr<F>,
    pub env: Ptr<F>,
    pub cont: ContPtr<F>, // This could be a Ptr too, if we want Continuations to be first class.
}

impl<F: LurkField> Write<F> for IO<F> {
    fn fmt<W: std::io::Write>(
        &self,
        store: &Store<F>,
        state: &State,
        w: &mut W,
    ) -> std::io::Result<()> {
        write!(w, "IO {{ expr: ")?;
        self.expr.fmt(store, state, w)?;
        write!(w, ", env: ")?;
        self.env.fmt(store, state, w)?;
        write!(w, ", cont: ")?;
        self.cont.fmt(store, state, w)?;
        write!(w, " }}")
    }
}

impl<F: LurkField> std::fmt::Display for IO<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{self:?}")
    }
}

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

impl<F: LurkField, W: Copy, C: Coprocessor<F>> Frame<IO<F>, W, F, C> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        let sequential = self.i + 1 == maybe_next.i;
        let io_match = self.output == maybe_next.input;

        sequential && io_match
    }
}

impl<F: LurkField> IO<F> {
    // Returns any expression that was emitted in this IO (if an output) or previous (if an input).
    // The intention is that this method will be used to extract and handle all output as needed.
    pub fn maybe_emitted_expression(&self, store: &Store<F>) -> Option<Ptr<F>> {
        if self.expr.tag != crate::tag::ExprTag::Thunk
            || self.cont.tag != crate::tag::ContTag::Dummy
        {
            return None;
        }

        let expr = match store.fetch(&self.expr) {
            Some(Expression::Thunk(thunk)) => thunk,
            _ => return None,
        };

        (expr.continuation.tag == crate::tag::ContTag::Emit).then_some(expr.value)
    }

    pub fn to_vector(&self, store: &Store<F>) -> Result<Vec<F>, store::Error> {
        let expr_z_ptr = store
            .hash_expr(&self.expr)
            .ok_or_else(|| store::Error("expr hash missing".into()))?;
        let env_z_ptr = store
            .hash_expr(&self.env)
            .ok_or_else(|| store::Error("expr hash missing".into()))?;
        let cont_z_ptr = store
            .hash_cont(&self.cont)
            .ok_or_else(|| store::Error("expr hash missing".into()))?;
        Ok(vec![
            expr_z_ptr.tag_field(),
            *expr_z_ptr.value(),
            env_z_ptr.tag_field(),
            *env_z_ptr.value(),
            cont_z_ptr.tag_field(),
            *cont_z_ptr.value(),
        ])
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
