use crate::coprocessor::Coprocessor;
use crate::error::ReductionError;
use crate::expr::Expression;
use crate::field::LurkField;
use crate::hash_witness::{ConsWitness, ContWitness};
use crate::ptr::{ContPtr, Ptr};
use crate::store;
use crate::store::Store;
use crate::tag::ContTag;
use crate::writer::Write;
use lang::Lang;

use log::info;
#[cfg(not(target_arch = "wasm32"))]
use lurk_macros::serde_test;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};
use std::cmp::PartialEq;
use std::iter::{Iterator, Take};
use std::marker::PhantomData;

pub mod lang;

mod reduction;

#[cfg(test)]
pub(crate) mod tests;

#[derive(Clone, Debug, PartialEq, Copy, Eq)]
pub struct IO<F: LurkField> {
    pub expr: Ptr<F>,
    pub env: Ptr<F>,
    pub cont: ContPtr<F>, // This could be a Ptr too, if we want Continuations to be first class.
}

impl<F: LurkField> Write<F> for IO<F> {
    fn fmt<W: std::io::Write>(&self, store: &Store<F>, w: &mut W) -> std::io::Result<()> {
        write!(w, "IO {{ expr: ")?;
        self.expr.fmt(store, w)?;
        write!(w, ", env: ")?;
        self.env.fmt(store, w)?;
        write!(w, ", cont: ")?;
        self.cont.fmt(store, w)?;
        write!(w, " }}")
    }
}

impl<F: LurkField> std::fmt::Display for IO<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:?}", self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame<T: Copy, W: Copy, C> {
    pub input: T,
    pub output: T,
    pub i: usize,
    pub witness: W,
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
    pub fn is_incomplete(&self) -> bool {
        match self {
            Self::Incomplete => true,
            Self::Terminal | Self::Error => false,
        }
    }

    pub fn to_cont<F: LurkField>(&self, s: &mut Store<F>) -> Option<ContPtr<F>> {
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

impl<F: LurkField, W: Copy, C: Coprocessor<F>> Frame<IO<F>, W, C> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        let sequential = self.i + 1 == maybe_next.i;
        let io_match = self.output == maybe_next.input;

        sequential && io_match
    }

    pub fn is_complete(&self) -> bool {
        self.input == self.output
            && <IO<F> as Evaluable<F, Witness<F>, C>>::is_complete(&self.output)
    }

    pub fn log(&self, store: &Store<F>) {
        // This frame's output is the input for the next frame.
        // Report that index. Otherwise we can't report the initial input.
        <IO<F> as Evaluable<F, Witness<F>, C>>::log(&self.output, store, self.i + 1);
    }

    pub fn significant_frame_count(frames: &[Frame<IO<F>, W, C>]) -> usize {
        frames
            .iter()
            .rev()
            .skip_while(|frame| frame.is_complete())
            .count()
    }
}

pub trait Evaluable<F: LurkField, W, C: Coprocessor<F>> {
    fn reduce(&self, store: &mut Store<F>, lang: &Lang<F, C>) -> Result<(Self, W), ReductionError>
    where
        Self: Sized;

    fn status(&self) -> Status;
    fn is_complete(&self) -> bool;
    fn is_terminal(&self) -> bool;
    fn is_error(&self) -> bool;

    fn log(&self, store: &Store<F>, i: usize);
}

impl<F: LurkField, C: Coprocessor<F>> Evaluable<F, Witness<F>, C> for IO<F> {
    fn reduce(
        &self,
        store: &mut Store<F>,
        lang: &Lang<F, C>,
    ) -> Result<(Self, Witness<F>), ReductionError> {
        let (expr, env, cont, witness) =
            reduction::reduce(self.expr, self.env, self.cont, store, lang)?;
        Ok((Self { expr, env, cont }, witness))
    }

    fn status(&self) -> Status {
        Status::from(self.cont)
    }

    fn is_complete(&self) -> bool {
        <IO<F> as Evaluable<F, Witness<F>, C>>::status(self).is_complete()
    }
    fn is_terminal(&self) -> bool {
        <IO<F> as Evaluable<F, Witness<F>, C>>::status(self).is_complete()
    }

    fn is_error(&self) -> bool {
        <IO<F> as Evaluable<F, Witness<F>, C>>::status(self).is_complete()
    }

    fn log(&self, store: &Store<F>, i: usize) {
        info!(
            "Frame: {}\n\tExpr: {}\n\tEnv: {}\n\tCont: {}{}\n",
            i,
            self.expr.fmt_to_string(store),
            self.env.fmt_to_string(store),
            self.cont.fmt_to_string(store),
            if let Some(emitted) = self.maybe_emitted_expression(store) {
                format!("\n\tOutput: {}", emitted.fmt_to_string(store))
            } else {
                "".to_string()
            }
        );
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

impl<
        F: LurkField,
        T: Evaluable<F, Witness<F>, C> + Clone + PartialEq + Copy,
        C: Coprocessor<F>,
    > Frame<T, Witness<F>, C>
{
    pub(crate) fn next(
        &self,
        store: &mut Store<F>,
        lang: &Lang<F, C>,
    ) -> Result<Self, ReductionError> {
        let input = self.output;
        let (output, witness) = input.reduce(store, lang)?;

        // FIXME: Why isn't this method found?
        // self.log(store);
        self.output.log(store, self.i + 1);
        Ok(Self {
            input,
            output,
            i: self.i + 1,
            witness,
            _p: Default::default(),
        })
    }
}

impl<
        F: LurkField,
        T: Evaluable<F, Witness<F>, C> + Clone + PartialEq + Copy,
        C: Coprocessor<F>,
    > Frame<T, Witness<F>, C>
{
    fn from_initial_input(
        input: T,
        store: &mut Store<F>,
        lang: &Lang<F, C>,
    ) -> Result<Self, ReductionError> {
        input.log(store, 0);
        let (output, witness) = input.reduce(store, lang)?;
        Ok(Self {
            input,
            output,
            i: 0,
            witness,
            _p: Default::default(),
        })
    }
}

#[derive(Debug)]
pub struct FrameIt<'a, W: Copy, F: LurkField, C: Coprocessor<F>> {
    first: bool,
    frame: Frame<IO<F>, W, C>,
    store: &'a mut Store<F>,
    lang: &'a Lang<F, C>,
}

impl<'a, F: LurkField, C: Coprocessor<F>> FrameIt<'a, Witness<F>, F, C> {
    fn new(
        initial_input: IO<F>,
        store: &'a mut Store<F>,
        lang: &'a Lang<F, C>,
    ) -> Result<Self, ReductionError> {
        let frame = Frame::from_initial_input(initial_input, store, lang)?;
        Ok(Self {
            first: true,
            frame,
            store,
            lang,
        })
    }

    /// Like `.iter().take(n).last()`, but skips intermediary stages, to optimize
    /// for evaluation.
    fn next_n(
        mut self,
        n: usize,
    ) -> Result<
        (
            Frame<IO<F>, Witness<F>, C>,
            Frame<IO<F>, Witness<F>, C>,
            Vec<Ptr<F>>,
        ),
        ReductionError,
    > {
        let mut previous_frame = self.frame.clone();
        let mut emitted: Vec<Ptr<F>> = Vec::new();
        for _ in 0..n {
            if self.frame.is_complete() {
                break;
            }
            let new_frame = self.frame.next(self.store, self.lang)?;

            if let Some(expr) = new_frame.output.maybe_emitted_expression(self.store) {
                emitted.push(expr);
            }
            previous_frame = std::mem::replace(&mut self.frame, new_frame);
        }
        Ok((self.frame, previous_frame, emitted))
    }
}

// Wrapper struct to preserve errors that would otherwise be lost during iteration
#[derive(Debug)]
struct ResultFrame<'a, F: LurkField, C: Coprocessor<F>>(
    Result<FrameIt<'a, Witness<F>, F, C>, ReductionError>,
);

impl<'a, F: LurkField, C: Coprocessor<F>> Iterator for ResultFrame<'a, F, C> {
    type Item = Result<Frame<IO<F>, Witness<F>, C>, ReductionError>;
    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        let frame_it = match &mut self.0 {
            Ok(f) => f,
            Err(e) => return Some(Err(e.clone())),
        };
        // skip first iteration, as one evaluation happens on construction
        if frame_it.first {
            frame_it.first = false;
            return Some(Ok(frame_it.frame.clone()));
        }

        if frame_it.frame.is_complete() {
            return None;
        }

        frame_it.frame = match frame_it.frame.next(frame_it.store, frame_it.lang) {
            Ok(f) => f,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(frame_it.frame.clone()))
    }
}

impl<'a, F: LurkField, C: Coprocessor<F>> Iterator for FrameIt<'a, Witness<F>, F, C> {
    type Item = Frame<IO<F>, Witness<F>, C>;
    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        // skip first iteration, as one evaluation happens on construction
        if self.first {
            self.first = false;
            return Some(self.frame.clone());
        }

        if self.frame.is_complete() {
            return None;
        }

        // TODO: Error info lost here
        self.frame = self.frame.next(self.store, self.lang).ok()?;

        Some(self.frame.clone())
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Witness<F: LurkField> {
    pub(crate) prethunk_output_expr: Ptr<F>,
    pub(crate) prethunk_output_env: Ptr<F>,
    pub(crate) prethunk_output_cont: ContPtr<F>,

    pub(crate) closure_to_extend: Option<Ptr<F>>,
    pub(crate) apply_continuation_cont: Option<ContPtr<F>>,
    pub(crate) conses: ConsWitness<F>,
    pub(crate) conts: ContWitness<F>,
}

impl<'a, F: LurkField, C: Coprocessor<F>> Evaluator<'a, F, C>
where
    IO<F>: Copy,
{
    pub fn new(
        expr: Ptr<F>,
        env: Ptr<F>,
        store: &'a mut Store<F>,
        limit: usize,
        lang: &'a Lang<F, C>,
    ) -> Self {
        Evaluator {
            expr,
            env,
            store,
            limit,
            terminal_frame: None,
            lang,
        }
    }

    #[inline]
    pub fn has_terminal_frame(&self) -> bool {
        self.terminal_frame.is_some()
    }

    pub fn eval(&mut self) -> Result<(IO<F>, usize, Vec<Ptr<F>>), ReductionError> {
        let initial_input = self.initial();
        let frame_iterator = FrameIt::new(initial_input, self.store, self.lang)?;

        // Initial input performs one reduction, so we need limit more.
        let (ultimate_frame, _penultimate_frame, emitted) = frame_iterator.next_n(self.limit)?;
        let output = ultimate_frame.output;

        // Since frames are 0-indexed, the i-th frame is reached after i iterations
        let iterations = ultimate_frame.i;

        if ultimate_frame.is_complete() {
            self.terminal_frame = Some(ultimate_frame);
        }
        Ok((output, iterations, emitted))
    }

    pub fn initial(&mut self) -> IO<F> {
        IO {
            expr: self.expr,
            env: self.env,
            cont: self.store.intern_cont_outermost(),
        }
    }

    pub fn iter(&mut self) -> Result<Take<FrameIt<'_, Witness<F>, F, C>>, ReductionError> {
        let initial_input = self.initial();

        Ok(FrameIt::new(initial_input, self.store, self.lang)?.take(self.limit + 1))
    }

    // Wraps frames in Result type in order to fail gracefully
    pub fn get_frames(&mut self) -> Result<Vec<Frame<IO<F>, Witness<F>, C>>, ReductionError> {
        let frame = FrameIt::new(self.initial(), self.store, self.lang)?;
        let result_frame = ResultFrame(Ok(frame)).take(self.limit + 1);
        result_frame.collect()
    }

    pub fn generate_frames<Fp: Fn(usize) -> bool>(
        expr: Ptr<F>,
        env: Ptr<F>,
        store: &'a mut Store<F>,
        limit: usize,
        needs_frame_padding: Fp,
        lang: &'a Lang<F, C>,
    ) -> Result<Vec<Frame<IO<F>, Witness<F>, C>>, ReductionError> {
        let mut evaluator = Self::new(expr, env, store, limit, lang);

        let mut frames = evaluator.get_frames()?;
        assert!(!frames.is_empty());

        // TODO: We previously had an optimization here. If the limit was not reached, the final frame should be an
        // identity reduction suitable for padding. If it's not needed for that purpose, we can pop it from frames. In
        // the worst case, this could save creating one multi-frame filled only with this identity padding. However,
        // knowing when it is safe to do that is complicated, because for Groth16/SnarkPack+, we may need to pad the
        // total number of proofs to a power of two. For now, we omit the optimization. With more thought and care, we
        // could add it back later.

        if !frames.is_empty() {
            let padding_frame = frames[frames.len() - 1].clone();
            while needs_frame_padding(frames.len()) {
                frames.push(padding_frame.clone());
            }
        }

        Ok(frames)
    }
}

pub fn empty_sym_env<F: LurkField>(store: &Store<F>) -> Ptr<F> {
    store.get_nil()
}

// Convenience functions, mostly for use in tests.

pub fn eval_to_ptr<F: LurkField, C: Coprocessor<F>>(
    s: &mut Store<F>,
    src: &str,
) -> Result<Ptr<F>, ReductionError> {
    let expr = s.read(src).unwrap();
    let limit = 1000000;
    let lang = Lang::<F, C>::new();
    Ok(Evaluator::new(expr, empty_sym_env(s), s, limit, &lang)
        .eval()?
        .0
        .expr)
}

pub struct Evaluator<'a, F: LurkField, C: Coprocessor<F>> {
    expr: Ptr<F>,
    env: Ptr<F>,
    store: &'a mut Store<F>,
    limit: usize,
    terminal_frame: Option<Frame<IO<F>, Witness<F>, C>>,
    lang: &'a Lang<F, C>,
}
