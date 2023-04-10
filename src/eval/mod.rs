use crate::error::ReductionError;
use crate::field::LurkField;
use crate::hash_witness::{ConsWitness, ContWitness};
use crate::store;
use crate::store::{ContPtr, Expression, Pointer, Ptr, Store};
use crate::tag::ContTag;
use crate::writer::Write;
use log::info;
use serde::{Deserialize, Serialize};
use std::cmp::PartialEq;
use std::iter::{Iterator, Take};

pub mod reduction;

#[cfg(test)]
mod tests;

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
pub struct Frame<T: Copy, W: Copy> {
    pub input: T,
    pub output: T,
    pub i: usize,
    pub witness: W,
}

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
        match cont.tag() {
            ContTag::Terminal => Self::Terminal,
            ContTag::Error => Self::Error,
            _ => Self::Incomplete,
        }
    }
}

impl<F: LurkField, W: Copy> Frame<IO<F>, W> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        let sequential = self.i + 1 == maybe_next.i;
        let io_match = self.output == maybe_next.input;

        sequential && io_match
    }

    pub fn is_complete(&self) -> bool {
        self.input == self.output && self.output.is_complete()
    }

    pub fn log(&self, store: &Store<F>) {
        // This frame's output is the input for the next frame.
        // Report that index. Otherwise we can't report the initial input.
        self.output.log(store, self.i + 1);
    }

    pub fn significant_frame_count(frames: &[Frame<IO<F>, W>]) -> usize {
        frames
            .iter()
            .rev()
            .skip_while(|frame| frame.is_complete())
            .count()
    }
}

pub trait Evaluable<F: LurkField, W> {
    fn reduce(&self, store: &mut Store<F>) -> Result<(Self, W), ReductionError>
    where
        Self: Sized;

    fn status(&self) -> Status;
    fn is_complete(&self) -> bool;
    fn is_terminal(&self) -> bool;
    fn is_error(&self) -> bool;

    fn log(&self, store: &Store<F>, i: usize);
}

impl<F: LurkField> Evaluable<F, Witness<F>> for IO<F> {
    fn reduce(&self, store: &mut Store<F>) -> Result<(Self, Witness<F>), ReductionError> {
        let (expr, env, cont, witness) = reduction::reduce(self.expr, self.env, self.cont, store)?;
        Ok((Self { expr, env, cont }, witness))
    }

    fn status(&self) -> Status {
        Status::from(self.cont)
    }

    fn is_complete(&self) -> bool {
        self.status().is_complete()
    }
    fn is_terminal(&self) -> bool {
        self.status().is_complete()
    }

    fn is_error(&self) -> bool {
        self.status().is_error()
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
        if self.expr.tag() == crate::tag::ExprTag::Thunk
            && self.cont.tag() == crate::tag::ContTag::Dummy
        {
            if let Some(Expression::Thunk(thunk)) = store.fetch(&self.expr) {
                if thunk.continuation.tag() == crate::tag::ContTag::Emit {
                    Some(thunk.value)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn to_vector(&self, store: &Store<F>) -> Result<Vec<F>, store::Error> {
        let expr_scalar_ptr = store
            .get_expr_hash(&self.expr)
            .ok_or_else(|| store::Error("expr hash missing".into()))?;
        let env_scalar_ptr = store
            .get_expr_hash(&self.env)
            .ok_or_else(|| store::Error("expr hash missing".into()))?;
        let cont_scalar_ptr = store
            .hash_cont(&self.cont)
            .ok_or_else(|| store::Error("expr hash missing".into()))?;
        Ok(vec![
            expr_scalar_ptr.tag_field(),
            *expr_scalar_ptr.value(),
            env_scalar_ptr.tag_field(),
            *env_scalar_ptr.value(),
            cont_scalar_ptr.tag_field(),
            *cont_scalar_ptr.value(),
        ])
    }
}

impl<F: LurkField, T: Evaluable<F, Witness<F>> + Clone + PartialEq + Copy> Frame<T, Witness<F>> {
    pub(crate) fn next(&self, store: &mut Store<F>) -> Result<Self, ReductionError> {
        let input = self.output;
        let (output, witness) = input.reduce(store)?;

        // FIXME: Why isn't this method found?
        // self.log(store);
        self.output.log(store, self.i + 1);
        Ok(Self {
            input,
            output,
            i: self.i + 1,
            witness,
        })
    }
}

impl<F: LurkField, T: Evaluable<F, Witness<F>> + Clone + PartialEq + Copy> Frame<T, Witness<F>> {
    fn from_initial_input(input: T, store: &mut Store<F>) -> Result<Self, ReductionError> {
        input.log(store, 0);
        let (output, witness) = input.reduce(store)?;
        Ok(Self {
            input,
            output,
            i: 0,
            witness,
        })
    }
}

#[derive(Debug)]
pub struct FrameIt<'a, W: Copy, F: LurkField> {
    first: bool,
    frame: Frame<IO<F>, W>,
    store: &'a mut Store<F>,
}

impl<'a, F: LurkField> FrameIt<'a, Witness<F>, F> {
    fn new(initial_input: IO<F>, store: &'a mut Store<F>) -> Result<Self, ReductionError> {
        let frame = Frame::from_initial_input(initial_input, store)?;
        Ok(Self {
            first: true,
            frame,
            store,
        })
    }

    /// Like `.iter().take(n).last()`, but skips intermediary stages, to optimize
    /// for evaluation.
    fn next_n(
        mut self,
        n: usize,
    ) -> Result<
        (
            Frame<IO<F>, Witness<F>>,
            Frame<IO<F>, Witness<F>>,
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
            let new_frame = self.frame.next(self.store)?;

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
struct ResultFrame<'a, F: LurkField>(Result<FrameIt<'a, Witness<F>, F>, ReductionError>);

impl<'a, F: LurkField> Iterator for ResultFrame<'a, F> {
    type Item = Result<Frame<IO<F>, Witness<F>>, ReductionError>;
    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        let mut frame_it = match &mut self.0 {
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

        frame_it.frame = match frame_it.frame.next(frame_it.store) {
            Ok(f) => f,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(frame_it.frame.clone()))
    }
}

impl<'a, F: LurkField> Iterator for FrameIt<'a, Witness<F>, F> {
    type Item = Frame<IO<F>, Witness<F>>;
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
        self.frame = self.frame.next(self.store).ok()?;

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

impl<'a, F: LurkField> Evaluator<'a, F>
where
    IO<F>: Copy,
{
    pub fn new(expr: Ptr<F>, env: Ptr<F>, store: &'a mut Store<F>, limit: usize) -> Self {
        Evaluator {
            expr,
            env,
            store,
            limit,
            terminal_frame: None,
        }
    }

    pub fn eval(&mut self) -> Result<(IO<F>, usize, Vec<Ptr<F>>), ReductionError> {
        let initial_input = self.initial();
        let frame_iterator = FrameIt::new(initial_input, self.store)?;

        // Initial input performs one reduction, so we need limit - 1 more.
        let (ultimate_frame, _penultimate_frame, emitted) =
            frame_iterator.next_n(self.limit - 1)?;
        let output = ultimate_frame.output;

        let was_terminal = ultimate_frame.is_complete();
        let i = ultimate_frame.i;
        if was_terminal {
            self.terminal_frame = Some(ultimate_frame);
        }
        let iterations = if was_terminal { i } else { i + 1 };
        // NOTE: We compute a terminal frame but don't include it in the iteration count.
        Ok((output, iterations, emitted))
    }

    pub fn initial(&mut self) -> IO<F> {
        IO {
            expr: self.expr,
            env: self.env,
            cont: self.store.intern_cont_outermost(),
        }
    }

    pub fn iter(&mut self) -> Result<Take<FrameIt<'_, Witness<F>, F>>, ReductionError> {
        let initial_input = self.initial();

        Ok(FrameIt::new(initial_input, self.store)?.take(self.limit))
    }

    // Wraps frames in Result type in order to fail gracefully
    pub fn get_frames(&mut self) -> Result<Vec<Frame<IO<F>, Witness<F>>>, ReductionError> {
        let frame = FrameIt::new(self.initial(), self.store)?;
        let result_frame = ResultFrame(Ok(frame)).take(self.limit);
        let ret: Result<Vec<_>, _> = result_frame.collect();
        ret
    }

    pub fn generate_frames<Fp: Fn(usize) -> bool>(
        expr: Ptr<F>,
        env: Ptr<F>,
        store: &'a mut Store<F>,
        limit: usize,
        needs_frame_padding: Fp,
    ) -> Result<Vec<Frame<IO<F>, Witness<F>>>, ReductionError> {
        let mut evaluator = Self::new(expr, env, store, limit);

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

pub fn eval_to_ptr<F: LurkField>(s: &mut Store<F>, src: &str) -> Result<Ptr<F>, ReductionError> {
    let expr = s.read(src).unwrap();
    let limit = 1000000;
    Ok(Evaluator::new(expr, empty_sym_env(s), s, limit)
        .eval()?
        .0
        .expr)
}

pub struct Evaluator<'a, F: LurkField> {
    expr: Ptr<F>,
    env: Ptr<F>,
    store: &'a mut Store<F>,
    limit: usize,
    terminal_frame: Option<Frame<IO<F>, Witness<F>>>,
}
