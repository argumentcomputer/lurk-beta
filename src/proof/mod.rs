#![deny(missing_docs)]

//! This module offers a connection the the backend proving engine of Lurk.
//! Abstracted behind the `Prover` and `Verifier` traits, the proving engine
//! has two instantiations:
//! - the Groth16/SnarkPack proving system, implemented in the `groth16` module
//! - the Nova proving system, implemented in the `nova` module.
/// An adapter to a Groth16 proving system implementation.
pub mod groth16;
/// An adapter to a Nova proving system implementation.
pub mod nova;

/// An adapter to a SuperNova proving system implementation.
pub mod supernova;

use crate::coprocessor::Coprocessor;
use crate::error::ProofError;
use crate::eval::Meta;
use crate::eval::{lang::Lang, Evaluator, Frame, Witness, IO};
use crate::field::LurkField;

use crate::ptr::Ptr;
use crate::store::Store;
use ::nova::traits::circuit::StepCircuit;
use bellpepper::util_cs::witness_cs::WitnessCS;
use bellpepper_core::ConstraintSystem;
use bellpepper_core::{test_cs::TestConstraintSystem, Circuit, SynthesisError};
use std::sync::Arc;

use self::supernova::FoldingConfig;

/// The State of a CEK machine.
pub trait CEKState<ExprPtr, ContPtr> {
    /// the expression, or control word (C)
    fn expr(&self) -> &ExprPtr;
    /// the environment (E)
    fn env(&self) -> &ExprPtr;
    /// the continuation (K)
    fn cont(&self) -> &ContPtr;
}

/// A Frame of evaluation in a CEK machine.
pub trait FrameLike<ExprPtr, ContPtr>: Sized {
    /// the type for the Frame's IO
    type FrameIO: CEKState<ExprPtr, ContPtr>;
    /// the input of the frame
    fn input(&self) -> &Self::FrameIO;
    /// the output of the frame
    fn output(&self) -> &Self::FrameIO;
}

/// A trait for a store of expressions
pub trait EvaluationStore {
    /// the type for the Store's pointers
    type Ptr;
    /// the type for the Store's continuation poitners
    type ContPtr;
    /// the type for the Store's errors
    type Error: std::fmt::Debug;

    /// interpreting a string representation of an expression
    fn read(&self, expr: &str) -> Result<Self::Ptr, Self::Error>;
    /// getting a pointer to the initial, empty environment
    fn initial_empty_env(&self) -> Self::Ptr;
    /// getting the terminal continuation pointer
    fn get_cont_terminal(&self) -> Self::ContPtr;

    /// hash-equality of the expressions represented by Ptrs
    fn ptr_eq(&self, left: &Self::Ptr, right: &Self::Ptr) -> Result<bool, Self::Error>;
}

/// Trait to support multiple `MultiFrame` implementations.
pub trait MultiFrameTrait<'a, F: LurkField, C: Coprocessor<F> + 'a>:
    Provable<F> + Circuit<F> + StepCircuit<F> + 'a
{
    /// The associated `Ptr` type
    type Ptr: std::fmt::Debug + Eq + Copy;
    /// The associated `ContPtr` type
    type ContPtr: std::fmt::Debug + Eq + Copy;
    /// The associated `Store` type
    type Store: Send + Sync + EvaluationStore<Ptr = Self::Ptr, ContPtr = Self::ContPtr>;
    /// The error type for the Store type
    type StoreError: Into<ProofError>;

    /// The associated `Frame` type
    type EvalFrame: FrameLike<Self::Ptr, Self::ContPtr>;
    /// The associated `CircuitFrame` type
    type CircuitFrame: FrameLike<
        Self::Ptr,
        Self::ContPtr,
        FrameIO = <Self::EvalFrame as FrameLike<Self::Ptr, Self::ContPtr>>::FrameIO,
    >;
    /// The associated type which manages global allocations
    type GlobalAllocation;
    /// The associated type of allocated input and output to the circuit
    type AllocatedIO;

    /// the emitted frames
    fn emitted(store: &Self::Store, eval_frame: &Self::EvalFrame) -> Vec<Self::Ptr>;

    /// Counting the number of non-trivial frames in the evaluation
    fn significant_frame_count(frames: &[Self::EvalFrame]) -> usize;

    /// Evaluates and generates the frames of the computation given the expression, environment, and store
    fn get_evaluation_frames(
        padding_predicate: impl Fn(usize) -> bool, // Determines if the prover needs padding for a given total number of frames
        expr: Self::Ptr,
        env: Self::Ptr,
        store: &Self::Store,
        limit: usize,
        land: &Lang<F, C>,
    ) -> Result<Vec<Self::EvalFrame>, ProofError>;

    /// Returns a public IO vector when equipped with the local store, and the Self::Frame's IO
    fn io_to_scalar_vector(
        store: &Self::Store,
        io: &<Self::EvalFrame as FrameLike<Self::Ptr, Self::ContPtr>>::FrameIO,
    ) -> Result<Vec<F>, Self::StoreError>;

    /// Returns true if the supplied instance directly precedes this one in a sequential computation trace.
    fn precedes(&self, maybe_next: &Self) -> bool;

    /// Populates a WitnessCS with the witness values for the given store.
    fn compute_witness(&self, s: &Self::Store) -> WitnessCS<F>;

    /// Returns a reference to the cached witness values
    fn cached_witness(&mut self) -> &mut Option<WitnessCS<F>>;

    /// The output of the last frame
    fn output(&self) -> &Option<<Self::EvalFrame as FrameLike<Self::Ptr, Self::ContPtr>>::FrameIO>;

    /// Iterates through the Self::CircuitFrame instances
    fn frames(&self) -> Option<&Vec<Self::CircuitFrame>>;

    /// Synthesize some frames.
    fn synthesize_frames<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Self::Store,
        input: Self::AllocatedIO,
        frames: &[Self::CircuitFrame],
        g: &Self::GlobalAllocation,
    ) -> Self::AllocatedIO;

    /// Synthesize a blank circuit.
    fn blank(folding_config: Arc<FoldingConfig<F, C>>, meta: Meta<F>) -> Self;

    /// Create an instance from some `Self::Frame`s.
    fn from_frames(
        count: usize,
        frames: &[Self::EvalFrame],
        store: &'a Self::Store,
        folding_config: Arc<FoldingConfig<F, C>>,
    ) -> Vec<Self>;

    /// Make a dummy instance, duplicating `self`'s final `CircuitFrame`.
    fn make_dummy(
        count: usize,
        circuit_frame: Option<Self::CircuitFrame>,
        store: &'a Self::Store,
        folding_config: Arc<FoldingConfig<F, C>>,
        meta: Meta<F>,
    ) -> Self;
}

/// Represents a sequential Constraint System for a given proof.
pub(crate) type SequentialCS<F, M> = Vec<(M, TestConstraintSystem<F>)>;

/// A trait for provable structures over a field `F`.
pub trait Provable<F: LurkField> {
    /// Returns the public inputs of the provable structure.
    fn public_inputs(&self) -> Vec<F>;
    /// Returns the size of the public inputs.
    fn public_input_size() -> usize;
    /// Returns the number of reductions in the provable structure.
    fn reduction_count(&self) -> usize;
}

/// Verifies a sequence of constraint systems (CSs) for sequentiality & validity.
pub fn verify_sequential_css<
    'a,
    F: LurkField + Copy,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
>(
    css: &SequentialCS<F, M>,
) -> Result<bool, SynthesisError> {
    let mut previous_frame: Option<&M> = None;

    for (i, (multiframe, cs)) in css.iter().enumerate() {
        if let Some(prev) = previous_frame {
            if !prev.precedes(multiframe) {
                tracing::debug!("frame {}: not preceeding frame", i);
                return Ok(false);
            }
        }
        if !cs.is_satisfied() {
            tracing::debug!("frame {}: cs not satisfied", i);
            return Ok(false);
        }

        let public_inputs = multiframe.public_inputs();
        if !cs.verify(&public_inputs) {
            tracing::debug!("frame {}: cs not verified", i);
            return Ok(false);
        }
        previous_frame = Some(multiframe);
    }
    Ok(true)
}
/// A trait representing the public parameters for a proving system.
pub trait PublicParameters {}

/// A trait for a prover that works with a field `F`.
pub trait Prover<'a, F: LurkField, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>> {
    /// The associated public parameters type for the prover.
    type PublicParams: PublicParameters;

    /// Creates a new prover with the specified number of reductions.
    fn new(reduction_count: usize, lang: Lang<F, C>) -> Self;

    /// Returns the number of reductions for the prover.
    fn reduction_count(&self) -> usize;

    /// Returns a reference to the Prover's Lang.
    fn lang(&self) -> &Lang<F, C>;

    /// Determines if the prover needs padding for a given total number of frames.
    fn needs_frame_padding(&self, total_frames: usize) -> bool {
        self.frame_padding_count(total_frames) != 0
    }
    /// Returns the number of padding frames needed for a given total number of frames.
    fn frame_padding_count(&self, total_frames: usize) -> usize {
        total_frames % self.reduction_count()
    }

    /// Returns the expected total number of iterations for the prover given raw iterations.
    fn expected_total_iterations(&self, raw_iterations: usize) -> usize {
        let raw_iterations = raw_iterations + 1;
        let cfc = self.reduction_count();
        let full_multiframe_count = raw_iterations / cfc;
        let unfull_multiframe_frame_count = raw_iterations % cfc;
        let raw_multiframe_count =
            full_multiframe_count + usize::from(unfull_multiframe_frame_count != 0);
        raw_multiframe_count + self.multiframe_padding_count(raw_multiframe_count)
    }

    /// Returns the number of padding multiframes needed for a given raw multiframe count.
    fn multiframe_padding_count(&self, _raw_multiframe_count: usize) -> usize {
        // By default, any number of multiframes is fine.
        0
    }
    /// Determines if the prover needs padding for a given raw multiframe count.
    fn needs_multiframe_padding(&self, raw_multiframe_count: usize) -> bool {
        self.multiframe_padding_count(raw_multiframe_count) != 0
    }

    /// Synthesizes the outer circuit for the prover given a slice of multiframes.
    fn outer_synthesize(&self, multiframes: &[M]) -> Result<SequentialCS<F, M>, SynthesisError> {
        // Note: This loop terminates and returns an error on the first occurrence of `SynthesisError`.
        multiframes
            .iter()
            .map(|multiframe| {
                let mut cs = TestConstraintSystem::new();

                multiframe
                    .clone()
                    .synthesize(&mut cs)
                    .map(|_| (multiframe.clone(), cs))
            })
            .collect::<Result<_, _>>()
    }
    /// Evaluates and generates the `Frame`s of the computation given the expression, environment, and store
    fn get_evaluation_frames(
        &self,
        expr: Ptr<F>,
        env: Ptr<F>,
        store: &Store<F>,
        limit: usize,
        lang: Arc<Lang<F, C>>,
    ) -> Result<Vec<Frame<IO<F>, Witness<F>, F, C>>, ProofError> {
        let padding_predicate = |count| self.needs_frame_padding(count);

        let frames = Evaluator::generate_frames(expr, env, store, limit, padding_predicate, &lang)?;

        store.hydrate_scalar_cache();

        Ok(frames)
    }
}

/// Supertrait for `Prover` that also supports NIVC.
pub trait NIVCProver<'a, F: LurkField, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>>:
    Prover<'a, F, C, M>
{
}
