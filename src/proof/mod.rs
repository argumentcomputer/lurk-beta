#![deny(missing_docs)]

//! This module offers a connection the the backend proving engine of Lurk.
//! Abstracted behind the `Prover` and `Verifier` traits, the proving engine
//! has two instantiations:
//! - the Nova proving system, implemented in the `nova` module.
//! - the SuperNova proving system, implemented in the `supernova` module.

/// An adapter to a Nova proving system implementation.
pub mod nova;

/// An adapter to a SuperNova proving system implementation.
pub mod supernova;

#[cfg(test)]
mod tests;

use ::nova::traits::{circuit::StepCircuit, Engine};
use bellpepper::util_cs::witness_cs::WitnessCS;
use bellpepper_core::{
    num::AllocatedNum, test_cs::TestConstraintSystem, Circuit, ConstraintSystem, SynthesisError,
};
use std::sync::Arc;

use crate::{
    coprocessor::Coprocessor, error::ProofError, eval::lang::Lang, field::LurkField,
    lem::eval::EvalConfig, proof::nova::E2,
};

use self::{nova::CurveCycleEquipped, supernova::FoldingConfig};

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

    /// cache hashes for pointers enqueued for hydration
    fn hydrate_z_cache(&self);

    /// hash-equality of the expressions represented by Ptrs
    fn ptr_eq(&self, left: &Self::Ptr, right: &Self::Ptr) -> bool;
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
    fn build_frames(
        expr: Self::Ptr,
        env: Self::Ptr,
        store: &Self::Store,
        limit: usize,
        ec: &EvalConfig<'_, F, C>,
    ) -> Result<Vec<Self::EvalFrame>, ProofError>;

    /// Returns a public IO vector when equipped with the local store, and the Self::Frame's IO
    fn io_to_scalar_vector(
        store: &Self::Store,
        io: &<Self::EvalFrame as FrameLike<Self::Ptr, Self::ContPtr>>::FrameIO,
    ) -> Vec<F>;

    /// Returns true if the supplied instance directly precedes this one in a sequential computation trace.
    fn precedes(&self, maybe_next: &Self) -> bool;

    /// Populates a WitnessCS with the witness values for the given store, also returning the allocated output.
    fn compute_witness(
        &self,
        s: &Self::Store,
    ) -> Result<(WitnessCS<F>, Vec<AllocatedNum<F>>), SynthesisError>;

    /// Returns a reference to the cached witness values
    fn cached_witness(&mut self) -> &mut Option<(WitnessCS<F>, Vec<AllocatedNum<F>>)>;

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
    ) -> Result<Self::AllocatedIO, SynthesisError>;

    /// Synthesize a blank circuit.
    fn blank(folding_config: Arc<FoldingConfig<F, C>>, pc: usize) -> Self;

    /// Create an instance from some `Self::Frame`s.
    fn from_frames(
        frames: &[Self::EvalFrame],
        store: &'a Self::Store,
        folding_config: Arc<FoldingConfig<F, C>>,
    ) -> Vec<Self>;
}

/// Represents a sequential Constraint System for a given proof.
pub(crate) type SequentialCS<F, M> = Vec<(M, TestConstraintSystem<F>)>;

/// A trait for provable structures over a field `F`.
pub trait Provable<F: LurkField> {
    /// Returns the public inputs of the provable structure.
    fn public_inputs(&self) -> Vec<F>;
    /// Returns the size of the public inputs.
    fn public_input_size(&self) -> usize;
    /// Returns the number of reduction frames in the provable structure.
    fn num_frames(&self) -> usize;
}

// Next we have two traits:
// * `RecursiveSNARKTrait`, which abstracts over Nova and a SuperNova proofs
// * `Prover`, which abstracts over Nova and SuperNova provers

/// Trait to abstract Nova and SuperNova proofs
pub trait RecursiveSNARKTrait<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
> where
    Self: Sized,
{
    /// Associated type for public parameters
    type PublicParams;

    /// Main output of `prove_recursively`, encoding the actual proof
    type ProveOutput;

    /// Extra input for `verify` to be defined as needed
    type ExtraVerifyInput;

    /// Type for error potentially thrown during verification
    type ErrorType;

    /// Generate the recursive SNARK, encoded in `ProveOutput`
    fn prove_recursively(
        pp: &Self::PublicParams,
        z0: &[F],
        steps: &[M],
        store: &'a M::Store,
        reduction_count: usize,
        lang: Arc<Lang<F, C>>,
    ) -> Result<Self::ProveOutput, ProofError>;

    /// Compress a proof
    fn compress(self, pp: &Self::PublicParams) -> Result<Self, ProofError>;

    /// Verify the proof given the public parameters, the input and output values
    /// and the extra custom argument defined by who implements this trait.
    fn verify(
        &self,
        pp: &Self::PublicParams,
        z0: &[F],
        zi: &[F],
        extra: Self::ExtraVerifyInput,
    ) -> Result<bool, Self::ErrorType>;

    /// Return the `z0_secondary`
    #[inline]
    fn z0_secondary() -> Vec<<F::E2 as Engine>::Scalar> {
        use ff::Field;
        vec![<E2<F> as Engine>::Scalar::ZERO]
    }
}

/// Folding mode used for proving
#[derive(Debug)]
pub enum FoldingMode {
    /// Variant for IVC folding
    IVC,
    /// Variant for NIVC folding
    NIVC,
}

impl FoldingMode {
    fn folding_config<F: LurkField, C: Coprocessor<F>>(
        &self,
        lang: Arc<Lang<F, C>>,
        reduction_count: usize,
    ) -> FoldingConfig<F, C> {
        match self {
            Self::IVC => FoldingConfig::new_ivc(lang, reduction_count),
            Self::NIVC => FoldingConfig::new_nivc(lang, reduction_count),
        }
    }

    fn eval_config<'a, F: LurkField, C: Coprocessor<F>>(
        &self,
        lang: &'a Lang<F, C>,
    ) -> EvalConfig<'a, F, C> {
        match self {
            Self::IVC => EvalConfig::new_ivc(lang),
            Self::NIVC => EvalConfig::new_nivc(lang),
        }
    }
}

/// A trait for a prover that works with a field `F`.
pub trait Prover<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>> {
    /// Associated type for public parameters
    type PublicParams;

    /// Main output of `prove`, encoding the actual proof
    type ProveOutput;

    /// Assiciated proof type, which must implement `RecursiveSNARKTrait`
    type RecursiveSnark: RecursiveSNARKTrait<
        'a,
        F,
        C,
        M,
        PublicParams = Self::PublicParams,
        ProveOutput = Self::ProveOutput,
    >;

    /// Returns a reference to the prover's FoldingMode
    fn folding_mode(&self) -> &FoldingMode;

    /// Returns the number of reductions for the prover.
    fn reduction_count(&self) -> usize;

    /// Returns a reference to the Prover's Lang.
    fn lang(&self) -> &Arc<Lang<F, C>>;

    /// Generate a proof from a sequence of frames
    fn prove(
        &self,
        pp: &Self::PublicParams,
        frames: &[M::EvalFrame],
        store: &'a M::Store,
    ) -> Result<(Self::ProveOutput, Vec<F>, Vec<F>, usize), ProofError> {
        store.hydrate_z_cache();
        let z0 = M::io_to_scalar_vector(store, frames[0].input());
        let zi = M::io_to_scalar_vector(store, frames.last().unwrap().output());

        let lang = self.lang().clone();
        let folding_config = self
            .folding_mode()
            .folding_config(lang.clone(), self.reduction_count());

        let steps = M::from_frames(frames, store, folding_config.into());

        let prove_output = Self::RecursiveSnark::prove_recursively(
            pp,
            &z0,
            &steps,
            store,
            self.reduction_count(),
            lang,
        )?;

        Ok((prove_output, z0, zi, steps.len()))
    }

    /// Evaluate an expression with an environment and then generate the corresponding proof
    fn evaluate_and_prove(
        &self,
        pp: &Self::PublicParams,
        expr: M::Ptr,
        env: M::Ptr,
        store: &'a M::Store,
        limit: usize,
    ) -> Result<(Self::ProveOutput, Vec<F>, Vec<F>, usize), ProofError> {
        let eval_config = self.folding_mode().eval_config(self.lang());
        let frames = M::build_frames(expr, env, store, limit, &eval_config)?;
        self.prove(pp, &frames, store)
    }

    /// Returns the expected total number of steps for the prover given raw iterations.
    fn expected_num_steps(&self, raw_iterations: usize) -> usize {
        let rc = self.reduction_count();
        let full_multiframe_count = raw_iterations / rc;
        let unfull_multiframe_frame_count = raw_iterations % rc;
        full_multiframe_count + usize::from(unfull_multiframe_frame_count != 0)
    }

    /// Synthesizes the outer circuit for the prover given a slice of multiframes.
    fn outer_synthesize(&self, multiframes: &[M]) -> Result<SequentialCS<F, M>, SynthesisError> {
        // TODO: do we need this?
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
}
