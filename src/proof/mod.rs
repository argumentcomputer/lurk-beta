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

use ::nova::traits::Engine;
use std::sync::Arc;

use crate::{
    coprocessor::Coprocessor,
    error::ProofError,
    eval::lang::Lang,
    field::LurkField,
    lem::{eval::EvalConfig, interpreter::Frame, pointers::Ptr, store::Store},
    proof::nova::E2,
};

use self::{
    nova::{CurveCycleEquipped, C1LEM},
    supernova::FoldingConfig,
};

/// The State of a CEK machine.
pub trait CEKState<Ptr> {
    /// the expression, or control word (C)
    fn expr(&self) -> &Ptr;
    /// the environment (E)
    fn env(&self) -> &Ptr;
    /// the continuation (K)
    fn cont(&self) -> &Ptr;
}

/// A Frame of evaluation in a CEK machine.
pub trait FrameLike<Ptr>: Sized {
    /// the type for the Frame's IO
    type FrameIO: CEKState<Ptr>;
    /// the input of the frame
    fn input(&self) -> &Self::FrameIO;
    /// the output of the frame
    fn output(&self) -> &Self::FrameIO;
}

/// A trait for a store of expressions
pub trait EvaluationStore {
    /// the type for the Store's pointers
    type Ptr;
    /// the type for the Store's errors
    type Error: std::fmt::Debug;

    /// interpreting a string representation of an expression
    fn read(&self, expr: &str) -> Result<Self::Ptr, Self::Error>;
    /// getting a pointer to the initial, empty environment
    fn initial_empty_env(&self) -> Self::Ptr;
    /// getting the terminal continuation pointer
    fn get_cont_terminal(&self) -> Self::Ptr;

    /// cache hashes for pointers enqueued for hydration
    fn hydrate_z_cache(&self);

    /// hash-equality of the expressions represented by Ptrs
    fn ptr_eq(&self, left: &Self::Ptr, right: &Self::Ptr) -> bool;
}

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
pub trait RecursiveSNARKTrait<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>
where
    Self: Sized,
{
    /// Associated type for public parameters
    type PublicParams;

    /// Type for error potentially thrown during verification
    type ErrorType;

    /// Generate the recursive SNARK, encoded in `ProveOutput`
    fn prove_recursively(
        pp: &'a Self::PublicParams,
        z0: &[F],
        steps: Vec<C1LEM<'a, F, C>>,
        store: &'a Store<F>,
        reduction_count: usize,
        lang: Arc<Lang<F, C>>,
    ) -> Result<Self, ProofError>;

    /// Compress a proof
    fn compress(self, pp: &Self::PublicParams) -> Result<Self, ProofError>;

    /// Verify the proof given the public parameters, the input and output values
    fn verify(&self, pp: &Self::PublicParams, z0: &[F], zi: &[F]) -> Result<bool, Self::ErrorType>;

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
pub trait Prover<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a> {
    /// Associated type for public parameters
    type PublicParams;

    /// Assiciated proof type, which must implement `RecursiveSNARKTrait`
    type RecursiveSnark: RecursiveSNARKTrait<'a, F, C, PublicParams = Self::PublicParams>;

    /// Returns a reference to the prover's FoldingMode
    fn folding_mode(&self) -> &FoldingMode;

    /// Returns the number of reductions for the prover.
    fn reduction_count(&self) -> usize;

    /// Returns a reference to the Prover's Lang.
    fn lang(&self) -> &Arc<Lang<F, C>>;

    /// Generate a proof from a sequence of frames
    fn prove(
        &self,
        pp: &'a Self::PublicParams,
        frames: &[Frame],
        store: &'a Store<F>,
    ) -> Result<(Self::RecursiveSnark, Vec<F>, Vec<F>, usize), ProofError> {
        store.hydrate_z_cache();
        let z0 = store.to_scalar_vector(frames[0].input());
        let zi = store.to_scalar_vector(frames.last().unwrap().output());

        let lang = self.lang().clone();
        let folding_config = self
            .folding_mode()
            .folding_config(lang.clone(), self.reduction_count());

        let steps = C1LEM::<'a, F, C>::from_frames(frames, store, &folding_config.into());
        let num_steps = steps.len();

        let prove_output = Self::RecursiveSnark::prove_recursively(
            pp,
            &z0,
            steps,
            store,
            self.reduction_count(),
            lang,
        )?;

        Ok((prove_output, z0, zi, num_steps))
    }

    /// Evaluate an expression with an environment and then generate the corresponding proof
    fn evaluate_and_prove(
        &self,
        pp: &'a Self::PublicParams,
        expr: Ptr,
        env: Ptr,
        store: &'a Store<F>,
        limit: usize,
    ) -> Result<(Self::RecursiveSnark, Vec<F>, Vec<F>, usize), ProofError> {
        let eval_config = self.folding_mode().eval_config(self.lang());
        let frames = C1LEM::<'a, F, C>::build_frames(expr, env, store, limit, &eval_config)?;
        self.prove(pp, &frames, store)
    }

    /// Returns the expected total number of steps for the prover given raw iterations.
    fn expected_num_steps(&self, raw_iterations: usize) -> usize {
        let rc = self.reduction_count();
        let full_multiframe_count = raw_iterations / rc;
        let unfull_multiframe_frame_count = raw_iterations % rc;
        full_multiframe_count + usize::from(unfull_multiframe_frame_count != 0)
    }
}
