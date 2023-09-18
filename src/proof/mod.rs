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

use crate::circuit::MultiFrame;
use crate::coprocessor::Coprocessor;
use crate::error::ProofError;
use crate::eval::{lang::Lang, Evaluator, Frame, Witness, IO};
use crate::field::LurkField;

use crate::ptr::Ptr;
use crate::store::Store;
use bellpepper_core::{test_cs::TestConstraintSystem, Circuit, SynthesisError};
use std::sync::Arc;

/// Represents a sequential Constraint System for a given proof.
pub(crate) type SequentialCS<'a, F, C> = Vec<(MultiFrame<'a, F, C>, TestConstraintSystem<F>)>;

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
pub fn verify_sequential_css<F: LurkField + Copy, C: Coprocessor<F>>(
    css: &SequentialCS<'_, F, C>,
) -> Result<bool, SynthesisError> {
    let mut previous_frame: Option<&MultiFrame<'_, F, C>> = None;

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
pub trait Prover<'a, F: LurkField, C: Coprocessor<F>> {
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
    fn outer_synthesize(
        &self,
        multiframes: &'a [MultiFrame<'_, F, C>],
    ) -> Result<SequentialCS<'a, F, C>, SynthesisError> {
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
        store: &mut Store<F>,
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
pub trait NIVCProver<'a, F: LurkField, C: Coprocessor<F>>: Prover<'a, F, C> {}
