pub mod groth16;
pub mod nova;

use bellperson::{util_cs::test_cs::TestConstraintSystem, Circuit, SynthesisError};

use crate::circuit::MultiFrame;
use crate::eval::{Witness, IO};
use crate::field::LurkField;

pub(crate) type SequentialCS<'a, F, IO, Witness> =
    Vec<(MultiFrame<'a, F, IO, Witness>, TestConstraintSystem<F>)>;

pub trait Provable<F: LurkField> {
    fn public_inputs(&self) -> Vec<F>;
    fn public_input_size() -> usize;
    fn reduction_count(&self) -> usize;
}

#[allow(dead_code)]
pub fn verify_sequential_css<F: LurkField + Copy>(
    css: &SequentialCS<F, IO<F>, Witness<F>>,
) -> Result<bool, SynthesisError> {
    let mut previous_frame: Option<&MultiFrame<F, IO<F>, Witness<F>>> = None;

    for (i, (multiframe, cs)) in css.iter().enumerate() {
        if let Some(prev) = previous_frame {
            if !prev.precedes(multiframe) {
                dbg!(i, "not preceeding frame");
                return Ok(false);
            }
        }
        if !cs.is_satisfied() {
            dbg!(i, "cs not satisfied");
            return Ok(false);
        }

        let public_inputs = multiframe.public_inputs();
        if !cs.verify(&public_inputs) {
            dbg!(i, "cs not verified");
            return Ok(false);
        }
        previous_frame = Some(multiframe);
    }
    Ok(true)
}
pub trait PublicParameters {}

pub trait Prover<'a, F: LurkField> {
    type PublicParams: PublicParameters;

    fn new(reduction_count: usize) -> Self;

    fn reduction_count(&self) -> usize;

    fn needs_frame_padding(&self, total_frames: usize) -> bool {
        self.frame_padding_count(total_frames) != 0
    }
    fn frame_padding_count(&self, total_frames: usize) -> usize {
        total_frames % self.reduction_count()
    }

    fn expected_total_iterations(&self, raw_iterations: usize) -> usize {
        let raw_iterations = raw_iterations + 1;
        let cfc = self.reduction_count();
        let full_multiframe_count = raw_iterations / cfc;
        let unfull_multiframe_frame_count = raw_iterations % cfc;
        let raw_multiframe_count =
            full_multiframe_count + (unfull_multiframe_frame_count != 0) as usize;
        raw_multiframe_count + self.multiframe_padding_count(raw_multiframe_count)
    }

    fn multiframe_padding_count(&self, _raw_multiframe_count: usize) -> usize {
        // By default, any number of multiframes is fine.
        0
    }
    fn needs_multiframe_padding(&self, raw_multiframe_count: usize) -> bool {
        self.multiframe_padding_count(raw_multiframe_count) != 0
    }

    fn outer_synthesize(
        &self,
        multiframes: &'a [MultiFrame<F, IO<F>, Witness<F>>],
    ) -> Result<SequentialCS<'a, F, IO<F>, Witness<F>>, SynthesisError> {
        let res = multiframes
            .iter()
            .enumerate()
            .map(|(_, multiframe)| {
                let mut cs = TestConstraintSystem::new();

                multiframe.clone().synthesize(&mut cs).unwrap(); // FIXME: unwrap
                (multiframe.clone(), cs)
            })
            .collect::<Vec<_>>();
        Ok(res)
    }
}
