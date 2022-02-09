pub mod groth16;

use bellperson::util_cs::test_cs::TestConstraintSystem;
use bellperson::SynthesisError;

use crate::circuit::CircuitFrame;
use crate::eval::{Frame, Witness, IO};
use crate::store::{ScalarPointer, Store};
use ff::PrimeField;
pub(crate) type SequentialCS<F, IO, Witness> = Vec<(Frame<IO, Witness>, TestConstraintSystem<F>)>;

pub trait Provable<F: PrimeField> {
    fn public_inputs(&self, store: &Store<F>) -> Vec<F>;
    fn public_input_size() -> usize;
}

impl<F: PrimeField> IO<F> {
    fn public_inputs(&self, store: &Store<F>) -> Vec<F> {
        let expr = store.hash_expr(&self.expr).unwrap();
        let env = store.hash_expr(&self.env).unwrap();
        let cont = store.hash_cont(&self.cont).unwrap();
        let public_inputs = vec![
            *expr.tag(),
            *expr.value(),
            *env.tag(),
            *env.value(),
            *cont.tag(),
            *cont.value(),
        ];

        // This ensures `public_input_size` is kept in sync with any changes.
        assert_eq!(Self::public_input_size(), public_inputs.len());
        public_inputs
    }
    fn public_input_size() -> usize {
        6
    }
}

impl<F: PrimeField, W> Provable<F> for CircuitFrame<'_, F, IO<F>, W> {
    fn public_inputs(&self, store: &Store<F>) -> Vec<F> {
        let mut inputs: Vec<_> = Vec::with_capacity(10);

        if let Some(input) = &self.input {
            inputs.extend(input.public_inputs(store));
        }
        if let Some(output) = &self.output {
            inputs.extend(output.public_inputs(store));
        }

        inputs
    }

    fn public_input_size() -> usize {
        let input_output_size = IO::<F>::public_input_size();
        input_output_size * 2
    }
}

impl<F: PrimeField, T: PartialEq + std::fmt::Debug, W> CircuitFrame<'_, F, T, W> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        self.output == maybe_next.input
    }
}

#[allow(dead_code)]
fn verify_sequential_css<F: PrimeField>(
    css: &SequentialCS<F, IO<F>, Witness<F>>,
    store: &Store<F>,
) -> Result<bool, SynthesisError> {
    let mut previous_frame: Option<&Frame<IO<F>, Witness<F>>> = None;

    for (_i, (frame, cs)) in css.iter().enumerate() {
        if let Some(prev) = previous_frame {
            if !prev.precedes(frame) {
                dbg!("not preceeding frame");
                return Ok(false);
            }
        }
        if !cs.is_satisfied() {
            dbg!("cs not satisfied");
            return Ok(false);
        }

        let public_inputs =
            CircuitFrame::<F, _, _>::from_frame(frame.clone(), store).public_inputs(store);

        if !cs.verify(&public_inputs) {
            dbg!("cs not verified");
            return Ok(false);
        }
        previous_frame = Some(frame);
    }
    Ok(true)
}
