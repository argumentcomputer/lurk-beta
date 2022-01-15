use bellperson::util_cs::test_cs::TestConstraintSystem;
use bellperson::{
    groth16::{self, verify_proof},
    util_cs::metric_cs::MetricCS,
    Circuit, ConstraintSystem, SynthesisError,
};
use blstrs::{Bls12, Scalar as Fr};
use once_cell::sync::OnceCell;
use pairing_lib::Engine;

use crate::data::{fr_from_u64, Continuation, Expression, Store, Tagged};

use crate::eval::{outer_evaluate_iterator, Control, Frame, Witness, IO};

use rand::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;
use std::sync::Mutex;

static FRAME_GROTH_PARAMS: OnceCell<groth16::Parameters<Bls12>> = OnceCell::new();

pub const DUMMY_RNG_SEED: [u8; 16] = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];

pub trait Provable {
    fn public_inputs(&self) -> Vec<Fr>;
}

#[derive(Clone)]
pub struct Proof<E: Engine> {
    groth16_proof: groth16::Proof<E>,
}

impl<W> Provable for Frame<IO, W> {
    fn public_inputs(&self) -> Vec<Fr> {
        let mut inputs: Vec<Fr> = Vec::with_capacity(10);

        if let Some(input) = &self.input {
            inputs.extend(input.public_inputs());
        }
        if let Some(output) = &self.output {
            inputs.extend(output.public_inputs());
        }
        if let Some(initial) = &self.initial {
            inputs.extend(initial.public_inputs());
        }
        if let Some(i) = self.i {
            inputs.push(fr_from_u64(i as u64));
        }

        inputs
    }
}

impl IO {
    fn public_inputs(&self) -> Vec<Fr> {
        vec![
            self.expr.tag_fr(),
            self.expr.get_hash(),
            self.env.tag_fr(),
            self.env.get_hash(),
            self.cont.get_continuation_tag().cont_tag_fr(),
            self.cont.get_hash(),
        ]
    }
}

impl Frame<IO, Witness> {
    pub fn blank() -> Self {
        Self {
            input: None,
            output: None,
            initial: None,
            i: None,
            witness: None,
        }
    }

    fn frame_groth_params(self) -> Result<groth16::Parameters<Bls12>, SynthesisError> {
        if let Some(params) = FRAME_GROTH_PARAMS.get() {
            Ok(params.clone())
        } else {
            let rng = &mut XorShiftRng::from_seed(DUMMY_RNG_SEED);
            let params = groth16::generate_random_parameters::<Bls12, _, _>(self, rng)?;
            FRAME_GROTH_PARAMS.set(params.clone());
            Ok(params)
        }
    }

    pub fn groth_params() -> Result<groth16::Parameters<Bls12>, SynthesisError> {
        Self::blank().frame_groth_params()
    }

    pub fn prove<R: RngCore>(
        self,
        params: Option<&groth16::Parameters<Bls12>>,
        mut rng: R,
    ) -> Result<Proof<Bls12>, SynthesisError> {
        Ok(Proof {
            groth16_proof: Self::generate_groth16_proof(self, params, &mut rng)?,
        })
    }

    pub fn outer_prove<R: RngCore + Clone>(
        params: &groth16::Parameters<Bls12>,
        expr: Expression,
        env: Expression,
        store: &mut Store,
        limit: usize,
        mut rng: R,
    ) -> Result<SequentialProofs<Bls12, IO, Witness>, SynthesisError> {
        Ok(outer_evaluate_iterator(expr, env, store, limit)
            // FIXME: Don't clone the RNG.
            .map(|frame| {
                (
                    frame.clone(),
                    frame.prove(Some(params), rng.clone()).unwrap(),
                )
            })
            .collect::<Vec<_>>())
    }

    pub fn outer_synthesize(
        expr: Expression,
        env: Expression,
        store: &mut Store,
        limit: usize,
    ) -> Result<SequentialCS<IO, Witness>, SynthesisError> {
        Ok(outer_evaluate_iterator(expr, env, store, limit)
            .map(|frame| {
                let mut cs = TestConstraintSystem::new();
                frame.clone().synthesize(&mut cs).unwrap();
                (frame, cs)
            })
            .collect::<Vec<_>>())
    }
}

type SequentialProofs<E, IO, Witness> = Vec<(Frame<IO, Witness>, Proof<E>)>;
type SequentialCS<IO, Witness> = Vec<(Frame<IO, Witness>, TestConstraintSystem<Fr>)>;

fn verify_sequential_groth16_proofs(
    proofs: SequentialProofs<Bls12, IO, Witness>,
    vk: groth16::VerifyingKey<Bls12>,
) -> Result<bool, SynthesisError> {
    let mut previous_frame: Option<&Frame<IO, Witness>> = None;

    for (i, (frame, proof)) in proofs.iter().enumerate() {
        dbg!(i);
        if let Some(prev) = previous_frame {
            if !prev.precedes(frame) {
                return Ok(false);
            }
        }

        let pvk = groth16::prepare_verifying_key(&vk);
        if !Frame::verify_groth16_proof(pvk, proof.clone(), frame.clone())? {
            return Ok(false);
        }
    }

    // TODO: Check that the last frame's initial field equals the first frames input.

    Ok(true)
}

#[allow(clippy::ptr_arg)]
fn verify_sequential_css(css: &SequentialCS<IO, Witness>) -> Result<bool, SynthesisError> {
    let mut previous_frame: Option<&Frame<IO, Witness>> = None;

    for (i, (frame, cs)) in css.iter().enumerate() {
        dbg!(i);
        if let Some(w) = &frame.witness {
            if let Some(s) = &w.store {
                if let Some(input) = &frame.input {
                    dbg!(s.write_expr_str(&input.expr));
                } else {
                    dbg!("no input");
                }
            } else {
                dbg!("no witness");
            }
        } else {
            dbg!("no frame");
        };

        if let Some(prev) = previous_frame {
            if !prev.precedes(frame) {
                return Ok(false);
            }
        }

        let public_inputs = frame.public_inputs();

        if !(cs.is_satisfied() && cs.verify(&public_inputs)) {
            return Ok(false);
        }
        previous_frame = Some(frame);
    }
    Ok(true)
}

impl Frame<IO, Witness> {
    pub fn generate_groth16_proof<R: RngCore>(
        self,
        groth_params: Option<&groth16::Parameters<Bls12>>,
        rng: &mut R,
    ) -> Result<groth16::Proof<Bls12>, SynthesisError> {
        let create_proof = |p| groth16::create_random_proof(self, p, rng);

        if let Some(params) = groth_params {
            create_proof(params)
        } else {
            create_proof(&Frame::<IO, Witness>::groth_params()?)
        }
    }

    pub fn verify_groth16_proof(
        pvk: groth16::PreparedVerifyingKey<Bls12>,
        p: Proof<Bls12>,
        f: Frame<IO, Witness>,
    ) -> Result<bool, SynthesisError> {
        let inputs = f.public_inputs();

        verify_proof(&pvk, &p.groth16_proof, &inputs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::empty_sym_env;
    use bellperson::util_cs::{metric_cs::MetricCS, Comparable, Delta};

    const DEFAULT_CHECK_GROTH16: bool = false;

    fn outer_prove_aux(
        source: &str,
        expected_result: Expression,
        expected_iterations: usize,
        check_groth16: bool,
        check_constraint_systems: bool,
        limit: usize,
        debug: bool,
    ) {
        let mut rng = rand::thread_rng();

        let mut s = Store::default();
        let expr = s.read(source).unwrap();

        let groth_params = Frame::groth_params().unwrap();
        let vk = &groth_params.vk;

        let proofs = if check_groth16 {
            Some(
                Frame::outer_prove(
                    &groth_params,
                    expr.clone(),
                    empty_sym_env(&s),
                    &mut s,
                    limit,
                    rng,
                )
                .unwrap(),
            )
        } else {
            None
        };

        let constraint_systems = if check_constraint_systems {
            Some(Frame::outer_synthesize(expr, empty_sym_env(&s), &mut s, limit).unwrap())
        } else {
            None
        };

        if let Some(proofs) = proofs {
            if !debug {
                assert_eq!(expected_iterations, proofs.len());
                assert_eq!(
                    expected_result,
                    proofs[proofs.len() - 1].0.output.as_ref().unwrap().expr
                );
            }
            let proofs_verified =
                verify_sequential_groth16_proofs(proofs, groth_params.vk).unwrap();
            assert!(proofs_verified);
        };

        if let Some(cs) = constraint_systems {
            if !debug {
                assert_eq!(expected_iterations, cs.len());
                assert_eq!(
                    expected_result,
                    cs[cs.len() - 1].0.output.as_ref().unwrap().expr
                );
            }
            let constraint_systems_verified = verify_sequential_css(&cs).unwrap();
            assert!(constraint_systems_verified);

            check_cs_deltas(&cs, limit);
        };
    }

    pub fn check_cs_deltas(constraint_systems: &SequentialCS<IO, Witness>, limit: usize) -> () {
        let mut cs_blank = MetricCS::<Fr>::new();
        let blank_frame = Frame::blank();
        blank_frame
            .synthesize(&mut cs_blank)
            .expect("failed to synthesize");

        for (i, (_frame, cs)) in constraint_systems.iter().take(limit).enumerate() {
            let delta = cs.delta(&cs_blank, true);
            dbg!(i, &delta);
            assert!(delta == Delta::Equal);
        }
    }

    #[test]
    fn outer_prove_arithmetic_let() {
        outer_prove_aux(
            &"(let* ((a 5)
                     (b 1)
                     (c 2))
                (/ (+ a b) c))",
            Expression::num(3),
            24,
            true, // Always check Groth16 in at least one test.
            true,
            100,
            false,
        );
    }

    #[test]
    fn outer_prove_binop() {
        outer_prove_aux(
            &"(+ 1 2)",
            Expression::num(3),
            5,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        );
    }

    #[test]
    fn outer_prove_eq() {
        outer_prove_aux(
            &"(eq 5 5)",
            Expression::Sym("T".to_string()),
            5,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        );

        // outer_prove_aux(&"(eq 5 6)", Expression::Nil, 5, false, true, 100, false);
    }

    #[test]
    fn outer_prove_num_equal() {
        outer_prove_aux(
            &"(= 5 5)",
            Expression::Sym("T".to_string()),
            5,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        );
        outer_prove_aux(
            &"(= 5 6)",
            Expression::Nil,
            5,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        );
    }

    #[test]
    fn outer_prove_if() {
        outer_prove_aux(
            &"(if t 5 6)",
            Expression::num(5),
            4,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        );

        outer_prove_aux(
            &"(if t 5 6)",
            Expression::num(5),
            4,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        )
    }
    #[test]
    fn outer_prove_if_fully_evaluates() {
        outer_prove_aux(
            &"(if t (+ 5 5) 6)",
            Expression::num(10),
            8,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        );
    }

    #[test]
    #[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
    fn outer_prove_recursion1() {
        outer_prove_aux(
            &"(letrec* ((exp (lambda (base)
                               (lambda (exponent)
                                 (if (= 0 exponent)
                                     1
                                     (* base ((exp base) (- exponent 1))))))))
                ((exp 5) 3))",
            Expression::num(125),
            117,
            DEFAULT_CHECK_GROTH16,
            true,
            200,
            false,
        );
    }

    #[test]
    #[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
    fn outer_prove_recursion2() {
        outer_prove_aux(
            &"(letrec* ((exp (lambda (base)
                                  (lambda (exponent)
                                     (lambda (acc)
                                       (if (= 0 exponent)
                                          acc
                                          (((exp base) (- exponent 1)) (* acc base))))))))
                (((exp 5) 5) 1))",
            Expression::num(3125),
            248,
            DEFAULT_CHECK_GROTH16,
            true,
            300,
            false,
        );
    }
}
