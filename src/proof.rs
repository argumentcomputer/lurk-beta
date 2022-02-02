use bellperson::util_cs::test_cs::TestConstraintSystem;
use bellperson::{
    groth16::{
        self,
        aggregate::{aggregate_proofs, setup_fake_srs, AggregateProof, GenericSRS, ProverSRS},
        verify_proof,
    },
    Circuit, SynthesisError,
};
use blstrs::{Bls12, Scalar as Fr};
use ff::PrimeField;
use once_cell::sync::{Lazy, OnceCell};
use pairing_lib::{Engine, MultiMillerLoop};
use rand::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;

use crate::circuit::CircuitFrame;
use crate::eval::{Evaluator, Frame, Witness, IO};
use crate::store::{Ptr, ScalarPointer, Store};

use std::env;
use std::fs::File;
use std::io;

const DUMMY_RNG_SEED: [u8; 16] = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];

pub static INNER_PRODUCT_SRS: Lazy<GenericSRS<Bls12>> = Lazy::new(|| load_srs().unwrap());
static FRAME_GROTH_PARAMS: OnceCell<groth16::Parameters<Bls12>> = OnceCell::new();
const MAX_FAKE_SRS_SIZE: usize = 2 << 20;

// If you don't have a real SnarkPack SRS symlinked, generate a fake one.
// Don't use this in production!
const FALLBACK_TO_FAKE_SRS: bool = true;

type SequentialProofs<'a, E, IO, Witness> = Vec<(CircuitFrame<'a, IO, Witness>, groth16::Proof<E>)>;
type SequentialCS<IO, Witness> = Vec<(Frame<IO, Witness>, TestConstraintSystem<Fr>)>;
type FrameProofs<'a, E, IO, Witness> = (Proof<'a, E, CircuitFrame<'a, IO, Witness>>, Vec<Vec<Fr>>);

fn load_srs() -> Result<GenericSRS<Bls12>, io::Error> {
    let path = env::current_dir()?.join("params/v28-fil-inner-product-v1.srs");
    let mut rng = rand::thread_rng();
    let f = File::open(path);

    match f {
        Ok(mut f) => GenericSRS::read(&mut f),
        Err(e) => {
            if FALLBACK_TO_FAKE_SRS {
                Ok(setup_fake_srs::<Bls12, _>(&mut rng, MAX_FAKE_SRS_SIZE))
            } else {
                Err(e)
            }
        }
    }
}

pub trait Provable<F: PrimeField> {
    fn public_inputs(&self, store: &Store<F>) -> Vec<F>;
    fn extend_transcript(&self, transcript: &mut Vec<u8>, store: &Store<F>);
}

#[allow(dead_code)]
pub struct Proof<'a, E: Engine + MultiMillerLoop, F: Provable>
where
    <E as Engine>::Gt: blstrs::Compress,
{
    frame_proofs: SequentialProofs<'a, E, IO, Witness>,
    aggregated_proof: AggregateProof<E>,
    // FIXME: We shouldn't really include the transcript data in the proof,
    // but we also will not ultimately be including all the intermediate public inputs either.
    // Meanwhile, this is a simplification to allow verification.
    // Once we can do input/instance aggregation with SnarkPack,
    // get rid of this (and also the frame proofs.
    transcript_include: Vec<u8>,
    frames: Vec<F>,
}

impl<W> Provable<Fr> for CircuitFrame<'_, IO<Fr>, W> {
    fn public_inputs(&self, store: &Store<Fr>) -> Vec<Fr> {
        let mut inputs: Vec<Fr> = Vec::with_capacity(10);

        if let Some(input) = &self.input {
            inputs.extend(input.public_inputs(store));
        }
        if let Some(output) = &self.output {
            inputs.extend(output.public_inputs(store));
        }
        if let Some(initial) = &self.initial {
            inputs.extend(initial.public_inputs(store));
        }
        if let Some(i) = self.i {
            inputs.push(Fr::from(i as u64));
        }

        inputs
    }

    fn extend_transcript(&self, transcript: &mut Vec<u8>, store: &Store) {
        // TODO: Refactor to share code with `public_inputs` to avoid allocation.
        let inputs = self.public_inputs(store);

        for input in inputs {
            let bytes: [u8; 32] = input.to_repr();
            transcript.extend(bytes);
        }
    }
}

impl<T: PartialEq + std::fmt::Debug, W> CircuitFrame<'_, T, W> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        let sequential = self.i.unwrap() + 1 == maybe_next.i.unwrap();
        let io_match = self.output == maybe_next.input;

        sequential && io_match
    }
}

impl<F: PrimeField> IO<F> {
    fn public_inputs(&self, store: &Store<F>) -> Vec<F> {
        let expr = store.hash_expr(&self.expr).unwrap();
        let env = store.hash_expr(&self.env).unwrap();
        let cont = store.hash_cont(&self.cont).unwrap();
        vec![
            *expr.tag(),
            *expr.value(),
            *env.tag(),
            *env.value(),
            *cont.tag(),
            *cont.value(),
        ]
    }
}

impl<'a> CircuitFrame<'a, IO<Fr>, Witness<Fr>> {
    pub fn blank(store: &'a Store<Fr>) -> Self {
        Self {
            store,
            input: None,
            output: None,
            initial: None,
            i: None,
            witness: None,
        }
    }

    fn frame_groth_params(self) -> Result<&'static groth16::Parameters<Bls12>, SynthesisError> {
        let params = FRAME_GROTH_PARAMS.get_or_try_init::<_, SynthesisError>(|| {
            let rng = &mut XorShiftRng::from_seed(DUMMY_RNG_SEED);
            let params = groth16::generate_random_parameters::<Bls12, _, _>(self, rng)?;
            Ok(params)
        })?;
        Ok(params)
    }

    pub fn groth_params() -> Result<&'static groth16::Parameters<Bls12>, SynthesisError> {
        let store = Store::default();
        CircuitFrame::<IO<Fr>, Witness<Fr>>::blank(&store).frame_groth_params()
    }

    pub fn prove<R: RngCore>(
        self,
        params: Option<&groth16::Parameters<Bls12>>,
        mut rng: R,
    ) -> Result<groth16::Proof<Bls12>, SynthesisError> {
        Self::generate_groth16_proof(self, params, &mut rng)
    }

    #[allow(clippy::needless_collect)]
    pub fn outer_prove<R: RngCore + Clone>(
        params: &groth16::Parameters<Bls12>,
        srs: ProverSRS<Bls12>,
        expr: Ptr<Fr>,
        env: Ptr<Fr>,
        store: &'a mut Store<Fr>,
        limit: usize,
        rng: R,
    ) -> Result<FrameProofs<'a, Bls12, IO<Fr>, Witness<Fr>>, SynthesisError> {
        // FIXME: optimize execution order
        let mut evaluator = Evaluator::new(expr, env, store, limit);
        let initial = evaluator.initial();
        let mut transcript_include = Vec::new();
        let mut frames = evaluator.iter().collect::<Vec<_>>();
        let mut proofs = Vec::with_capacity(frames.len());
        let mut circuit_frames = Vec::with_capacity(frames.len());

        let mut public_inputs = Vec::with_capacity(frames.len());
        store.hydrate_scalar_cache();

        // NOTE: frame_proofs are not really needed, but having them helps with
        // testing and building confidence as we work up to fully succinct proofs.
        // Once these are removed a lot of the cloning and awkwardness of assembling
        // results here can be eliminated.
        let mut frame_proofs = Vec::with_capacity(frames.len());

        for frame in &frames {
            let circuit_frame = CircuitFrame::from_frame(initial.clone(), frame.clone(), store);
            public_inputs.push(circuit_frame.clone().public_inputs(store));
            circuit_frames.push(circuit_frame.clone());

            // FIXME: Don't clone the RNG (?).
            let proof = circuit_frame
                .clone()
                .prove(Some(params), rng.clone())
                .unwrap();
            proofs.push(proof.clone());

            circuit_frame.extend_transcript(&mut transcript_include, store);

            frame_proofs.push((circuit_frame, proof));
        }

        while proofs.len().count_ones() != 1 {
            // Pad proofs and frames to a power of 2.
            proofs.push(proofs[0].clone());
            frames.push(frames[0].clone());
            public_inputs.push(public_inputs[0].clone());
        }

        let aggregated_proof = aggregate_proofs(&srs, &transcript_include, proofs.as_slice())?;

        Ok((
            Proof {
                frame_proofs,
                aggregated_proof,
                transcript_include,
                frames: circuit_frames,
            },
            public_inputs,
        ))
    }

    #[allow(clippy::needless_collect)]
    pub fn outer_synthesize(
        expr: Ptr<Fr>,
        env: Ptr<Fr>,
        store: &mut Store<Fr>,
        limit: usize,
    ) -> Result<SequentialCS<IO<Fr>, Witness<Fr>>, SynthesisError> {
        let mut evaluator = Evaluator::new(expr, env, store, limit);
        let initial = evaluator.initial();
        let frames = evaluator.iter().collect::<Vec<_>>();

        store.hydrate_scalar_cache();

        let res = frames
            .into_iter()
            .map(|frame| {
                let mut cs = TestConstraintSystem::new();
                CircuitFrame::from_frame(initial.clone(), frame.clone(), store)
                    .synthesize(&mut cs)
                    .unwrap();
                (frame, cs)
            })
            .collect::<Vec<_>>();
        Ok(res)
    }
}

#[allow(dead_code)]
fn verify_sequential_groth16_proofs(
    frame_proofs: SequentialProofs<Bls12, IO<Fr>, Witness<Fr>>,
    vk: &groth16::VerifyingKey<Bls12>,
    store: &Store<Fr>,
) -> Result<bool, SynthesisError> {
    let previous_frame: Option<&CircuitFrame<IO<Fr>, Witness<Fr>>> = None;
    let pvk = groth16::prepare_verifying_key(vk);
    let initial = frame_proofs[0].0.input.clone();
    let retained = frame_proofs[frame_proofs.len() - 1].0.initial.clone();

    for (i, (frame, proof)) in frame_proofs.into_iter().enumerate() {
        dbg!(i);
        if let Some(prev) = previous_frame {
            if !prev.precedes(&frame) {
                return Ok(false);
            }
        }

        if !frame.verify_groth16_proof(&pvk, proof.clone())? {
            return Ok(false);
        }
    }

    Ok(initial == retained)
}

#[allow(dead_code)]
fn verify_sequential_css(
    css: &SequentialCS<IO<Fr>, Witness<Fr>>,
    store: &Store<Fr>,
) -> Result<bool, SynthesisError> {
    let mut previous_frame: Option<&Frame<IO<Fr>, Witness<Fr>>> = None;
    let initial = css[0].0.input.clone();

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
            CircuitFrame::from_frame(initial.clone(), frame.clone(), store).public_inputs(store);

        if !cs.verify(&public_inputs) {
            dbg!("cs not verified");
            return Ok(false);
        }
        previous_frame = Some(frame);
    }
    Ok(true)
}

impl CircuitFrame<'_, IO<Fr>, Witness<Fr>> {
    pub fn generate_groth16_proof<R: RngCore>(
        self,
        groth_params: Option<&groth16::Parameters<Bls12>>,
        rng: &mut R,
    ) -> Result<groth16::Proof<Bls12>, SynthesisError> {
        let create_proof = |p| groth16::create_random_proof(self, p, rng);

        if let Some(params) = groth_params {
            create_proof(params)
        } else {
            create_proof(CircuitFrame::<IO<Fr>, Witness<Fr>>::groth_params()?)
        }
    }

    pub fn verify_groth16_proof(
        self,
        pvk: &groth16::PreparedVerifyingKey<Bls12>,
        proof: groth16::Proof<Bls12>,
    ) -> Result<bool, SynthesisError> {
        let inputs = self.public_inputs(self.store);

        verify_proof(pvk, &proof, &inputs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::empty_sym_env;
    use bellperson::groth16::aggregate::verify_aggregate_proof;
    use bellperson::util_cs::{metric_cs::MetricCS, Comparable, Delta};
    use rand::rngs::OsRng;

    const DEFAULT_CHECK_GROTH16: bool = false;

    fn outer_prove_aux<Fo: Fn(&'_ mut Store<Fr>) -> Ptr<Fr>>(
        source: &str,
        expected_result: Fo,
        expected_iterations: usize,
        check_groth16: bool,
        check_constraint_systems: bool,
        limit: usize,
        debug: bool,
    ) {
        let rng = OsRng;

        let mut s = Store::default();
        let expected_result = expected_result(&mut s);

        let expr = s.read(source).unwrap();

        let groth_params = CircuitFrame::groth_params().unwrap();

        let pvk = groth16::prepare_verifying_key(&groth_params.vk);

        let size = 32;
        let (srs_pk, srs_vk) = INNER_PRODUCT_SRS.specialize(size);

        let e = empty_sym_env(&s);

        let proof = if check_groth16 {
            Some(
                CircuitFrame::outer_prove(
                    &groth_params,
                    srs_pk,
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

        if let Some((proof, public_inputs)) = proof {
            let frame_proofs = proof.frame_proofs.clone();
            if !debug {
                assert_eq!(expected_iterations, frame_proofs.len());
                assert_eq!(
                    expected_result,
                    frame_proofs[frame_proofs.len() - 1]
                        .0
                        .output
                        .as_ref()
                        .unwrap()
                        .expr
                );
            }
            let proofs_verified =
                verify_sequential_groth16_proofs(proof.frame_proofs, &groth_params.vk).unwrap();
            assert!(proofs_verified);

            let aggregate_proof_verified = verify_aggregate_proof(
                &srs_vk,
                &pvk,
                rng.clone(),
                &public_inputs,
                &proof.aggregated_proof,
                &proof.transcript_include,
            )
            .unwrap();

            assert!(aggregate_proof_verified);
        };

        let constraint_systems = if check_constraint_systems {
            Some(CircuitFrame::outer_synthesize(expr, e, &mut s, limit).unwrap())
        } else {
            None
        };

        if let Some(cs) = constraint_systems {
            if !debug {
                assert_eq!(expected_iterations, cs.len());
                assert_eq!(expected_result, cs[cs.len() - 1].0.output.expr);
            }
            let constraint_systems_verified = verify_sequential_css(&cs, &s).unwrap();
            assert!(constraint_systems_verified);

            check_cs_deltas(&cs, limit);
        };
    }

    pub fn check_cs_deltas(
        constraint_systems: &SequentialCS<IO<Fr>, Witness<Fr>>,
        limit: usize,
    ) -> () {
        let mut cs_blank = MetricCS::<Fr>::new();
        let store = Store::default();
        let blank_frame = CircuitFrame::blank(&store);
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
            |store| store.num(3),
            18,
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
            |store| store.num(3),
            3,
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
            |store| store.t(),
            3,
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
            |store| store.t(),
            3,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        );
        outer_prove_aux(
            &"(= 5 6)",
            |store| store.nil(),
            3,
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
            |store| store.num(5),
            3,
            DEFAULT_CHECK_GROTH16,
            true,
            100,
            false,
        );

        outer_prove_aux(
            &"(if t 5 6)",
            |store| store.num(5),
            3,
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
            |store| store.num(10),
            5,
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
            |store| store.num(125),
            // 117, // FIXME: is this change correct?
            91,
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
            |store| store.num(3125),
            // 248, // FIXME: is this change correct?
            201,
            DEFAULT_CHECK_GROTH16,
            true,
            300,
            false,
        );
    }
}
