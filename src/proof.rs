use bellperson::util_cs::test_cs::TestConstraintSystem;
use bellperson::{
    groth16::{
        self,
        aggregate::{
            aggregate_proofs, aggregate_proofs_and_instances, setup_fake_srs, AggregateProof,
            AggregateProofAndInstance, GenericSRS,
        },
        verify_proof,
    },
    Circuit, SynthesisError,
};
use blstrs::{Bls12, Scalar};
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

const TRANSCRIPT_INCLUDE: &[u8] = "LURK-CIRCUIT".as_bytes();

// If you don't have a real SnarkPack SRS symlinked, generate a fake one.
// Don't use this in production!
const FALLBACK_TO_FAKE_SRS: bool = true;

type SequentialProofs<'a, E, IO, Witness> =
    Vec<(CircuitFrame<'a, E, IO, Witness>, groth16::Proof<E>)>;
type SequentialCS<F, IO, Witness> = Vec<(Frame<IO, Witness>, TestConstraintSystem<F>)>;
type FrameProofs<'a, E, IO, Witness> = (
    Proof<'a, E, CircuitFrame<'a, E, IO, Witness>>,
    Vec<Vec<<E as Engine>::Fr>>,
);

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
    fn public_input_size() -> usize;
    #[allow(clippy::ptr_arg)]
    fn extend_transcript(&self, transcript: &mut Vec<u8>, store: &Store<F>);
}

#[allow(dead_code)]
pub struct Proof<'a, E: Engine + MultiMillerLoop, F: Provable<E::Fr>>
where
    <E as Engine>::Gt: blstrs::Compress,
{
    frame_proofs: SequentialProofs<'a, E, IO<E::Fr>, Witness<E::Fr>>,
    aggregated_proof_and_instance: AggregateProofAndInstance<E>,
    aggregated_proof: AggregateProof<E>,
    // FIXME: remove when input aggregation is enabled.
    transcript_include: Vec<u8>,
    frames: Vec<F>,
}

impl<E: Engine, W> Provable<E::Fr> for CircuitFrame<'_, E, IO<E::Fr>, W> {
    fn public_inputs(&self, store: &Store<E::Fr>) -> Vec<E::Fr> {
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
        let input_output_size = IO::<E::Fr>::public_input_size();
        input_output_size * 2
    }

    // This is only needed for proof aggregation without input aggregation.
    fn extend_transcript(&self, transcript: &mut Vec<u8>, store: &Store<E::Fr>) {
        // TODO: Refactor to share code with `public_inputs` to avoid allocation.
        let inputs = self.public_inputs(store);

        for input in inputs {
            let bytes = input.to_repr();
            transcript.extend(bytes.as_ref());
        }
    }
}

impl<E: Engine, T: PartialEq + std::fmt::Debug, W> CircuitFrame<'_, E, T, W> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        self.output == maybe_next.input
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
    fn public_input_size() -> usize {
        6
    }
}

impl<'a, E: Engine> CircuitFrame<'a, E, IO<E::Fr>, Witness<E::Fr>> {
    pub fn blank(store: &'a Store<E::Fr>) -> Self {
        Self {
            store,
            input: None,
            output: None,
            witness: None,
        }
    }
}

impl<'a> CircuitFrame<'a, Bls12, IO<Scalar>, Witness<Scalar>> {
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
        CircuitFrame::blank(&store).frame_groth_params()
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
        srs: &GenericSRS<Bls12>,
        expr: Ptr<Scalar>,
        env: Ptr<Scalar>,
        store: &'a mut Store<Scalar>,
        limit: usize,
        rng: R,
    ) -> Result<FrameProofs<'a, Bls12, IO<Scalar>, Witness<Scalar>>, SynthesisError> {
        // FIXME: optimize execution order
        let mut evaluator = Evaluator::new(expr, env, store, limit);
        let mut frames = evaluator.iter().collect::<Vec<_>>();
        let mut proofs = Vec::with_capacity(frames.len());
        let mut circuit_frames = Vec::with_capacity(frames.len());

        let mut statements = Vec::with_capacity(frames.len());

        store.hydrate_scalar_cache();

        // NOTE: frame_proofs are not really needed, but having them helps with
        // testing and building confidence as we work up to fully succinct proofs.
        // Once these are removed a lot of the cloning and awkwardness of assembling
        // results here can be eliminated.
        let mut frame_proofs = Vec::with_capacity(frames.len());
        let mut transcript_include = Vec::new();
        for frame in &frames {
            let circuit_frame = CircuitFrame::from_frame(frame.clone(), store);
            statements.push(circuit_frame.clone().public_inputs(store));
            circuit_frames.push(circuit_frame.clone());

            // FIXME: Don't clone the RNG (?).
            let proof = circuit_frame
                .clone()
                .prove(Some(params), rng.clone())
                .unwrap();
            proofs.push(proof.clone());

            // FIXME: Remove this when input aggregation is working and enabled.
            circuit_frame.extend_transcript(&mut transcript_include, store);

            frame_proofs.push((circuit_frame, proof));
        }

        let last_index = frames.len() - 1;
        while proofs.len().count_ones() != 1 {
            // Pad proofs and frames to a power of 2.
            proofs.push(proofs[last_index].clone());
            frames.push(frames[last_index].clone());
            statements.push(statements[last_index].clone());
        }

        let srs = srs.specialize(proofs.len()).0;

        let aggregated_proof = aggregate_proofs(&srs, &transcript_include, proofs.as_slice())?;

        let aggregated_proof_and_instance = aggregate_proofs_and_instances(
            &srs,
            TRANSCRIPT_INCLUDE,
            statements.as_slice(),
            proofs.as_slice(),
        )?;

        Ok((
            Proof {
                frame_proofs,
                aggregated_proof_and_instance,
                aggregated_proof,
                frames: circuit_frames,
                transcript_include,
            },
            statements,
        ))
    }

    #[allow(clippy::needless_collect)]
    pub fn outer_synthesize(
        expr: Ptr<Scalar>,
        env: Ptr<Scalar>,
        store: &mut Store<Scalar>,
        limit: usize,
    ) -> Result<SequentialCS<Scalar, IO<Scalar>, Witness<Scalar>>, SynthesisError> {
        let mut evaluator = Evaluator::new(expr, env, store, limit);
        let frames = evaluator.iter().collect::<Vec<_>>();

        store.hydrate_scalar_cache();

        let res = frames
            .into_iter()
            .map(|frame| {
                let mut cs = TestConstraintSystem::new();
                CircuitFrame::<Bls12, _, _>::from_frame(frame.clone(), store)
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
    frame_proofs: SequentialProofs<Bls12, IO<Scalar>, Witness<Scalar>>,
    vk: &groth16::VerifyingKey<Bls12>,
) -> Result<bool, SynthesisError> {
    let previous_frame: Option<&CircuitFrame<Bls12, IO<Scalar>, Witness<Scalar>>> = None;

    let pvk = groth16::prepare_verifying_key(vk);

    for (_, (frame, proof)) in frame_proofs.into_iter().enumerate() {
        if let Some(prev) = previous_frame {
            if !prev.precedes(&frame) {
                return Ok(false);
            }
        }

        if !frame.verify_groth16_proof(&pvk, proof.clone())? {
            return Ok(false);
        }
    }

    Ok(true)
}

#[allow(dead_code)]
fn verify_sequential_css<E: Engine>(
    css: &SequentialCS<E::Fr, IO<E::Fr>, Witness<E::Fr>>,
    store: &Store<E::Fr>,
) -> Result<bool, SynthesisError> {
    let mut previous_frame: Option<&Frame<IO<E::Fr>, Witness<E::Fr>>> = None;

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
            CircuitFrame::<E, _, _>::from_frame(frame.clone(), store).public_inputs(store);

        if !cs.verify(&public_inputs) {
            dbg!("cs not verified");
            return Ok(false);
        }
        previous_frame = Some(frame);
    }
    Ok(true)
}

impl CircuitFrame<'_, Bls12, IO<Scalar>, Witness<Scalar>> {
    pub fn generate_groth16_proof<R: RngCore>(
        self,
        groth_params: Option<&groth16::Parameters<Bls12>>,
        rng: &mut R,
    ) -> Result<groth16::Proof<Bls12>, SynthesisError> {
        let create_proof = |p| groth16::create_random_proof(self, p, rng);

        if let Some(params) = groth_params {
            create_proof(params)
        } else {
            create_proof(CircuitFrame::groth_params()?)
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
    use bellperson::groth16::aggregate::{
        verify_aggregate_proof, verify_aggregate_proof_and_aggregate_instances,
    };
    use bellperson::util_cs::{metric_cs::MetricCS, Comparable, Delta};
    use blstrs::Scalar as Fr;
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

        let e = empty_sym_env(&s);

        let proof_results = if check_groth16 {
            Some(
                CircuitFrame::outer_prove(
                    &groth_params,
                    &INNER_PRODUCT_SRS,
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

        if let Some((proof, statements)) = proof_results {
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

            let mid = IO::<Fr>::public_input_size();
            let public_inputs = &statements[0][..mid];
            let public_outputs = &statements[statements.len() - 1][mid..];

            let srs_vk = INNER_PRODUCT_SRS.specialize(statements.len()).1;
            let _aggregate_proof_and_instances_verified =
                verify_aggregate_proof_and_aggregate_instances(
                    &srs_vk,
                    &pvk,
                    rng.clone(),
                    public_inputs,
                    public_outputs,
                    &proof.aggregated_proof_and_instance,
                    &TRANSCRIPT_INCLUDE,
                )
                .unwrap();

            let aggregate_proof_verified = verify_aggregate_proof(
                &srs_vk,
                &pvk,
                rng.clone(),
                &statements,
                &proof.aggregated_proof,
                &proof.transcript_include,
            )
            .unwrap();

            assert!(aggregate_proof_verified);
            // Uncomment this and remove `aggregate_proof` entirely once input aggregation
            // is working in bellperson.
            // assert!(aggregate_proof_and_instances_verified);
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
            let constraint_systems_verified = verify_sequential_css::<Bls12>(&cs, &s).unwrap();
            assert!(constraint_systems_verified);

            check_cs_deltas(&cs, limit);
        };
    }

    pub fn check_cs_deltas(
        constraint_systems: &SequentialCS<Fr, IO<Fr>, Witness<Fr>>,
        limit: usize,
    ) -> () {
        let mut cs_blank = MetricCS::<Fr>::new();
        let store = Store::<Fr>::default();
        let blank_frame = CircuitFrame::<Bls12, _, _>::blank(&store);
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
