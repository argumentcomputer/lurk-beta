use bellperson::{
    groth16::{
        self,
        aggregate::{
            aggregate_proofs, aggregate_proofs_and_instances, setup_fake_srs, AggregateProof,
            AggregateProofAndInstance, GenericSRS,
        },
        verify_proof,
    },
    SynthesisError,
};
use blstrs::{Bls12, Scalar};
use ff::PrimeField;
use once_cell::sync::{Lazy, OnceCell};
use pairing_lib::{Engine, MultiMillerLoop};
use rand::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;

use crate::circuit::CircuitFrame;
use crate::eval::{Evaluator, Witness, IO};
use crate::proof::Provable;
use crate::store::{Ptr, Store};

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

type FrameProofs<'a, E> = (Proof<'a, E>, Vec<Vec<<E as Engine>::Fr>>);

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

#[allow(dead_code)]
pub struct Proof<'a, E: Engine + MultiMillerLoop>
where
    <E as Engine>::Gt: blstrs::Compress,
{
    frame_proofs: Vec<(
        CircuitFrame<'a, E::Fr, IO<E::Fr>, Witness<E::Fr>>,
        groth16::Proof<E>,
    )>,
    aggregated_proof_and_instance: AggregateProofAndInstance<E>,
    aggregated_proof: AggregateProof<E>,
    // FIXME: remove when input aggregation is enabled.
    transcript_include: Vec<u8>,
}

impl<F: PrimeField, W> CircuitFrame<'_, F, IO<F>, W> {
    // This is only needed for proof aggregation without input aggregation.
    fn extend_transcript(&self, transcript: &mut Vec<u8>, store: &Store<F>) {
        // TODO: Refactor to share code with `public_inputs` to avoid allocation.
        let inputs = self.public_inputs(store);

        for input in inputs {
            let bytes = input.to_repr();
            transcript.extend(bytes.as_ref());
        }
    }
}

pub trait Groth16
where
    <Self::E as Engine>::Gt: blstrs::Compress + serde::Serialize,
    <Self::E as Engine>::G1: serde::Serialize,
    <Self::E as Engine>::G1Affine: serde::Serialize,
    <Self::E as Engine>::G2Affine: serde::Serialize,
    <Self::E as Engine>::Fr: serde::Serialize,
{
    type E: Engine + MultiMillerLoop;

    fn groth_params() -> Result<&'static groth16::Parameters<Bls12>, SynthesisError> {
        let store = Store::default();
        let circuit_frame = CircuitFrame::blank(&store);
        let params = FRAME_GROTH_PARAMS.get_or_try_init::<_, SynthesisError>(|| {
            let rng = &mut XorShiftRng::from_seed(DUMMY_RNG_SEED);
            let params = groth16::generate_random_parameters::<Bls12, _, _>(circuit_frame, rng)?;
            Ok(params)
        })?;
        Ok(params)
    }

    fn prove<R: RngCore>(
        circuit_frame: CircuitFrame<
            '_,
            <Self::E as Engine>::Fr,
            IO<<Self::E as Engine>::Fr>,
            Witness<<Self::E as Engine>::Fr>,
        >,
        params: Option<&groth16::Parameters<Self::E>>,
        mut rng: R,
    ) -> Result<groth16::Proof<Self::E>, SynthesisError> {
        Self::generate_groth16_proof(circuit_frame, params, &mut rng)
    }

    fn outer_prove<'a, R: RngCore + Clone>(
        params: &groth16::Parameters<Self::E>,
        srs: &GenericSRS<Self::E>,
        expr: Ptr<<Self::E as Engine>::Fr>,
        env: Ptr<<Self::E as Engine>::Fr>,
        store: &'a mut Store<<Self::E as Engine>::Fr>,
        limit: usize,
        mut rng: R,
    ) -> Result<FrameProofs<'a, Self::E>, SynthesisError> {
        // See NOTE below.
        assert_eq!(1, limit.count_ones());

        // FIXME: optimize execution order
        let mut evaluator = Evaluator::new(expr, env, store, limit);
        let mut frames = evaluator.iter().collect::<Vec<_>>();

        if frames.len().count_ones() != 1 {
            // NOTE: PADDING and LIMIT
            //
            // If there are not a power-of-two number of frames, then padding will be needed.
            // In that case, obtain a trivial final proof of the terminal reduction to itself.
            // This will fail if the proof is not complete (i.e. the final continuation must be Terminal).
            // This implies that when power-of-two padding is required, we must choose a limit
            // which is a power of two.

            frames.push(frames[frames.len() - 1].next(store));
        }

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

            let proof = Self::generate_groth16_proof(circuit_frame.clone(), Some(params), &mut rng)
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
                transcript_include,
            },
            statements,
        ))
    }

    fn generate_groth16_proof<R: RngCore>(
        circuit_frame: CircuitFrame<
            '_,
            <Self::E as Engine>::Fr,
            IO<<Self::E as Engine>::Fr>,
            Witness<<Self::E as Engine>::Fr>,
        >,
        groth_params: Option<&groth16::Parameters<Self::E>>,
        rng: &mut R,
    ) -> Result<groth16::Proof<Self::E>, SynthesisError>;

    fn verify_groth16_proof(
        circuit_frame: CircuitFrame<
            '_,
            <Self::E as Engine>::Fr,
            IO<<Self::E as Engine>::Fr>,
            Witness<<Self::E as Engine>::Fr>,
        >,
        pvk: &groth16::PreparedVerifyingKey<Self::E>,
        proof: groth16::Proof<Self::E>,
    ) -> Result<bool, SynthesisError> {
        let inputs = circuit_frame.public_inputs(circuit_frame.store);

        verify_proof(pvk, &proof, &inputs)
    }
}

pub struct Groth16Prover();

impl Groth16 for Groth16Prover {
    type E = Bls12;

    fn generate_groth16_proof<R: RngCore>(
        circuit_frame: CircuitFrame<
            '_,
            <Self::E as Engine>::Fr,
            IO<<Self::E as Engine>::Fr>,
            Witness<<Self::E as Engine>::Fr>,
        >,
        groth_params: Option<&groth16::Parameters<Self::E>>,
        rng: &mut R,
    ) -> Result<groth16::Proof<Self::E>, SynthesisError> {
        let create_proof = |p| groth16::create_random_proof(circuit_frame, p, rng);

        if let Some(params) = groth_params {
            create_proof(params)
        } else {
            create_proof(Self::groth_params()?)
        }
    }
}

#[allow(dead_code)]
fn verify_sequential_groth16_proofs(
    frame_proofs: Vec<(
        CircuitFrame<'_, Scalar, IO<Scalar>, Witness<Scalar>>,
        groth16::Proof<Bls12>,
    )>,
    vk: &groth16::VerifyingKey<Bls12>,
) -> Result<bool, SynthesisError> {
    let previous_frame: Option<&CircuitFrame<Scalar, IO<Scalar>, Witness<Scalar>>> = None;

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

impl CircuitFrame<'_, Scalar, IO<Scalar>, Witness<Scalar>> {
    pub fn generate_groth16_proof<R: RngCore>(
        self,
        groth_params: Option<&groth16::Parameters<Bls12>>,
        rng: &mut R,
    ) -> Result<groth16::Proof<Bls12>, SynthesisError> {
        let create_proof = |p| groth16::create_random_proof(self, p, rng);

        if let Some(params) = groth_params {
            create_proof(params)
        } else {
            create_proof(Groth16Prover::groth_params()?)
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
    use crate::proof::{verify_sequential_css, SequentialCS};
    use bellperson::{
        groth16::aggregate::{
            verify_aggregate_proof, verify_aggregate_proof_and_aggregate_instances,
        },
        util_cs::{metric_cs::MetricCS, Comparable, Delta},
        Circuit,
    };
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

        let groth_params = Groth16Prover::groth_params().unwrap();

        let pvk = groth16::prepare_verifying_key(&groth_params.vk);

        let e = empty_sym_env(&s);

        let proof_results = if check_groth16 {
            Some(
                Groth16Prover::outer_prove(
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
                assert_eq!(expected_iterations, frame_proofs.len() - 1);
                assert_eq!(
                    expected_result,
                    proof.frame_proofs[frame_proofs.len() - 1]
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
            let aggregate_proof_and_instances_verified =
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
            assert!(aggregate_proof_and_instances_verified);
        };

        let constraint_systems = if check_constraint_systems {
            Some(CircuitFrame::outer_synthesize(expr, e, &mut s, limit, true).unwrap())
        } else {
            None
        };

        if let Some(cs) = constraint_systems {
            if !debug {
                assert_eq!(expected_iterations, cs.len() - 1);
                assert_eq!(expected_result, cs[cs.len() - 1].0.output.expr);
            }
            let constraint_systems_verified = verify_sequential_css::<Scalar>(&cs, &s).unwrap();
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
        let blank_frame = CircuitFrame::<Scalar, _, _>::blank(&store);
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
            &"(let ((a 5)
                     (b 1)
                     (c 2))
                (/ (+ a b) c))",
            |store| store.num(3),
            18,
            true, // Always check Groth16 in at least one test.
            true,
            128,
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
            128,
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
            128,
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
            128,
            false,
        );
        outer_prove_aux(
            &"(= 5 6)",
            |store| store.nil(),
            3,
            DEFAULT_CHECK_GROTH16,
            true,
            128,
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
            128,
            false,
        );

        outer_prove_aux(
            &"(if t 5 6)",
            |store| store.num(5),
            3,
            DEFAULT_CHECK_GROTH16,
            true,
            128,
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
            128,
            false,
        );
    }

    #[test]
    #[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
    fn outer_prove_recursion1() {
        outer_prove_aux(
            &"(letrec ((exp (lambda (base)
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
            256,
            false,
        );
    }

    #[test]
    #[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
    fn outer_prove_recursion2() {
        outer_prove_aux(
            &"(letrec ((exp (lambda (base)
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
            256,
            false,
        );
    }
}
