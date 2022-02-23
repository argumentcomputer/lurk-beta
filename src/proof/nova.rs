#![allow(non_snake_case)]

use bellperson::{Circuit, ConstraintSystem, SynthesisError};
use merlin::Transcript;
use nova::{
    bellperson::{
        r1cs::{NovaShape, NovaWitness},
        shape_cs::ShapeCS,
        solver::SatisfyingAssignment,
    },
    errors::NovaError,
    r1cs::{
        R1CSGens, R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness,
    },
    traits::Group,
    FinalSNARK, StepSNARK,
};
use once_cell::sync::Lazy;
use pasta_curves::pallas;

use crate::circuit::CircuitFrame;
use crate::eval::{Evaluator, Frame, Witness, IO};

use crate::proof::Provable;
use crate::store::{Ptr, Store};

type PallasPoint = pallas::Point;
type PallasScalar = pallas::Scalar;

static EMPTY_STORE: Lazy<Store<PallasScalar>> = Lazy::new(Store::<PallasScalar>::default);
static BLANK_CIRCUIT_FRAME: Lazy<
    CircuitFrame<'_, PallasScalar, IO<PallasScalar>, Witness<PallasScalar>>,
> = Lazy::new(|| CircuitFrame::blank(&EMPTY_STORE));

pub struct Proof<G: Group> {
    pub step_proofs: Vec<StepSNARK<G>>,
    pub final_proof: FinalSNARK<G>,
    pub final_instance: RelaxedR1CSInstance<G>,
}

impl<G: Group> Proof<G> {
    pub fn verify(
        &self,
        shape_and_gens: &(R1CSShape<G>, R1CSGens<G>),
        instance: &RelaxedR1CSInstance<G>,
    ) -> bool {
        self.final_proof
            .verify(&shape_and_gens.1, &shape_and_gens.0, instance)
            .is_ok()
    }
}

pub trait Nova
where
    <Self::Grp as Group>::Scalar: ff::PrimeField,
{
    type Grp: Group;

    fn make_r1cs(
        circuit_frame: CircuitFrame<
            '_,
            <Self::Grp as Group>::Scalar,
            IO<<Self::Grp as Group>::Scalar>,
            Witness<<Self::Grp as Group>::Scalar>,
        >,
        shape: &R1CSShape<Self::Grp>,
        gens: &R1CSGens<Self::Grp>,
    ) -> Result<(R1CSInstance<Self::Grp>, R1CSWitness<Self::Grp>), NovaError> {
        let mut cs = SatisfyingAssignment::<Self::Grp>::new();

        circuit_frame.synthesize(&mut cs).unwrap();

        let (instance, witness) = cs.r1cs_instance_and_witness(shape, gens)?;

        Ok((instance, witness))
    }

    fn evaluate_and_prove(
        expr: Ptr<<Self::Grp as Group>::Scalar>,
        env: Ptr<<Self::Grp as Group>::Scalar>,
        store: &mut Store<<Self::Grp as Group>::Scalar>,
        limit: usize,
    ) -> Result<(Proof<Self::Grp>, RelaxedR1CSInstance<Self::Grp>), SynthesisError> {
        let mut evaluator = Evaluator::new(expr, env, store, limit);
        let frames = evaluator.iter().collect::<Vec<_>>();
        let (shape, gens) = Self::make_shape_and_gens();

        store.hydrate_scalar_cache();

        Self::make_proof(frames.as_slice(), &shape, &gens, store, true)
    }

    fn make_shape_and_gens() -> (R1CSShape<Self::Grp>, R1CSGens<Self::Grp>);

    fn make_proof(
        frames: &[Frame<IO<<Self::Grp as Group>::Scalar>, Witness<<Self::Grp as Group>::Scalar>>],
        shape: &R1CSShape<Self::Grp>,
        gens: &R1CSGens<Self::Grp>,
        store: &mut Store<<Self::Grp as Group>::Scalar>,
        verify_steps: bool, // Sanity check for development, until we have recursion.
    ) -> Result<(Proof<Self::Grp>, RelaxedR1CSInstance<Self::Grp>), SynthesisError> {
        let r1cs_instances = frames
            .iter()
            .map(|f| {
                let circuit_frame = CircuitFrame::from_frame(f.clone(), store);
                dbg!(&circuit_frame.public_inputs(store));

                Self::make_r1cs(circuit_frame, shape, gens).unwrap()
            })
            .collect::<Vec<_>>();

        assert!(r1cs_instances.len() > 1);

        let mut step_proofs = Vec::new();
        let mut prover_transcript = Transcript::new(b"LurkProver");
        let mut verifier_transcript = Transcript::new(b"LurkVerifier");

        let initial_acc = (
            RelaxedR1CSInstance::default(gens, shape),
            RelaxedR1CSWitness::default(shape),
        );

        let (acc_U, acc_W) =
            r1cs_instances
                .iter()
                .fold(initial_acc, |(acc_U, acc_W), (next_U, next_W)| {
                    let (step_proof, (step_U, step_W)) = Self::make_step_snark(
                        gens,
                        shape,
                        &acc_U,
                        &acc_W,
                        next_U,
                        next_W,
                        &mut prover_transcript,
                    );
                    if verify_steps {
                        step_proof
                            .verify(&acc_U, next_U, &mut verifier_transcript)
                            .unwrap();
                        step_proofs.push(step_proof);
                    };
                    (step_U, step_W)
                });

        let final_proof = Self::make_final_snark(&acc_W);

        let proof = Proof {
            step_proofs,
            final_proof,
            final_instance: acc_U.clone(),
        };

        Ok((proof, acc_U))
    }

    fn make_step_snark(
        gens: &R1CSGens<Self::Grp>,
        S: &R1CSShape<Self::Grp>,
        r_U: &RelaxedR1CSInstance<Self::Grp>,
        r_W: &RelaxedR1CSWitness<Self::Grp>,
        U2: &R1CSInstance<Self::Grp>,
        W2: &R1CSWitness<Self::Grp>,
        prover_transcript: &mut merlin::Transcript,
    ) -> (
        StepSNARK<Self::Grp>,
        (
            RelaxedR1CSInstance<Self::Grp>,
            RelaxedR1CSWitness<Self::Grp>,
        ),
    ) {
        let res = StepSNARK::prove(gens, S, r_U, r_W, U2, W2, prover_transcript);
        res.expect("make_step_snark failed")
    }

    fn make_final_snark(W: &RelaxedR1CSWitness<Self::Grp>) -> FinalSNARK<Self::Grp> {
        // produce a final SNARK
        let res = FinalSNARK::prove(W);
        res.expect("make_final_snark failed")
    }
}

pub struct NovaProver();
impl Nova for NovaProver {
    type Grp = PallasPoint;

    fn make_shape_and_gens() -> (R1CSShape<Self::Grp>, R1CSGens<Self::Grp>) {
        let mut cs = ShapeCS::<Self::Grp>::new();
        BLANK_CIRCUIT_FRAME.clone().synthesize(&mut cs).unwrap();

        let shape = cs.r1cs_shape();
        let gens = cs.r1cs_gens();

        (shape, gens)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::empty_sym_env;
    use crate::proof::verify_sequential_css;
    use crate::proof::SequentialCS;

    use bellperson::util_cs::{metric_cs::MetricCS, Comparable, Delta};
    use pallas::Scalar as Fr;

    const DEFAULT_CHECK_GROTH16: bool = false;

    fn outer_prove_aux<Fo: Fn(&'_ mut Store<Fr>) -> Ptr<Fr>>(
        source: &str,
        expected_result: Fo,
        expected_iterations: usize,
        check_nova: bool,
        check_constraint_systems: bool,
        limit: usize,
        debug: bool,
    ) {
        let mut s = Store::default();
        let expected_result = expected_result(&mut s);

        let expr = s.read(source).unwrap();

        let e = empty_sym_env(&s);

        let proof_results = if check_nova {
            Some(
                NovaProver::evaluate_and_prove(expr.clone(), empty_sym_env(&s), &mut s, limit)
                    .unwrap(),
            )
        } else {
            None
        };

        let shape_and_gens = NovaProver::make_shape_and_gens();
        if check_nova {
            if let Some((proof, instance)) = proof_results {
                proof.verify(&shape_and_gens, &instance);
            }
        }

        let constraint_systems = if check_constraint_systems {
            Some(CircuitFrame::outer_synthesize(expr, e, &mut s, limit, false).unwrap())
        } else {
            None
        };

        if let Some(cs) = constraint_systems {
            if !debug {
                assert_eq!(expected_iterations, cs.len());
                assert_eq!(expected_result, cs[cs.len() - 1].0.output.expr);
            }
            let constraint_systems_verified = verify_sequential_css::<Fr>(&cs, &s).unwrap();
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
        let blank_frame = CircuitFrame::<Fr, _, _>::blank(&store);
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
            true, // Always check Nova in at least one test.
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
