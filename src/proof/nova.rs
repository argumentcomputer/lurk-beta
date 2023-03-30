#![allow(non_snake_case)]

use std::marker::PhantomData;

use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};

use nova::{
    errors::NovaError,
    traits::{
        circuit::{StepCircuit, TrivialTestCircuit},
        Group,
    },
    CompressedSNARK, ProverKey, RecursiveSNARK, VerifierKey,
};
use pasta_curves::{pallas, vesta};

use crate::circuit::{
    gadgets::{
        data::GlobalAllocations,
        pointer::{AllocatedContPtr, AllocatedPtr},
    },
    CircuitFrame, MultiFrame,
};
use crate::error::ProofError;
use crate::eval::{Evaluator, Frame, Witness, IO};
use crate::field::LurkField;
use crate::proof::{Prover, PublicParameters};
use crate::store::{Ptr, Store};

pub type G1 = pallas::Point;
pub type G2 = vesta::Point;

pub type S1 = pallas::Scalar;
pub type S2 = vesta::Scalar;

pub type EE1 = nova::provider::ipa_pc::EvaluationEngine<G1>;
pub type EE2 = nova::provider::ipa_pc::EvaluationEngine<G2>;

type CC1 = nova::spartan::spark::TrivialCompComputationEngine<G1, EE1>;
type CC2 = nova::spartan::spark::TrivialCompComputationEngine<G2, EE2>;

pub type SS1 = nova::spartan::RelaxedR1CSSNARK<G1, EE1, CC1>;
pub type SS2 = nova::spartan::RelaxedR1CSSNARK<G2, EE2, CC2>;

pub type C1<'a> = MultiFrame<'a, S1, IO<S1>, Witness<S1>>;
pub type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

pub type NovaPublicParams<'a> = nova::PublicParams<G1, G2, C1<'a>, C2>;

#[derive(Serialize, Deserialize)]
pub struct PublicParams<'a> {
    pp: NovaPublicParams<'a>,
    pk: ProverKey<G1, G2, C1<'a>, C2, SS1, SS2>,
    vk: VerifierKey<G1, G2, C1<'a>, C2, SS1, SS2>,
}

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub enum Proof<'a> {
    Recursive(Box<RecursiveSNARK<G1, G2, C1<'a>, C2>>),
    Compressed(Box<CompressedSNARK<G1, G2, C1<'a>, C2, SS1, SS2>>),
}

pub fn public_params<'a>(num_iters_per_step: usize) -> PublicParams<'a> {
    let (circuit_primary, circuit_secondary) = C1::circuits(num_iters_per_step);

    let pp = nova::PublicParams::setup(circuit_primary, circuit_secondary);
    let (pk, vk) = CompressedSNARK::setup(&pp).unwrap();
    PublicParams { pp, pk, vk }
}

impl<'a> MultiFrame<'a, S1, IO<S1>, Witness<S1>> {
    fn circuits(count: usize) -> (C1<'a>, C2) {
        (MultiFrame::blank(count), TrivialTestCircuit::default())
    }
}

pub struct NovaProver<F: LurkField> {
    // `reduction_count` specifies the number of small-step reductions are performed in each recursive step.
    reduction_count: usize,
    _p: PhantomData<F>,
}

impl<'a> PublicParameters for PublicParams<'a> {}

impl<'a, F: LurkField> Prover<'a, F> for NovaProver<F> {
    type PublicParams = PublicParams<'a>;
    fn new(reduction_count: usize) -> Self {
        NovaProver::<F> {
            reduction_count,
            _p: PhantomData::<F>,
        }
    }
    fn reduction_count(&self) -> usize {
        self.reduction_count
    }
}

impl<F: LurkField> NovaProver<F> {
    fn get_evaluation_frames(
        &self,
        expr: Ptr<S1>,
        env: Ptr<S1>,
        store: &mut Store<S1>,
        limit: usize,
    ) -> Result<Vec<Frame<IO<S1>, Witness<S1>>>, ProofError> {
        let padding_predicate = |count| self.needs_frame_padding(count);

        let frames = Evaluator::generate_frames(expr, env, store, limit, padding_predicate)?;
        store.hydrate_scalar_cache();

        Ok(frames)
    }
    pub fn evaluate_and_prove<'a>(
        &'a self,
        pp: &'a PublicParams,
        expr: Ptr<S1>,
        env: Ptr<S1>,
        store: &'a mut Store<S1>,
        limit: usize,
    ) -> Result<(Proof, Vec<S1>, Vec<S1>, usize), ProofError> {
        let frames = self.get_evaluation_frames(expr, env, store, limit)?;
        let z0 = frames[0].input.to_vector(store)?;
        let zi = frames.last().unwrap().output.to_vector(store)?;
        let circuits = MultiFrame::from_frames(self.reduction_count(), &frames, store);
        let num_steps = circuits.len();
        let proof =
            Proof::prove_recursively(pp, store, &circuits, self.reduction_count, z0.clone())?;

        Ok((proof, z0, zi, num_steps))
    }
}

impl<'a, F: LurkField> StepCircuit<F> for MultiFrame<'a, F, IO<F>, Witness<F>> {
    fn arity(&self) -> usize {
        6
    }

    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        assert_eq!(self.arity(), z.len());

        let input_expr = AllocatedPtr::by_index(0, z);
        let input_env = AllocatedPtr::by_index(1, z);
        let input_cont = AllocatedContPtr::by_index(2, z);

        let count = self.count;

        let (new_expr, new_env, new_cont) = match self.frames.as_ref() {
            Some(frames) => {
                let s = self.store.expect("store missing");
                let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s)?;
                self.synthesize_frames(cs, s, input_expr, input_env, input_cont, frames, &g)
            }
            None => {
                assert!(self.store.is_none());
                let s = Store::default();
                let blank_frame = CircuitFrame::blank();
                let frames = vec![blank_frame; count];

                let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), &s)?;
                self.synthesize_frames(cs, &s, input_expr, input_env, input_cont, &frames, &g)
            }
        };

        Ok(vec![
            new_expr.tag().clone(),
            new_expr.hash().clone(),
            new_env.tag().clone(),
            new_env.hash().clone(),
            new_cont.tag().clone(),
            new_cont.hash().clone(),
        ])
    }

    fn output(&self, z: &[F]) -> Vec<F> {
        // sanity check
        assert_eq!(z, self.input.unwrap().to_vector(self.get_store()).unwrap());
        assert_eq!(
            self.frames.as_ref().unwrap().last().unwrap().output,
            self.output
        );
        self.output.unwrap().to_vector(self.get_store()).unwrap()
    }
}

impl<'a> Proof<'a> {
    pub fn prove_recursively(
        pp: &'a PublicParams,
        store: &'a Store<S1>,
        circuits: &[C1<'a>],
        num_iters_per_step: usize,
        z0: Vec<S1>,
    ) -> Result<Self, ProofError> {
        assert!(!circuits.is_empty());
        assert_eq!(circuits[0].arity(), z0.len());
        let debug = false;
        let z0_primary = z0;
        let z0_secondary = Self::z0_secondary();

        assert_eq!(
            circuits[0].frames.as_ref().unwrap().len(),
            num_iters_per_step
        );
        let (_circuit_primary, circuit_secondary) = C1::<'a>::circuits(num_iters_per_step);

        // produce a recursive SNARK
        let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1<'a>, C2>> = None;

        for circuit_primary in circuits.iter() {
            assert_eq!(
                num_iters_per_step,
                circuit_primary.frames.as_ref().unwrap().len()
            );
            if debug {
                // For debugging purposes, synthesize the circuit and check that the constraint system is satisfied.
                use bellperson::util_cs::test_cs::TestConstraintSystem;
                let mut cs = TestConstraintSystem::<<G1 as Group>::Scalar>::new();

                let zi = circuit_primary.frames.as_ref().unwrap()[0]
                    .input
                    .unwrap()
                    .to_vector(store)?;
                let mut zi_allocated = Vec::with_capacity(zi.len());

                for (i, x) in zi.iter().enumerate() {
                    let allocated =
                        AllocatedNum::alloc(cs.namespace(|| format!("z{i}_1")), || Ok(*x))?;
                    zi_allocated.push(allocated);
                }

                circuit_primary.synthesize(&mut cs, zi_allocated.as_slice())?;

                assert!(cs.is_satisfied());
            }

            let res = RecursiveSNARK::prove_step(
                &pp.pp,
                recursive_snark,
                circuit_primary.clone(),
                circuit_secondary.clone(),
                z0_primary.clone(),
                z0_secondary.clone(),
            );
            assert!(res.is_ok());
            recursive_snark = Some(res?);
        }

        Ok(Self::Recursive(Box::new(recursive_snark.unwrap())))
    }

    pub fn compress(self, pp: &'a PublicParams) -> Result<Self, ProofError> {
        match &self {
            Self::Recursive(recursive_snark) => Ok(Self::Compressed(Box::new(CompressedSNARK::<
                _,
                _,
                _,
                _,
                SS1,
                SS2,
            >::prove(
                &pp.pp,
                &pp.pk,
                recursive_snark,
            )?))),
            Self::Compressed(_) => Ok(self),
        }
    }

    pub fn verify(
        &self,
        pp: &PublicParams,
        num_steps: usize,
        z0: Vec<S1>,
        zi: &[S1],
    ) -> Result<bool, NovaError> {
        let (z0_primary, zi_primary) = (z0, zi);
        let z0_secondary = Self::z0_secondary();
        let zi_secondary = z0_secondary.clone();

        let (zi_primary_verified, zi_secondary_verified) = match self {
            Self::Recursive(p) => p.verify(&pp.pp, num_steps, z0_primary, z0_secondary),
            Self::Compressed(p) => p.verify(&pp.vk, num_steps, z0_primary, z0_secondary),
        }?;

        Ok(zi_primary == zi_primary_verified && zi_secondary == zi_secondary_verified)
    }

    fn z0_secondary() -> Vec<S2> {
        vec![<G2 as Group>::Scalar::zero()]
    }
}

#[cfg(test)]
mod tests {
    use crate::num::Num;

    use super::*;
    use crate::eval::empty_sym_env;
    use crate::proof::Provable;
    use crate::store::ContPtr;
    use crate::tag::{Op, Op1, Op2};

    use bellperson::{
        util_cs::{metric_cs::MetricCS, test_cs::TestConstraintSystem, Comparable, Delta},
        Circuit,
    };
    use pallas::Scalar as Fr;

    const DEFAULT_REDUCTION_COUNT: usize = 5;
    const REDUCTION_COUNTS_TO_TEST: [usize; 3] = [1, 2, 5];
    fn test_aux(
        s: &mut Store<Fr>,
        expr: &str,
        expected_result: Option<Ptr<Fr>>,
        expected_env: Option<Ptr<Fr>>,
        expected_cont: Option<ContPtr<Fr>>,
        expected_emitted: Option<Vec<Ptr<Fr>>>,
        expected_iterations: usize,
    ) {
        dbg!(expr);

        for chunk_size in REDUCTION_COUNTS_TO_TEST {
            nova_test_full_aux(
                s,
                expr,
                expected_result,
                expected_env,
                expected_cont,
                expected_emitted.as_ref(),
                expected_iterations,
                chunk_size,
                false,
                None,
            )
        }
    }

    fn nova_test_full_aux(
        s: &mut Store<Fr>,
        expr: &str,
        expected_result: Option<Ptr<Fr>>,
        expected_env: Option<Ptr<Fr>>,
        expected_cont: Option<ContPtr<Fr>>,
        expected_emitted: Option<&Vec<Ptr<Fr>>>,
        expected_iterations: usize,
        reduction_count: usize,
        check_nova: bool,
        limit: Option<usize>,
    ) {
        let expr = s.read(expr).unwrap();
        nova_test_full_aux2(
            s,
            expr,
            expected_result,
            expected_env,
            expected_cont,
            expected_emitted,
            expected_iterations,
            reduction_count,
            check_nova,
            limit,
        )
    }

    fn nova_test_full_aux2(
        s: &mut Store<Fr>,
        expr: Ptr<Fr>,
        expected_result: Option<Ptr<Fr>>,
        expected_env: Option<Ptr<Fr>>,
        expected_cont: Option<ContPtr<Fr>>,
        expected_emitted: Option<&Vec<Ptr<Fr>>>,
        expected_iterations: usize,
        reduction_count: usize,
        check_nova: bool,
        limit: Option<usize>,
    ) {
        let limit = limit.unwrap_or(10000);

        let e = empty_sym_env(s);

        let nova_prover = NovaProver::<Fr>::new(reduction_count);

        if check_nova {
            let pp = public_params(reduction_count);
            let (proof, z0, zi, num_steps) = nova_prover
                .evaluate_and_prove(&pp, expr, empty_sym_env(s), s, limit)
                .unwrap();

            let res = proof.verify(&pp, num_steps, z0.clone(), &zi);
            if res.is_err() {
                dbg!(&res);
            }
            assert!(res.unwrap());

            let compressed = proof.compress(&pp).unwrap();
            let res2 = compressed.verify(&pp, num_steps, z0, &zi);

            assert!(res2.unwrap());
        }

        let frames = nova_prover
            .get_evaluation_frames(expr, e, s, limit)
            .unwrap();

        let multiframes = MultiFrame::from_frames(nova_prover.reduction_count(), &frames, s);

        let len = multiframes.len();

        let adjusted_iterations = nova_prover.expected_total_iterations(expected_iterations);
        let mut previous_frame: Option<MultiFrame<Fr, IO<Fr>, Witness<Fr>>> = None;

        let mut cs_blank = MetricCS::<Fr>::new();

        let blank = MultiFrame::<Fr, IO<Fr>, Witness<Fr>>::blank(reduction_count);
        blank
            .synthesize(&mut cs_blank)
            .expect("failed to synthesize blank");

        for (_i, multiframe) in multiframes.iter().enumerate() {
            let mut cs = TestConstraintSystem::new();
            multiframe.clone().synthesize(&mut cs).unwrap();

            if let Some(prev) = previous_frame {
                assert!(prev.precedes(multiframe));
            }

            // dbg!(i);
            assert!(cs.is_satisfied());
            assert!(cs.verify(&multiframe.public_inputs()));

            previous_frame = Some(multiframe.clone());

            let delta = cs.delta(&cs_blank, true);

            assert!(delta == Delta::Equal);
        }
        let output = previous_frame.unwrap().output.unwrap();

        if let Some(expected_emitted) = expected_emitted {
            let emitted_vec: Vec<_> = frames
                .iter()
                .flat_map(|frame| frame.output.maybe_emitted_expression(s))
                .collect();
            assert_eq!(expected_emitted, &emitted_vec);
        }

        if let Some(expected_result) = expected_result {
            assert!(s.ptr_eq(&expected_result, &output.expr).unwrap());
        }
        if let Some(expected_env) = expected_env {
            assert!(s.ptr_eq(&expected_env, &output.env).unwrap());
        }
        if let Some(expected_cont) = expected_cont {
            assert_eq!(expected_cont, output.cont);
        } else {
            assert_eq!(s.get_cont_terminal(), output.cont);
        }

        assert_eq!(expected_iterations, Frame::significant_frame_count(&frames));
        assert_eq!(adjusted_iterations, len);
    }

    // IMPORTANT: Run next tests at least once. Some are ignored because they
    // are expensive. The criteria is that if the number of iteractions is
    // more than 30 we ignore it.
    ////////////////////////////////////////////////////////////////////////////

    #[test]
    fn test_prove_binop() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux(s, "(+ 1 2)", Some(expected), None, Some(terminal), None, 3);
    }

    #[test]
    #[should_panic]
    // This tests the testing mechanism. Since the supplied expected value is wrong,
    // the test should panic on an assertion failure.
    fn test_prove_binop_fail() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux(s, "(+ 1 2)", Some(expected), None, Some(terminal), None, 3);
    }

    #[test]
    #[ignore]
    fn test_prove_arithmetic_let() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((a 5)
                      (b 1)
                      (c 2))
                 (/ (+ a b) c))",
            Some(expected),
            None,
            Some(terminal),
            None,
            18,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_eq() {
        let s = &mut Store::<Fr>::default();
        let expected = s.t();
        let terminal = s.get_cont_terminal();
        nova_test_full_aux(
            s,
            "(eq 5 5)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            DEFAULT_REDUCTION_COUNT,
            true,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_num_equal() {
        let s = &mut Store::<Fr>::default();
        let expected = s.t();
        let terminal = s.get_cont_terminal();
        test_aux(s, "(= 5 5)", Some(expected), None, Some(terminal), None, 3);

        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux(s, "(= 5 6)", Some(expected), None, Some(terminal), None, 3);
    }

    #[test]
    fn test_prove_invalid_num_equal() {
        let s = &mut Store::<Fr>::default();
        let expected = s.nil();
        let error = s.get_cont_error();
        test_aux(s, "(= 5 nil)", Some(expected), None, Some(error), None, 3);

        let expected = s.num(5);
        test_aux(s, "(= nil 5)", Some(expected), None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_equal() {
        let s = &mut Store::<Fr>::default();
        let nil = s.nil();
        let t = s.t();
        let terminal = s.get_cont_terminal();

        test_aux(s, "(eq 5 nil)", Some(nil), None, Some(terminal), None, 3);
        test_aux(s, "(eq nil 5)", Some(nil), None, Some(terminal), None, 3);
        test_aux(s, "(eq nil nil)", Some(t), None, Some(terminal), None, 3);
        test_aux(s, "(eq 5 5)", Some(t), None, Some(terminal), None, 3);
    }

    #[test]
    fn test_prove_quote_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(quote (1) (2))", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_if() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(if t 5 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
        );

        let expected = s.num(6);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(if nil 5 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
        )
    }

    #[test]
    fn test_prove_if_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let error = s.get_cont_error();
        test_aux(
            s,
            "(if nil 5 6 7)",
            Some(expected),
            None,
            Some(error),
            None,
            2,
        )
    }

    #[test]
    #[ignore]
    fn test_prove_if_fully_evaluates() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(10);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(if t (+ 5 5) 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
        );
    }

    #[test]
    #[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
    fn test_prove_recursion1() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((exp (lambda (base)
                               (lambda (exponent)
                                 (if (= 0 exponent)
                                     1
                                     (* base ((exp base) (- exponent 1))))))))
                 ((exp 5) 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            66,
        );
    }

    #[test]
    #[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
    fn test_prove_recursion2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((exp (lambda (base)
                                  (lambda (exponent)
                                     (lambda (acc)
                                       (if (= 0 exponent)
                                          acc
                                          (((exp base) (- exponent 1)) (* acc base))))))))
                (((exp 5) 2) 1))",
            Some(expected),
            None,
            Some(terminal),
            None,
            93,
        );
    }

    fn test_prove_unop_regression_aux(chunk_count: usize) {
        let s = &mut Store::<Fr>::default();
        let expected = s.sym("t");
        let terminal = s.get_cont_terminal();
        nova_test_full_aux(
            s,
            "(atom 123)",
            Some(expected),
            None,
            Some(terminal),
            None,
            2,
            chunk_count, // This needs to be 1 to exercise the bug.
            false,
            None,
        );

        let expected = s.num(1);
        nova_test_full_aux(
            s,
            "(car '(1 . 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            2,
            chunk_count, // This needs to be 1 to exercise the bug.
            false,
            None,
        );

        let expected = s.num(2);
        nova_test_full_aux(
            s,
            "(cdr '(1 . 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            2,
            chunk_count, // This needs to be 1 to exercise the bug.
            false,
            None,
        );

        let expected = s.num(123);
        nova_test_full_aux(
            s,
            "(emit 123)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            chunk_count,
            false,
            None,
        )
    }

    #[test]
    #[ignore]
    fn test_prove_unop_regression() {
        // We need to at least use chunk size 1 to exercise the regression.
        // Also use a non-1 value to check the MultiFrame case.
        for i in 1..2 {
            test_prove_unop_regression_aux(i);
        }
    }

    #[test]
    #[ignore]
    fn test_prove_emit_output() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(emit 123)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(99);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "((lambda (x) x) 99)",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(99);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "((lambda (y)
                    ((lambda (x) y) 888))
                  99)",
            Some(expected),
            None,
            Some(terminal),
            None,
            9,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate3() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(999);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "((lambda (y)
                     ((lambda (x)
                        ((lambda (z) z)
                         x))
                      y))
                   999)",
            Some(expected),
            None,
            Some(terminal),
            None,
            10,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate4() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(888);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "((lambda (y)
                     ((lambda (x)
                        ((lambda (z) z)
                         x))
                      ;; NOTE: We pass a different value here.
                      888))
                  999)",
            Some(expected),
            None,
            Some(terminal),
            None,
            10,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate5() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(999);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(((lambda (fn)
                      (lambda (x) (fn x)))
                    (lambda (y) y))
                   999)",
            Some(expected),
            None,
            Some(terminal),
            None,
            13,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate_sum() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(9);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(+ 2 (+ 3 4))",
            Some(expected),
            None,
            Some(terminal),
            None,
            6,
        );
    }

    #[test]
    fn test_prove_binop_rest_is_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(9);
        let error = s.get_cont_error();
        test_aux(s, "(- 9 8 7)", Some(expected), None, Some(error), None, 2);
        test_aux(s, "(= 9 8 7)", Some(expected), None, Some(error), None, 2);
    }

    fn op_syntax_error<T: Op + Copy>() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        let mut test = |op: T| {
            let name = op.symbol_name();

            if !op.supports_arity(0) {
                let expr = format!("({name})");
                dbg!(&expr);
                test_aux(s, &expr, None, None, Some(error), None, 1);
            }
            if !op.supports_arity(1) {
                let expr = format!("({name} 123)");
                dbg!(&expr);
                test_aux(s, &expr, None, None, Some(error), None, 1);
            }
            if !op.supports_arity(2) {
                let expr = format!("({name} 123 456)");
                dbg!(&expr);
                test_aux(s, &expr, None, None, Some(error), None, 1);
            }

            if !op.supports_arity(3) {
                let expr = format!("({name} 123 456 789)");
                dbg!(&expr);
                let iterations = if op.supports_arity(2) { 2 } else { 1 };
                test_aux(s, &expr, None, None, Some(error), None, iterations);
            }
        };

        for op in T::all() {
            test(*op);
        }
    }

    #[test]
    #[ignore]
    fn test_prove_unop_syntax_error() {
        op_syntax_error::<Op1>();
    }

    #[test]
    #[ignore]
    fn test_prove_binop_syntax_error() {
        op_syntax_error::<Op2>();
    }

    #[test]
    fn test_prove_diff() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(4);
        let terminal = s.get_cont_terminal();
        test_aux(s, "(- 9 5)", Some(expected), None, Some(terminal), None, 3);
    }

    #[test]
    #[ignore]
    fn test_prove_product() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(45);
        let terminal = s.get_cont_terminal();
        test_aux(s, "(* 9 5)", Some(expected), None, Some(terminal), None, 3);
    }

    #[test]
    #[ignore]
    fn test_prove_quotient() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(7);
        let terminal = s.get_cont_terminal();
        test_aux(s, "(/ 21 3)", Some(expected), None, Some(terminal), None, 3);
    }

    #[test]
    fn test_prove_error_div_by_zero() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(0);
        let error = s.get_cont_error();
        test_aux(s, "(/ 21 0)", Some(expected), None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_error_invalid_type_and_not_cons() {
        let s = &mut Store::<Fr>::default();
        let expected = s.nil();
        let error = s.get_cont_error();
        test_aux(s, "(/ 21 nil)", Some(expected), None, Some(error), None, 3);
    }

    #[test]
    #[ignore]
    fn test_prove_adder() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(((lambda (x)
                    (lambda (y)
                      (+ x y)))
                  2)
                 3)",
            Some(expected),
            None,
            Some(terminal),
            None,
            13,
        );
    }

    #[test]
    fn test_prove_current_env_simple() {
        let s = &mut Store::<Fr>::default();
        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(current-env)",
            Some(expected),
            None,
            Some(terminal),
            None,
            1,
        );
    }

    #[test]
    fn test_prove_current_env_rest_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let expected = s.read("(current-env a)").unwrap();
        let error = s.get_cont_error();
        test_aux(
            s,
            "(current-env a)",
            Some(expected),
            None,
            Some(error),
            None,
            1,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_let_simple() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(1);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((a 1))
                  a)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
        );
    }

    #[test]
    fn test_prove_let_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(let ((a 1 2)) a)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_letrec_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(letrec ((a 1 2)) a)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_let_empty_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(let)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_let_empty_body_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(let ((a 1)))", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_letrec_empty_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(letrec)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_letrec_empty_body_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(letrec ((a 1)))", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_let_body_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = s.t();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(eq nil (let () nil))",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
        );
    }

    #[test]
    fn test_prove_let_rest_body_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(let ((a 1)) a 1)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_letrec_rest_body_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(letrec ((a 1)) a 1)", None, None, Some(error), None, 1);
    }

    #[test]
    #[ignore]
    fn test_prove_let_null_bindings() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let () (+ 1 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
        );
    }
    #[test]
    #[ignore]
    fn test_prove_letrec_null_bindings() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec () (+ 1 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_let() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(6);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((a 1)
                       (b 2)
                       (c 3))
                  (+ a (+ b c)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            18,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_arithmetic() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(20);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "((((lambda (x)
                      (lambda (y)
                        (lambda (z)
                          (* z
                             (+ x y)))))
                    2)
                  3)
                 4)",
            Some(expected),
            None,
            Some(terminal),
            None,
            23,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_comparison() {
        let s = &mut Store::<Fr>::default();
        let expected = s.t();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((x 2)
                       (y 3)
                       (z 4))
                  (= 20 (* z
                           (+ x y))))",
            Some(expected),
            None,
            Some(terminal),
            None,
            21,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_conditional() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((true (lambda (a)
                               (lambda (b)
                                 a)))
                       (false (lambda (a)
                                (lambda (b)
                                  b)))
                      ;; NOTE: We cannot shadow IF because it is built-in.
                      (if- (lambda (a)
                             (lambda (c)
                               (lambda (cond)
                                 ((cond a) c))))))
                 (((if- 5) 6) true))",
            Some(expected),
            None,
            Some(terminal),
            None,
            35,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_conditional2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(6);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((true (lambda (a)
                               (lambda (b)
                                 a)))
                       (false (lambda (a)
                                (lambda (b)
                                  b)))
                      ;; NOTE: We cannot shadow IF because it is built-in.
                      (if- (lambda (a)
                             (lambda (c)
                               (lambda (cond)
                                 ((cond a) c))))))
                 (((if- 5) 6) false))",
            Some(expected),
            None,
            Some(terminal),
            None,
            32,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_fundamental_conditional_bug() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((true (lambda (a)
                               (lambda (b)
                                 a)))
                       ;; NOTE: We cannot shadow IF because it is built-in.
                       (if- (lambda (a)
                              (lambda (c)
                               (lambda (cond)
                                 ((cond a) c))))))
                 (((if- 5) 6) true))",
            Some(expected),
            None,
            Some(terminal),
            None,
            32,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_fully_evaluates() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(10);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(if t (+ 5 5) 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_recursion() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((exp (lambda (base)
                                   (lambda (exponent)
                                     (if (= 0 exponent)
                                         1
                                         (* base ((exp base) (- exponent 1))))))))
                           ((exp 5) 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            66,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_recursion_multiarg() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((exp (lambda (base exponent)
                                   (if (= 0 exponent)
                                       1
                                       (* base (exp base (- exponent 1)))))))
                           (exp 5 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            69,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_recursion_optimized() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((exp (lambda (base)
                                (letrec ((base-inner
                                           (lambda (exponent)
                                             (if (= 0 exponent)
                                                 1
                                                 (* base (base-inner (- exponent 1)))))))
                                        base-inner))))
                   ((exp 5) 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            56,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_tail_recursion() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((exp (lambda (base)
                                   (lambda (exponent-remaining)
                                     (lambda (acc)
                                       (if (= 0 exponent-remaining)
                                           acc
                                           (((exp base) (- exponent-remaining 1)) (* acc base))))))))
                          (((exp 5) 2) 1))",
            Some(expected),
            None,
            Some(terminal),
            None,
            93,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_tail_recursion_somewhat_optimized() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((exp (lambda (base)
                                   (letrec ((base-inner
                                              (lambda (exponent-remaining)
                                                (lambda (acc)
                                                  (if (= 0 exponent-remaining)
                                                      acc
                                                     ((base-inner (- exponent-remaining 1)) (* acc base)))))))
                                           base-inner))))
                          (((exp 5) 2) 1))",
            Some(expected),
            None,
            Some(terminal),
            None,
            81,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_no_mutual_recursion() {
        let s = &mut Store::<Fr>::default();
        let expected = s.t();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((even (lambda (n)
                                  (if (= 0 n)
                                      t
                                      (odd (- n 1)))))
                          (odd (lambda (n)
                                 (even (- n 1)))))
                        ;; NOTE: This is not true mutual-recursion.
                        ;; However, it exercises the behavior of LETREC.
                        (odd 1))",
            Some(expected),
            None,
            Some(terminal),
            None,
            22,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_no_mutual_recursion_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(
            s,
            "(letrec ((even (lambda (n)
                                  (if (= 0 n)
                                      t
                                      (odd (- n 1)))))
                          (odd (lambda (n)
                                 (even (- n 1)))))
                        ;; NOTE: This is not true mutual-recursion.
                        ;; However, it exercises the behavior of LETREC.
                        (odd 2))",
            None,
            None,
            Some(error),
            None,
            25,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_cons1() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(1);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(car (cons 1 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
        );
    }

    #[test]
    fn test_prove_car_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(car (1 2) 3)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_cdr_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(cdr (1 2) 3)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_atom_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(atom 123 4)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_emit_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "(emit 123 4)", None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_cons2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(cdr (cons 1 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda1() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "((lambda () 123))",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(10);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((x 9) (f (lambda () (+ x 1)))) (f))",
            Some(expected),
            None,
            Some(terminal),
            None,
            10,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda3() {
        let s = &mut Store::<Fr>::default();
        let expected = {
            let arg = s.sym("x");
            let num = s.num(123);
            let body = s.list(&[num]);
            let env = s.nil();
            s.intern_fun(arg, body, env)
        };
        let terminal = s.get_cont_terminal();
        nova_test_full_aux(
            s,
            "((lambda (x) 123))",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            DEFAULT_REDUCTION_COUNT,
            false,
            None,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda4() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, "((lambda () 123) 1)", None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_zero_arg_lambda5() {
        let s = &mut Store::<Fr>::default();
        let expected = s.read("(123)").unwrap();
        let error = s.get_cont_error();
        test_aux(s, "(123)", Some(expected), None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_zero_arg_lambda6() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let error = s.get_cont_error();
        test_aux(
            s,
            "((emit 123))",
            Some(expected),
            None,
            Some(error),
            None,
            5,
        );
    }

    #[test]
    fn test_prove_nested_let_closure_regression() {
        let s = &mut Store::<Fr>::default();
        let terminal = s.get_cont_terminal();
        let expected = s.num(6);
        let expr = "(let ((data-function (lambda () 123))
                          (x 6)
                          (data (data-function)))
                      x)";
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 14);
    }

    #[test]
    #[ignore]
    fn test_prove_minimal_tail_call() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec
                   ((f (lambda (x)
                         (if (= x 3)
                             123
                             (f (+ x 1))))))
                   (f 0))",
            Some(expected),
            None,
            Some(terminal),
            None,
            50,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_cons_in_function1() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(((lambda (a)
                    (lambda (b)
                      (car (cons a b))))
                  2)
                 3)",
            Some(expected),
            None,
            Some(terminal),
            None,
            15,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_cons_in_function2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(((lambda (a)
                    (lambda (b)
                      (cdr (cons a b))))
                  2)
                 3)",
            Some(expected),
            None,
            Some(terminal),
            None,
            15,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiarg_eval_bug() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(car (cdr '(1 2 3 4)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiple_letrec_bindings() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec
                   ((x 888)
                    (f (lambda (x)
                         (if (= x 5)
                             123
                             (f (+ x 1))))))
                  (f 0))",
            Some(expected),
            None,
            Some(terminal),
            None,
            78,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_tail_call2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec
                   ((f (lambda (x)
                         (if (= x 5)
                             123
                             (f (+ x 1)))))
                    (g (lambda (x) (f x))))
                  (g 0))",
            Some(expected),
            None,
            Some(terminal),
            None,
            84,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiple_letrecstar_bindings() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(13);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((double (lambda (x) (* 2 x)))
                           (square (lambda (x) (* x x))))
                          (+ (square 3) (double 2)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            22,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiple_letrecstar_bindings_referencing() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(11);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((double (lambda (x) (* 2 x)))
                           (double-inc (lambda (x) (+ 1 (double x)))))
                          (+ (double 3) (double-inc 2)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            31,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiple_letrecstar_bindings_recursive() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(33);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((exp (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp base (- exponent 1))))))
                           (exp2 (lambda (base exponent)
                                   (if (= 0 exponent)
                                      1
                                      (* base (exp2 base (- exponent 1))))))
                          (exp3 (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp3 base (- exponent 1)))))))
                         (+ (+ (exp 3 2) (exp2 2 3))
                            (exp3 4 2)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            242,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_dont_discard_rest_env() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(18);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(let ((z 9))
                   (letrec ((a 1)
                             (b 2)
                             (l (lambda (x) (+ z x))))
                            (l 9)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            22,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_fibonacci() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(1);
        let terminal = s.get_cont_terminal();
        nova_test_full_aux(
            s,
            "(letrec ((next (lambda (a b n target)
                     (if (eq n target)
                         a
                         (next b
                             (+ a b)
                             (+ 1 n)
                            target))))
                    (fib (next 0 1 0)))
                (fib 1))",
            Some(expected),
            None,
            Some(terminal),
            None,
            89,
            5,
            false,
            None,
        );
    }

    // #[test]
    // #[ignore]
    // fn test_prove_fibonacci_100() {
    //     let s = &mut Store::<Fr>::default();
    //     let expected = s.read("354224848179261915075").unwrap();
    //     let terminal = s.get_cont_terminal();
    //     nova_test_full_aux(
    //         s,
    //         "(letrec ((next (lambda (a b n target)
    //                  (if (eq n target)
    //                      a
    //                      (next b
    //                          (+ a b)
    //                          (+ 1 n)
    //                         target))))
    //                 (fib (next 0 1 0)))
    //             (fib 100))",
    //         Some(expected),
    //         None,
    //         Some(terminal),
    //         None,
    //         4841,
    //         5,
    //         false,
    //     );
    // }

    #[test]
    fn test_prove_terminal_continuation_regression() {
        let s = &mut Store::<Fr>::default();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((a (lambda (x) (cons 2 2))))
               (a 1))",
            None,
            None,
            Some(terminal),
            None,
            9,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_chained_functional_commitment() {
        let s = &mut Store::<Fr>::default();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            "(letrec ((secret 12345)
                      (a (lambda (acc x)
                           (let ((acc (+ acc x)))
                             (cons acc (cons secret (a acc)))))))
                (a 0 5))",
            None,
            None,
            Some(terminal),
            None,
            39,
        );
    }

    #[test]
    fn test_prove_begin_empty() {
        let s = &mut Store::<Fr>::default();
        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux(s, "(begin)", Some(expected), None, Some(terminal), None, 2);
    }

    #[test]
    fn test_prove_begin_emit() {
        let s = &mut Store::<Fr>::default();
        let expr = "(begin (emit 1) (emit 2) (emit 3))";
        let expected_expr = s.num(3);
        let expected_emitted = vec![s.num(1), s.num(2), s.num(3)];
        test_aux(
            s,
            expr,
            Some(expected_expr),
            None,
            None,
            Some(expected_emitted),
            13,
        );
    }

    #[test]
    fn test_prove_str_car() {
        let s = &mut Store::<Fr>::default();
        let expected_a = s.read(r#"#\a"#).unwrap();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            r#"(car "apple")"#,
            Some(expected_a),
            None,
            Some(terminal),
            None,
            2,
        );
    }

    #[test]
    fn test_prove_str_cdr() {
        let s = &mut Store::<Fr>::default();
        let expected_pple = s.read(r#" "pple" "#).unwrap();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            r#"(cdr "apple")"#,
            Some(expected_pple),
            None,
            Some(terminal),
            None,
            2,
        );
    }

    #[test]
    fn test_prove_str_car_empty() {
        let s = &mut Store::<Fr>::default();
        let expected_nil = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            r#"(car "")"#,
            Some(expected_nil),
            None,
            Some(terminal),
            None,
            2,
        );
    }

    #[test]
    fn test_prove_str_cdr_empty() {
        let s = &mut Store::<Fr>::default();
        let expected_empty_str = s.intern_str("");
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            r#"(cdr "")"#,
            Some(expected_empty_str),
            None,
            Some(terminal),
            None,
            2,
        );
    }

    #[test]
    fn test_prove_strcons() {
        let s = &mut Store::<Fr>::default();
        let expected_apple = s.read(r#" "apple" "#).unwrap();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            r#"(strcons #\a "pple")"#,
            Some(expected_apple),
            None,
            Some(terminal),
            None,
            3,
        );
    }

    #[test]
    fn test_prove_str_cons_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, r#"(strcons #\a 123)"#, None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_one_arg_cons_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, r#"(cons "")"#, None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_car_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            r#"(car NIL)"#,
            Some(expected),
            None,
            Some(terminal),
            None,
            2,
        );
    }

    #[test]
    fn test_prove_cdr_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            r#"(cdr NIL)"#,
            Some(expected),
            None,
            Some(terminal),
            None,
            2,
        );
    }

    #[test]
    fn test_prove_car_cdr_invalid_tag_error_sym() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, r#"(car car)"#, None, None, Some(error), None, 2);
        test_aux(s, r#"(cdr car)"#, None, None, Some(error), None, 2);
    }

    #[test]
    fn test_prove_car_cdr_invalid_tag_error_char() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, r#"(car #\a)"#, None, None, Some(error), None, 2);
        test_aux(s, r#"(cdr #\a)"#, None, None, Some(error), None, 2);
    }

    #[test]
    fn test_prove_car_cdr_invalid_tag_error_num() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(s, r#"(car 42)"#, None, None, Some(error), None, 2);
        test_aux(s, r#"(cdr 42)"#, None, None, Some(error), None, 2);
    }

    #[test]
    fn test_prove_car_cdr_of_cons() {
        let s = &mut Store::<Fr>::default();
        let res1 = s.num(1);
        let res2 = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux(
            s,
            r#"(car (cons 1 2))"#,
            Some(res1),
            None,
            Some(terminal),
            None,
            5,
        );
        test_aux(
            s,
            r#"(cdr (cons 1 2))"#,
            Some(res2),
            None,
            Some(terminal),
            None,
            5,
        );
    }

    #[test]
    fn test_prove_car_cdr_invalid_tag_error_lambda() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux(
            s,
            r#"(car (lambda (x) x))"#,
            None,
            None,
            Some(error),
            None,
            2,
        );
        test_aux(
            s,
            r#"(cdr (lambda (x) x))"#,
            None,
            None,
            Some(error),
            None,
            2,
        );
    }

    #[test]
    fn test_prove_hide_open() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (hide 123 456))";
        let expected = s.num(456);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 5);
    }

    #[test]
    fn test_prove_hide_wrong_secret_type() {
        let s = &mut Store::<Fr>::default();
        let expr = "(hide 'x 456)";
        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_hide_secret() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (hide 123 456))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 5);
    }

    #[test]
    fn test_prove_hide_open_sym() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (hide 123 'x))";
        let x = s.sym("x");
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(x), None, Some(terminal), None, 5);
    }

    #[test]
    fn test_prove_commit_open_sym() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (commit 'x))";
        let x = s.sym("x");
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(x), None, Some(terminal), None, 4);
    }

    #[test]
    fn test_prove_commit_open() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (commit 123))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 4);
    }

    #[test]
    fn test_prove_commit_error() {
        let s = &mut Store::<Fr>::default();
        let expr = "(commit 123 456)";
        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_open_error() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open 123 456)";
        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 1);
    }

    #[test]
    fn test_prove_open_wrong_type() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open 'asdf)";
        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 2);
    }

    #[test]
    fn test_prove_secret_wrong_type() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret 'asdf)";
        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 2);
    }

    #[test]
    fn test_prove_commit_secret() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (commit 123))";
        let expected = s.num(0);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 4);
    }

    #[test]
    fn test_prove_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(num 123)";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 2);
    }

    #[test]
    fn test_prove_num_char() {
        let s = &mut Store::<Fr>::default();
        let expr = r#"(num #\a)"#;
        let expected = s.num(97);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 2);
    }

    #[test]
    fn test_prove_char_num() {
        let s = &mut Store::<Fr>::default();
        let expr = r#"(char 97)"#;
        let expected_a = s.read(r#"#\a"#).unwrap();
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected_a), None, Some(terminal), None, 2);
    }

    #[test]
    fn test_prove_char_coercion() {
        let s = &mut Store::<Fr>::default();
        let expr = r#"(char (- 0 4294967200))"#;
        let expr2 = r#"(char (- 0 4294967199))"#;
        let expected_a = s.read(r#"#\a"#).unwrap();
        let expected_b = s.read(r#"#\b"#).unwrap();
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected_a), None, Some(terminal), None, 5);
        test_aux(s, expr2, Some(expected_b), None, Some(terminal), None, 5);
    }

    #[test]
    fn test_prove_commit_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(num (commit 123))";
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, None, None, Some(terminal), None, 4);
    }

    #[test]
    fn test_prove_hide_open_comm_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (comm (num (hide 123 456))))";
        let expected = s.num(456);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 9);
    }

    #[test]
    fn test_prove_hide_secret_comm_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (comm (num (hide 123 456))))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 9);
    }

    #[test]
    fn test_prove_commit_open_comm_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (comm (num (commit 123))))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 8);
    }

    #[test]
    fn test_prove_commit_secret_comm_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (comm (num (commit 123))))";
        let expected = s.num(0);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 8);
    }

    #[test]
    fn test_prove_commit_num_open() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (num (commit 123)))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(expected), None, Some(terminal), None, 6);
    }

    #[test]
    fn test_prove_num_invalid_tag() {
        let s = &mut Store::<Fr>::default();
        let expr = "(num (quote x))";
        let expr1 = "(num \"asdf\")";
        let expr2 = "(num '(1))";
        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 2);
        test_aux(s, expr1, None, None, Some(error), None, 2);
        test_aux(s, expr2, None, None, Some(error), None, 2);
    }

    #[test]
    fn test_prove_comm_invalid_tag() {
        let s = &mut Store::<Fr>::default();
        let expr = "(comm (quote x))";
        let expr1 = "(comm \"asdf\")";
        let expr2 = "(comm '(1))";
        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 2);
        test_aux(s, expr1, None, None, Some(error), None, 2);
        test_aux(s, expr2, None, None, Some(error), None, 2);
    }

    #[test]
    fn test_prove_char_invalid_tag() {
        let s = &mut Store::<Fr>::default();
        let expr = "(char (quote x))";
        let expr1 = "(char \"asdf\")";
        let expr2 = "(char '(1))";
        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 2);
        test_aux(s, expr1, None, None, Some(error), None, 2);
        test_aux(s, expr2, None, None, Some(error), None, 2);
    }

    #[test]
    fn test_prove_terminal_sym() {
        let s = &mut Store::<Fr>::default();
        let expr = "(quote x)";
        let x = s.sym("x");
        let terminal = s.get_cont_terminal();
        test_aux(s, expr, Some(x), None, Some(terminal), None, 1);
    }

    #[test]
    #[should_panic = "hidden value could not be opened"]
    fn test_prove_open_opaque_commit() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open 123)";
        test_aux(s, expr, None, None, None, None, 2);
    }

    #[test]
    #[should_panic]
    fn test_prove_secret_invalid_tag() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret 123)";
        test_aux(s, expr, None, None, None, None, 2);
    }

    #[test]
    #[should_panic = "secret could not be extracted"]
    fn test_prove_secret_opaque_commit() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (comm 123))";
        test_aux(s, expr, None, None, None, None, 2);
    }

    #[test]
    fn test_str_car_cdr_cons() {
        let s = &mut Store::<Fr>::default();
        let a = s.read(r#"#\a"#).unwrap();
        let apple = s.read(r#" "apple" "#).unwrap();
        let a_pple = s.read(r#" (#\a . "pple") "#).unwrap();
        let pple = s.read(r#" "pple" "#).unwrap();
        let empty = s.intern_str("");
        let nil = s.nil();
        let terminal = s.get_cont_terminal();
        let error = s.get_cont_error();

        test_aux(
            s,
            r#"(car "apple")"#,
            Some(a),
            None,
            Some(terminal),
            None,
            2,
        );
        test_aux(
            s,
            r#"(cdr "apple")"#,
            Some(pple),
            None,
            Some(terminal),
            None,
            2,
        );
        test_aux(s, r#"(car "")"#, Some(nil), None, Some(terminal), None, 2);
        test_aux(s, r#"(cdr "")"#, Some(empty), None, Some(terminal), None, 2);
        test_aux(
            s,
            r#"(cons #\a "pple")"#,
            Some(a_pple),
            None,
            Some(terminal),
            None,
            3,
        );

        test_aux(
            s,
            r#"(strcons #\a "pple")"#,
            Some(apple),
            None,
            Some(terminal),
            None,
            3,
        );

        test_aux(s, r#"(strcons #\a #\b)"#, None, None, Some(error), None, 3);

        test_aux(s, r#"(strcons "a" "b")"#, None, None, Some(error), None, 3);

        test_aux(s, r#"(strcons 1 2)"#, None, None, Some(error), None, 3);
    }

    fn relational_aux(s: &mut Store<Fr>, op: &str, a: &str, b: &str, res: bool) {
        let expr = &format!("({op} {a} {b})");
        let expected = if res { s.t() } else { s.nil() };
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(expected), None, Some(terminal), None, 3);
    }

    #[ignore]
    #[test]
    fn test_prove_test_relational() {
        let s = &mut Store::<Fr>::default();
        let lt = "<";
        let gt = ">";
        let lte = "<=";
        let gte = ">=";
        let zero = "0";
        let one = "1";
        let two = "2";

        let most_negative = &format!("{}", Num::<Fr>::most_negative());
        let most_positive = &format!("{}", Num::<Fr>::most_positive());
        let neg_one = &format!("{}", Num::<Fr>::Scalar(Fr::zero() - Fr::one()));

        relational_aux(s, lt, one, two, true);
        relational_aux(s, gt, one, two, false);
        relational_aux(s, lte, one, two, true);
        relational_aux(s, gte, one, two, false);

        relational_aux(s, lt, two, one, false);
        relational_aux(s, gt, two, one, true);
        relational_aux(s, lte, two, one, false);
        relational_aux(s, gte, two, one, true);

        relational_aux(s, lt, one, one, false);
        relational_aux(s, gt, one, one, false);
        relational_aux(s, lte, one, one, true);
        relational_aux(s, gte, one, one, true);

        relational_aux(s, lt, zero, two, true);
        relational_aux(s, gt, zero, two, false);
        relational_aux(s, lte, zero, two, true);
        relational_aux(s, gte, zero, two, false);

        relational_aux(s, lt, two, zero, false);
        relational_aux(s, gt, two, zero, true);
        relational_aux(s, lte, two, zero, false);
        relational_aux(s, gte, two, zero, true);

        relational_aux(s, lt, zero, zero, false);
        relational_aux(s, gt, zero, zero, false);
        relational_aux(s, lte, zero, zero, true);
        relational_aux(s, gte, zero, zero, true);

        relational_aux(s, lt, most_negative, zero, true);
        relational_aux(s, gt, most_negative, zero, false);
        relational_aux(s, lte, most_negative, zero, true);
        relational_aux(s, gte, most_negative, zero, false);

        relational_aux(s, lt, zero, most_negative, false);
        relational_aux(s, gt, zero, most_negative, true);
        relational_aux(s, lte, zero, most_negative, false);
        relational_aux(s, gte, zero, most_negative, true);

        relational_aux(s, lt, most_negative, most_positive, true);
        relational_aux(s, gt, most_negative, most_positive, false);
        relational_aux(s, lte, most_negative, most_positive, true);
        relational_aux(s, gte, most_negative, most_positive, false);

        relational_aux(s, lt, most_positive, most_negative, false);
        relational_aux(s, gt, most_positive, most_negative, true);
        relational_aux(s, lte, most_positive, most_negative, false);
        relational_aux(s, gte, most_positive, most_negative, true);

        relational_aux(s, lt, most_negative, most_negative, false);
        relational_aux(s, gt, most_negative, most_negative, false);
        relational_aux(s, lte, most_negative, most_negative, true);
        relational_aux(s, gte, most_negative, most_negative, true);

        relational_aux(s, lt, one, most_positive, true);
        relational_aux(s, gt, one, most_positive, false);
        relational_aux(s, lte, one, most_positive, true);
        relational_aux(s, gte, one, most_positive, false);

        relational_aux(s, lt, most_positive, one, false);
        relational_aux(s, gt, most_positive, one, true);
        relational_aux(s, lte, most_positive, one, false);
        relational_aux(s, gte, most_positive, one, true);

        relational_aux(s, lt, one, most_negative, false);
        relational_aux(s, gt, one, most_negative, true);
        relational_aux(s, lte, one, most_negative, false);
        relational_aux(s, gte, one, most_negative, true);

        relational_aux(s, lt, most_negative, one, true);
        relational_aux(s, gt, most_negative, one, false);
        relational_aux(s, lte, most_negative, one, true);
        relational_aux(s, gte, most_negative, one, false);

        relational_aux(s, lt, neg_one, most_positive, true);
        relational_aux(s, gt, neg_one, most_positive, false);
        relational_aux(s, lte, neg_one, most_positive, true);
        relational_aux(s, gte, neg_one, most_positive, false);

        relational_aux(s, lt, most_positive, neg_one, false);
        relational_aux(s, gt, most_positive, neg_one, true);
        relational_aux(s, lte, most_positive, neg_one, false);
        relational_aux(s, gte, most_positive, neg_one, true);

        relational_aux(s, lt, neg_one, most_negative, false);
        relational_aux(s, gt, neg_one, most_negative, true);
        relational_aux(s, lte, neg_one, most_negative, false);
        relational_aux(s, gte, neg_one, most_negative, true);

        relational_aux(s, lt, most_negative, neg_one, true);
        relational_aux(s, gt, most_negative, neg_one, false);
        relational_aux(s, lte, most_negative, neg_one, true);
        relational_aux(s, gte, most_negative, neg_one, false);
    }

    #[test]
    fn test_relational_edge_case_identity() {
        let s = &mut Store::<Fr>::default();
        // Normally, a value cannot be less than the result of incrementing it.
        // However, the most positive field element (when viewed as signed)
        // is the exception. Incrementing it yields the most negative element,
        // which is less than the most positive.
        let expr = "(let ((most-positive (/ (- 0 1) 2))
                          (most-negative (+ 1 most-positive)))
                      (< most-negative most-positive))";
        let t = s.t();
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(t), None, Some(terminal), None, 19);
    }

    #[test]
    fn test_prove_test_eval() {
        let s = &mut Store::<Fr>::default();
        let expr = "(* 3 (eval  (cons '+ (cons 1 (cons 2 nil)))))";
        let expr2 = "(* 5 (eval '(+ 1 a) '((a . 3))))"; // two-arg eval, optional second arg is env.
        let res = s.num(9);
        let res2 = s.num(20);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 17);
        test_aux(s, expr2, Some(res2), None, Some(terminal), None, 9);
    }

    #[test]
    fn test_prove_test_keyword() {
        let s = &mut Store::<Fr>::default();

        let expr = ":asdf";
        let expr2 = "(eq :asdf :asdf)";
        let expr3 = "(eq :asdf 'asdf)";
        let res = s.key("ASDF");
        let res2 = s.get_t();
        let res3 = s.get_nil();

        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 1);
        test_aux(s, expr2, Some(res2), None, Some(terminal), None, 3);
        test_aux(s, expr3, Some(res3), None, Some(terminal), None, 3);
    }

    // The following functional commitment tests were discovered to fail. They are commented out (as tests) for now so
    // they can be addressed independently in future work.

    #[test]
    fn test_prove_functional_commitment() {
        let s = &mut Store::<Fr>::default();

        let expr = "(let ((f (commit (let ((num 9)) (lambda (f) (f num)))))
                          (inc (lambda (x) (+ x 1))))
                      ((open f) inc))";
        let res = s.num(10);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 25);
    }

    #[test]
    #[ignore]
    fn test_prove_complicated_functional_commitment() {
        let s = &mut Store::<Fr>::default();

        let expr = "(let ((f (commit (let ((nums '(1 2 3))) (lambda (f) (f nums)))))
                          (in (letrec ((sum-aux (lambda (acc nums)
                                              (if nums
                                                (sum-aux (+ acc (car nums)) (cdr nums))
                                                acc)))
                                   (sum (sum-aux 0)))
                             (lambda (nums)
                               (sum nums)))))

                      ((open f) in))";
        let res = s.num(6);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 108);
    }

    #[test]
    fn test_prove_test_fold_cons_regression() {
        let s = &mut Store::<Fr>::default();
        let expr = "(letrec ((fold (lambda (op acc l)
                                     (if l
                                         (fold op (op acc (car l)) (cdr l))
                                         acc))))
                      (fold (lambda (x y) (+ x y)) 0 '(1 2 3)))";
        let res = s.num(6);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 152);
    }

    #[test]
    fn test_prove_test_lambda_args_regression() {
        let s = &mut Store::<Fr>::default();

        let expr = "(cons (lambda (x y) nil) nil)";
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, None, None, Some(terminal), None, 3);
    }

    #[test]
    fn test_prove_reduce_sym_contradiction_regression() {
        let s = &mut Store::<Fr>::default();

        let expr = "(eval 'a '(nil))";
        let error = s.get_cont_error();

        test_aux(s, expr, None, None, Some(error), None, 4);
    }

    #[test]
    fn test_prove_test_self_eval_env_not_nil() {
        let s = &mut Store::<Fr>::default();

        // NOTE: cond1 shouldn't depend on env-is-not-nil
        // therefore this unit test is not very useful
        // the conclusion is that by removing condition env-is-not-nil from cond1,
        // we solve this soundness problem
        // this solution makes the circuit a bit smaller
        let expr = "(let ((a 1)) t)";

        let terminal = s.get_cont_terminal();
        test_aux(s, expr, None, None, Some(terminal), None, 3);
    }

    #[test]
    fn test_prove_test_self_eval_nil() {
        let s = &mut Store::<Fr>::default();

        // nil doesn't have SYM tag
        let expr = "nil";

        let terminal = s.get_cont_terminal();
        test_aux(s, expr, None, None, Some(terminal), None, 1);
    }

    #[test]
    fn test_prove_test_env_not_nil_and_binding_nil() {
        let s = &mut Store::<Fr>::default();

        let expr = "(let ((a 1) (b 2)) c)";

        let error = s.get_cont_error();
        test_aux(s, expr, None, None, Some(error), None, 7);
    }

    #[test]
    fn test_prove_test_eval_bad_form() {
        let s = &mut Store::<Fr>::default();
        let expr = "(* 5 (eval '(+ 1 a) '((0 . 3))))"; // two-arg eval, optional second arg is env. This tests for error on malformed env.
        let error = s.get_cont_error();

        test_aux(s, expr, None, None, Some(error), None, 8);
    }

    #[test]
    fn test_prove_test_u64_self_evaluating() {
        let s = &mut Store::<Fr>::default();

        let expr = "123u64";
        let res = s.uint64(123);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 1);
    }

    #[test]
    fn test_prove_test_u64_mul() {
        let s = &mut Store::<Fr>::default();

        let expr = "(* (u64 18446744073709551615) (u64 2))";
        let expr2 = "(* 18446744073709551615u64 2u64)";
        let expr3 = "(* (- 0u64 1u64) 2u64)";
        let expr4 = "(u64 18446744073709551617)";
        let res = s.uint64(18446744073709551614);
        let res2 = s.uint64(1);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 7);
        test_aux(s, expr2, Some(res), None, Some(terminal), None, 3);
        test_aux(s, expr3, Some(res), None, Some(terminal), None, 6);
        test_aux(s, expr4, Some(res2), None, Some(terminal), None, 2);
    }

    #[test]
    fn test_prove_test_u64_add() {
        let s = &mut Store::<Fr>::default();

        let expr = "(+ 18446744073709551615u64 2u64)";
        let expr2 = "(+ (- 0u64 1u64) 2u64)";
        let res = s.uint64(1);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 3);
        test_aux(s, expr2, Some(res), None, Some(terminal), None, 6);
    }

    #[test]
    fn test_prove_test_u64_sub() {
        let s = &mut Store::<Fr>::default();

        let expr = "(- 2u64 1u64)";
        let expr2 = "(- 0u64 1u64)";
        let expr3 = "(+ 1u64 (- 0u64 1u64))";
        let res = s.uint64(1);
        let res2 = s.uint64(18446744073709551615);
        let res3 = s.uint64(0);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 3);
        test_aux(s, expr2, Some(res2), None, Some(terminal), None, 3);
        test_aux(s, expr3, Some(res3), None, Some(terminal), None, 6);
    }

    #[test]
    fn test_prove_test_u64_div() {
        let s = &mut Store::<Fr>::default();

        let expr = "(/ 100u64 2u64)";
        let res = s.uint64(50);

        let expr2 = "(/ 100u64 3u64)";
        let res2 = s.uint64(33);

        let expr3 = "(/ 100u64 0u64)";

        let terminal = s.get_cont_terminal();
        let error = s.get_cont_error();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 3);
        test_aux(s, expr2, Some(res2), None, Some(terminal), None, 3);
        test_aux(s, expr3, None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_test_u64_mod() {
        let s = &mut Store::<Fr>::default();

        let expr = "(% 100u64 2u64)";
        let res = s.uint64(0);

        let expr2 = "(% 100u64 3u64)";
        let res2 = s.uint64(1);

        let expr3 = "(% 100u64 0u64)";

        let terminal = s.get_cont_terminal();
        let error = s.get_cont_error();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 3);
        test_aux(s, expr2, Some(res2), None, Some(terminal), None, 3);
        test_aux(s, expr3, None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_test_num_mod() {
        let s = &mut Store::<Fr>::default();

        let expr = "(% 100 3)";
        let expr2 = "(% 100 3u64)";
        let expr3 = "(% 100u64 3)";

        let error = s.get_cont_error();

        test_aux(s, expr, None, None, Some(error), None, 3);
        test_aux(s, expr2, None, None, Some(error), None, 3);
        test_aux(s, expr3, None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_test_u64_comp() {
        let s = &mut Store::<Fr>::default();

        let expr = "(< 0u64 1u64)";
        let expr2 = "(< 1u64 0u64)";
        let expr3 = "(<= 0u64 1u64)";
        let expr4 = "(<= 1u64 0u64)";

        let expr5 = "(> 0u64 1u64)";
        let expr6 = "(> 1u64 0u64)";
        let expr7 = "(>= 0u64 1u64)";
        let expr8 = "(>= 1u64 0u64)";

        let expr9 = "(<= 0u64 0u64)";
        let expr10 = "(>= 0u64 0u64)";

        let t = s.t();
        let nil = s.nil();
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(t), None, Some(terminal), None, 3);
        test_aux(s, expr2, Some(nil), None, Some(terminal), None, 3);
        test_aux(s, expr3, Some(t), None, Some(terminal), None, 3);
        test_aux(s, expr4, Some(nil), None, Some(terminal), None, 3);

        test_aux(s, expr5, Some(nil), None, Some(terminal), None, 3);
        test_aux(s, expr6, Some(t), None, Some(terminal), None, 3);
        test_aux(s, expr7, Some(nil), None, Some(terminal), None, 3);
        test_aux(s, expr8, Some(t), None, Some(terminal), None, 3);

        test_aux(s, expr9, Some(t), None, Some(terminal), None, 3);
        test_aux(s, expr10, Some(t), None, Some(terminal), None, 3);
    }

    #[test]
    fn test_prove_test_u64_conversion() {
        let s = &mut Store::<Fr>::default();

        let expr = "(+ 0 1u64)";
        let expr2 = "(num 1u64)";
        let expr3 = "(+ 1 1u64)";
        let expr4 = "(u64 (+ 1 1))";
        let res = s.intern_num(1);
        let res2 = s.intern_num(2);
        let res3 = s.get_u64(2);
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 3);
        test_aux(s, expr2, Some(res), None, Some(terminal), None, 2);
        test_aux(s, expr3, Some(res2), None, Some(terminal), None, 3);
        test_aux(s, expr4, Some(res3), None, Some(terminal), None, 5);
    }

    #[test]
    fn test_prove_test_u64_num_comparison() {
        let s = &mut Store::<Fr>::default();

        let expr = "(= 1 1u64)";
        let expr2 = "(= 1 2u64)";
        let t = s.t();
        let nil = s.nil();
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(t), None, Some(terminal), None, 3);
        test_aux(s, expr2, Some(nil), None, Some(terminal), None, 3);
    }

    #[test]
    fn test_prove_test_u64_num_cons() {
        let s = &mut Store::<Fr>::default();

        let expr = "(cons 1 1u64)";
        let expr2 = "(cons 1u64 1)";
        let res = s.read("(1 . 1u64)").unwrap();
        let res2 = s.read("(1u64 . 1)").unwrap();
        let terminal = s.get_cont_terminal();

        test_aux(s, expr, Some(res), None, Some(terminal), None, 3);
        test_aux(s, expr2, Some(res2), None, Some(terminal), None, 3);
    }

    #[test]
    fn test_prove_test_hide_u64_secret() {
        let s = &mut Store::<Fr>::default();

        let expr = "(hide 0u64 123)";
        let error = s.get_cont_error();

        test_aux(s, expr, None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_test_mod_by_zero_error() {
        let s = &mut Store::<Fr>::default();

        let expr = "(% 0 0)";
        let error = s.get_cont_error();

        test_aux(s, expr, None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_dotted_syntax_error() {
        let s = &mut Store::<Fr>::default();
        let expr = "(let ((a (lambda (x) (+ x 1)))) (a . 1))";
        let error = s.get_cont_error();

        test_aux(s, expr, None, None, Some(error), None, 3);
    }

    #[test]
    fn test_prove_call_literal_fun() {
        let s = &mut Store::<Fr>::default();
        let empty_env = s.get_nil();
        let arg = s.sym("X");
        let body = s.read("((+ X 1))").unwrap();
        let fun = s.intern_fun(arg, body, empty_env);
        let input = s.num(9);
        let expr = s.list(&[fun, input]);
        let res = s.num(10);
        let terminal = s.get_cont_terminal();

        nova_test_full_aux2(
            s,
            expr,
            Some(res),
            None,
            Some(terminal),
            None,
            7,
            DEFAULT_REDUCTION_COUNT,
            false,
            None,
        );
    }

    #[test]
    fn test_prove_lambda_body_syntax() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();

        test_aux(s, "((lambda ()))", None, None, Some(error), None, 2);
        test_aux(s, "((lambda () 1 2))", None, None, Some(error), None, 2);
        test_aux(s, "((lambda (x)) 1)", None, None, Some(error), None, 3);
        test_aux(s, "((lambda (x) 1 2) 1)", None, None, Some(error), None, 3);
    }

    #[test]
    #[ignore]
    fn test_eval_non_symbol_binding_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();

        let mut test = |x| {
            let expr = format!("(let (({x} 123)) {x})");
            let expr2 = format!("(letrec (({x} 123)) {x})");
            let expr3 = format!("(lambda ({x}) {x})");

            test_aux(s, &expr, None, None, Some(error), None, 1);
            test_aux(s, &expr2, None, None, Some(error), None, 1);
            test_aux(s, &expr3, None, None, Some(error), None, 1);
        };

        test(":a");
        test("1");
        test("\"string\"");
        test("1u64");
        test("#\\x");
    }
    #[test]
    fn test_prove_head_with_sym_mimicking_value() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();

        let hash_num = |s: &mut Store<Fr>, name| {
            let sym = s.sym(name);
            let scalar_ptr = s.hash_expr(&sym).unwrap();
            let hash = *scalar_ptr.value();
            Num::Scalar(hash)
        };
        {
            // binop
            let expr = format!("({} 1 1)", hash_num(s, "+"));
            test_aux(s, &expr, None, None, Some(error), None, 1);
        }
        {
            // unop
            let expr = format!("({} '(1 . 2))", hash_num(s, "car"));
            test_aux(s, &expr, None, None, Some(error), None, 1);
        }
        {
            // let_or_letrec
            let expr = format!("({} ((a 1)) a)", hash_num(s, "let"));
            test_aux(s, &expr, None, None, Some(error), None, 1);
        }
        {
            // current-env
            let expr = format!("({})", hash_num(s, "current-env"));
            test_aux(s, &expr, None, None, Some(error), None, 1);
        }
        {
            // lambda
            let expr = format!("({} (x) 123)", hash_num(s, "lambda"));
            test_aux(s, &expr, None, None, Some(error), None, 1);
        }
        {
            // quote
            let expr = format!("({} asdf)", hash_num(s, "quote"));
            test_aux(s, &expr, None, None, Some(error), None, 1);
        }
        {
            // if
            let expr = format!("({} t 123 456)", hash_num(s, "if"));
            test_aux(s, &expr, None, None, Some(error), None, 1);
        }
    }
}
