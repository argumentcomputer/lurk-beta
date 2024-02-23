#![allow(dead_code)]
use crate::{
    circuit::gadgets::pointer::AllocatedPtr,
    error::ProofError,
    field::LurkField,
    lem::{pointers::Ptr, store::Store},
    proof::{
        nova::{CurveCycleEquipped, E1},
        supernova::{Proof, PublicParams, SuperNovaPublicParams, C2, SS1, SS2},
        FrameLike, Prover, RecursiveSNARKTrait,
    },
};

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use once_cell::sync::OnceCell;
use tracing::info;

use super::query::Query;
use super::{CoroutineCircuit, LogMemo, MemoSet, Scope, DEFAULT_RC_FOR_QUERY};

use nova::{
    supernova::{
        error::SuperNovaError, snark::CompressedSNARK, NonUniformCircuit, RecursiveSNARK,
        StepCircuit,
    },
    traits::{
        snark::{BatchedRelaxedR1CSSNARKTrait, RelaxedR1CSSNARKTrait},
        Dual as DualEng,
    },
};
use std::marker::PhantomData;

/// Number of arguments a coroutine takes: CEK arguments + memoset arguments
const COROUTINE_ARITY: usize = 12;

type Coroutine<F, Q> = CoroutineCircuit<F, LogMemo<F>, Q>;

#[derive(Debug)]
pub(crate) struct MemosetProver<'a, F, Q> {
    reduction_count: usize,
    _phantom: PhantomData<&'a (F, Q)>,
}

impl<'a, F, Q> MemosetProver<'a, F, Q> {
    pub(crate) fn new(reduction_count: usize) -> Self {
        Self {
            reduction_count,
            _phantom: PhantomData,
        }
    }
    pub(crate) fn default() -> Self {
        Self::new(DEFAULT_RC_FOR_QUERY)
    }
}

impl<F, Q> NonUniformCircuit<E1<F>> for Coroutine<F, Q>
where
    F: CurveCycleEquipped + LurkField,
    Q: Query<F> + Send + Sync,
{
    type C1 = Coroutine<F, Q>;
    type C2 = C2<F>;

    fn num_circuits(&self) -> usize {
        Q::count()
    }

    fn primary_circuit(&self, circuit_index: usize) -> Coroutine<F, Q> {
        Coroutine::blank(circuit_index, self.store.clone(), self.rc)
    }

    fn secondary_circuit(&self) -> C2<F> {
        Default::default()
    }
}

impl<F: LurkField, Q: Query<F> + Send + Sync> StepCircuit<F> for Coroutine<F, Q> {
    fn arity(&self) -> usize {
        COROUTINE_ARITY
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        assert_eq!(z.len(), COROUTINE_ARITY);

        let size = COROUTINE_ARITY / 2;
        let mut input = Vec::with_capacity(size);
        for i in 0..size {
            input.push(AllocatedPtr::from_parts(
                z[2 * i].clone(),
                z[2 * i + 1].clone(),
            ));
        }
        let (next_pc, output_ptrs) = self.supernova_synthesize(cs, &input)?;
        assert_eq!(output_ptrs.len(), size);
        let mut output = Vec::with_capacity(COROUTINE_ARITY);
        for ptr in output_ptrs {
            output.push(ptr.tag().clone());
            output.push(ptr.hash().clone());
        }
        Ok((next_pc, output))
    }

    fn circuit_index(&self) -> usize {
        self.query_index
    }
}

impl<F: CurveCycleEquipped, Q: Query<F> + Send + Sync> RecursiveSNARKTrait<F, Coroutine<F, Q>>
    for Proof<F, Coroutine<F, Q>>
{
    type PublicParams = PublicParams<F>;

    type ErrorType = SuperNovaError;

    #[tracing::instrument(skip_all, name = "supernova::prove_recursively")]
    fn prove_recursively(
        pp: &PublicParams<F>,
        z0: &[F],
        steps: Vec<Coroutine<F, Q>>,
        _store: &Store<F>,
    ) -> Result<Self, ProofError> {
        let mut recursive_snark_option: Option<RecursiveSNARK<E1<F>>> = None;

        let z0_primary = z0;
        let z0_secondary = Self::z0_secondary();

        let mut prove_step = |i: usize, step: &Coroutine<F, Q>| {
            info!("prove_recursively, step {i}");

            let secondary_circuit = step.secondary_circuit();

            let mut recursive_snark = recursive_snark_option.clone().unwrap_or_else(|| {
                info!("prove_recursively, step {i}");
                RecursiveSNARK::new(
                    &pp.pp,
                    step,
                    step,
                    &secondary_circuit,
                    z0_primary,
                    &z0_secondary,
                )
                .unwrap()
            });

            recursive_snark
                .prove_step(&pp.pp, step, &secondary_circuit)
                .unwrap();

            recursive_snark_option = Some(recursive_snark);
        };
        for (i, step) in steps.iter().enumerate() {
            prove_step(i, step);
        }
        // This probably should be made unnecessary.
        Ok(Self::Recursive(
            Box::new(recursive_snark_option.expect("RecursiveSNARK missing")),
            PhantomData,
        ))
    }

    fn compress(self, pp: &PublicParams<F>) -> Result<Self, ProofError> {
        match &self {
            Self::Recursive(recursive_snark, _) => {
                let snark = CompressedSNARK::prove(&pp.pp, pp.pk(), recursive_snark)?;
                Ok(Self::Compressed(Box::new(snark), PhantomData))
            }
            Self::Compressed(..) => Ok(self),
        }
    }

    fn verify(&self, pp: &Self::PublicParams, z0: &[F], zi: &[F]) -> Result<bool, Self::ErrorType> {
        let (z0_primary, zi_primary) = (z0, zi);
        let z0_secondary = Self::z0_secondary();
        let zi_secondary = &z0_secondary;

        let (zi_primary_verified, zi_secondary_verified) = match self {
            Self::Recursive(p, _) => p.verify(&pp.pp, z0_primary, &z0_secondary)?,
            Self::Compressed(p, _) => p.verify(&pp.pp, pp.vk(), z0_primary, &z0_secondary)?,
        };

        Ok(zi_primary == zi_primary_verified && zi_secondary == &zi_secondary_verified)
    }
}

impl<F: LurkField, Q: Query<F> + Send + Sync> FrameLike<Ptr> for Coroutine<F, Q> {
    type FrameIO = Vec<Ptr>;
    #[inline]
    fn input(&self) -> &Vec<Ptr> {
        unimplemented!()
    }

    #[inline]
    fn output(&self) -> &Vec<Ptr> {
        unimplemented!()
    }
}

impl<'a, F: CurveCycleEquipped, Q: Query<F> + Send + Sync> Prover<'a, F>
    for MemosetProver<'a, F, Q>
{
    type Frame = Coroutine<F, Q>;
    type PublicParams = PublicParams<F>;
    type RecursiveSnark = Proof<F, Coroutine<F, Q>>;

    #[inline]
    fn reduction_count(&self) -> usize {
        self.reduction_count
    }

    #[inline]
    fn folding_mode(&self) -> &crate::proof::FoldingMode {
        unimplemented!()
    }

    fn evaluate_and_prove(
        &self,
        _pp: &Self::PublicParams,
        _expr: Ptr,
        _env: Ptr,
        _store: &'a Store<F>,
        _limit: usize,
    ) -> Result<(Self::RecursiveSnark, Vec<F>, Vec<F>, usize), ProofError> {
        unimplemented!()
    }

    fn prove(
        &self,
        pp: &Self::PublicParams,
        steps: Vec<Coroutine<F, Q>>,
        store: &'a Store<F>,
    ) -> Result<(Self::RecursiveSnark, Vec<F>, Vec<F>, usize), ProofError> {
        store.hydrate_z_cache();
        let input_ptrs = steps[0].input.as_ref().unwrap();
        let z0 = store.to_scalar_vector(input_ptrs);

        let num_steps = steps.len();

        let prove_output = Self::RecursiveSnark::prove_recursively(pp, &z0, steps, store)?;
        let zi = match prove_output {
            Proof::Recursive(ref snark, ..) => snark.zi_primary().clone(),
            Proof::Compressed(..) => unreachable!(),
        };

        Ok((prove_output, z0, zi, num_steps))
    }
}

fn prove_from_scope<F: CurveCycleEquipped, Q: Query<F> + Send + Sync>(
    prover: &MemosetProver<'_, F, Q>,
    pp: &PublicParams<F>,
    scope: &Scope<Q, LogMemo<F>, F>,
) -> Result<(Proof<F, Coroutine<F, Q>>, Vec<F>, Vec<F>, usize), ProofError> {
    let store = scope.store.as_ref();
    let mut steps = Vec::new();
    let mut iterator = scope.unique_inserted_keys.iter().peekable();
    while let Some((index, keys)) = iterator.next() {
        let rc = scope.rc_for_query(*index);
        let mut chunks = keys.chunks(rc).peekable();
        while let Some(chunk) = chunks.next() {
            let next_query_index = if chunks.peek().is_none() && iterator.peek().is_some() {
                *iterator.peek().unwrap().0
            } else {
                *index
            };
            let circuit: CoroutineCircuit<F, LogMemo<F>, Q> = CoroutineCircuit::new(
                None,
                scope,
                scope.memoset.clone(),
                chunk.to_vec(),
                *index,
                next_query_index,
                rc,
            );
            steps.push(circuit);
        }
    }
    let input_ptrs = Some(vec![
        store.dummy(),
        store.dummy(),
        store.dummy(),
        scope.init_memoset(),
        scope.init_transcript(),
        store.num(*scope.memoset.r().unwrap()),
    ]);
    steps[0].input = input_ptrs;
    prover.prove(pp, steps, store)
}

fn public_params<
    F: CurveCycleEquipped,
    SC: StepCircuit<F> + NonUniformCircuit<<F as CurveCycleEquipped>::E1>,
>(
    non_uniform_circuit: &SC,
) -> PublicParams<F> {
    let commitment_size_hint1 = <SS1<F> as BatchedRelaxedR1CSSNARKTrait<E1<F>>>::ck_floor();
    let commitment_size_hint2 = <SS2<F> as RelaxedR1CSSNARKTrait<DualEng<E1<F>>>>::ck_floor();

    let pp = SuperNovaPublicParams::<F>::setup(
        non_uniform_circuit,
        &*commitment_size_hint1,
        &*commitment_size_hint2,
    );
    PublicParams {
        pp,
        pk_and_vk: OnceCell::new(),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{coroutine::memoset::demo::DemoQuery, lem::tag::Tag, tag::ExprTag::Cons};
    use bellpepper::util_cs::Comparable;
    use bellpepper_core::{test_cs::TestConstraintSystem, Delta};
    use expect_test::{expect, Expect};
    use halo2curves::bn256::Fr;
    use std::sync::Arc;

    fn check_from_scope<F: CurveCycleEquipped, Q: Query<F> + Send + Sync>(
        scope: &Scope<Q, LogMemo<F>, F>,
        expected_constraints: &Expect,
        expected_aux: &Expect,
    ) {
        let store = scope.store.as_ref();
        let mut input_ptrs = [
            store.dummy(),
            store.dummy(),
            store.dummy(),
            scope.init_memoset(),
            scope.init_transcript(),
            store.intern_atom(Tag::Expr(Cons), *scope.memoset.r().unwrap()),
        ]
        .iter()
        .map(|ptr| store.hash_ptr(ptr))
        .collect::<Vec<_>>();
        let mut cs_prev = None;
        for (index, keys) in scope.unique_inserted_keys.iter() {
            let rc = scope.rc_for_query(*index);
            for chunk in keys.chunks(rc) {
                let mut cs = TestConstraintSystem::<F>::new();
                let alloc_ptr = input_ptrs
                    .iter()
                    .enumerate()
                    .map(|(i, zptr)| {
                        AllocatedPtr::alloc_infallible(
                            &mut cs.namespace(|| format!("input {i}")),
                            || *zptr,
                        )
                    })
                    .collect::<Vec<_>>();
                let circuit: CoroutineCircuit<F, LogMemo<F>, Q> = CoroutineCircuit::new(
                    None,
                    scope,
                    scope.memoset.clone(),
                    chunk.to_vec(),
                    *index,
                    *index,
                    rc,
                );
                let (_next, out) = circuit.supernova_synthesize(&mut cs, &alloc_ptr).unwrap();
                let unsat = cs.which_is_unsatisfied();

                if unsat.is_some() {
                    eprintln!("{:?}", unsat);
                }
                expected_constraints.assert_eq(&cs.num_constraints().to_string());
                expected_aux.assert_eq(&cs.aux().len().to_string());
                assert!(cs.is_satisfied());
                input_ptrs = out.into_iter().map(|x| x.get_value().unwrap()).collect();
                if let Some(cs_prev) = cs_prev {
                    // Check for all input expresssions that all frames are uniform.
                    assert_eq!(cs.delta(&cs_prev, true), Delta::Equal);
                }
                cs_prev = Some(cs);
            }
        }
    }

    #[test]
    fn coroutine_uniformity_test() {
        let s = Arc::new(Store::<Fr>::default());
        let query = s.read_with_default_state("(factorial . 40)").unwrap();
        let prover = MemosetProver::<'_, Fr, DemoQuery<Fr>>::new(1);
        let mut scope = Scope::<DemoQuery<_>, _, _>::new(prover.reduction_count, s);
        scope.query(query);
        scope.finalize_transcript();
        check_from_scope(&scope, &expect!["1772"], &expect!["1792"]);
    }

    #[test]
    fn coroutine_prove_test() {
        let s = Arc::new(Store::<Fr>::default());
        let query = s.read_with_default_state("(factorial . 40)").unwrap();
        let prover = MemosetProver::<'_, Fr, DemoQuery<Fr>>::new(10);
        let mut scope = Scope::new(prover.reduction_count, s.clone());
        scope.query(query);
        scope.finalize_transcript();

        let sc = CoroutineCircuit::<_, _, DemoQuery<Fr>>::blank(0, s, prover.reduction_count);
        let pp = public_params(&sc);
        let (snark, input, output, _iterations) = prove_from_scope(&prover, &pp, &scope).unwrap();
        assert!(snark.verify(&pp, &input, &output).unwrap());
    }
}
