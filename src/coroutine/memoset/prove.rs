use crate::{
    circuit::gadgets::pointer::AllocatedPtr,
    error::ProofError,
    field::LurkField,
    lem::{pointers::Ptr, store::Store},
    proof::{
        nova::{CurveCycleEquipped, E1, E2},
        supernova::{Proof, PublicParams, C2, SS1, SS2},
        FrameLike, Prover, RecursiveSNARKTrait,
    },
};

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use tracing::info;

use super::query::Query;
use super::{
    CoroutineCircuit, LogMemo, LogMemoCircuit, Scope, DEFAULT_RC_FOR_QUERY,
    DEFAULT_TRANSCRIBE_INTERNAL_INSERTIONS,
};

use nova::supernova::{
    error::SuperNovaError, snark::CompressedSNARK, NonUniformCircuit, RecursiveSNARK, StepCircuit,
};
use std::marker::PhantomData;

const COROUTINE_ARITY: usize = 12;

type Coroutine<'a, F, Q> = CoroutineCircuit<'a, F, LogMemoCircuit<F>, Q>;

#[derive(Debug)]
struct MemosetProver<'a, F, Q> {
    /// The number of small-step reductions performed in each recursive step of
    /// the primary Lurk circuit.
    reduction_count: usize,
    _phantom: PhantomData<&'a (F, Q)>,
}

impl<'a, F, Q> NonUniformCircuit<E1<F>, E2<F>, Coroutine<'a, F, Q>, C2<F>> for Coroutine<'a, F, Q>
where
    F: CurveCycleEquipped + LurkField,
    Q: Query<F> + 'a + Send + Sync,
{
    fn num_circuits(&self) -> usize {
        Q::count()
    }

    fn primary_circuit(&self, circuit_index: usize) -> Coroutine<'a, F, Q> {
        Coroutine::blank(
            circuit_index,
            self.memoset.r.clone(),
            self.queries,
            self.store,
        )
    }

    fn secondary_circuit(&self) -> C2<F> {
        Default::default()
    }
}

impl<'a, F: LurkField, Q: Query<F> + Send + Sync> StepCircuit<F> for Coroutine<'a, F, Q> {
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
        let (next_pc, output_ptrs) = CoroutineCircuit::synthesize(self, cs, &input)?;
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

impl<'a, F: CurveCycleEquipped, Q: Query<F> + Send + Sync>
    RecursiveSNARKTrait<F, Coroutine<'a, F, Q>> for Proof<F, Coroutine<'a, F, Q>>
{
    type PublicParams = PublicParams<F, Coroutine<'a, F, Q>>;

    type ErrorType = SuperNovaError;

    #[tracing::instrument(skip_all, name = "supernova::prove_recursively")]
    fn prove_recursively(
        pp: &PublicParams<F, Coroutine<'a, F, Q>>,
        z0: &[F],
        steps: Vec<Coroutine<'a, F, Q>>,
        _store: &Store<F>,
    ) -> Result<Self, ProofError> {
        let mut recursive_snark_option: Option<RecursiveSNARK<E1<F>, E2<F>>> = None;

        let z0_primary = z0;
        let z0_secondary = Self::z0_secondary();

        let mut prove_step = |i: usize, step: &Coroutine<'a, F, Q>| {
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
        Ok(Self::Recursive(Box::new(
            recursive_snark_option.expect("RecursiveSNARK missing"),
        )))
    }

    fn compress(self, pp: &PublicParams<F, Coroutine<'a, F, Q>>) -> Result<Self, ProofError> {
        match &self {
            Self::Recursive(recursive_snark) => {
                let snark = CompressedSNARK::<_, _, _, _, SS1<F>, SS2<F>>::prove(
                    &pp.pp,
                    pp.pk(),
                    recursive_snark,
                )?;
                Ok(Self::Compressed(Box::new(snark)))
            }
            Self::Compressed(..) => Ok(self),
        }
    }

    fn verify(&self, pp: &Self::PublicParams, z0: &[F], zi: &[F]) -> Result<bool, Self::ErrorType> {
        let (z0_primary, zi_primary) = (z0, zi);
        let z0_secondary = Self::z0_secondary();
        let zi_secondary = &z0_secondary;

        let (zi_primary_verified, zi_secondary_verified) = match self {
            Self::Recursive(p) => p.verify(&pp.pp, z0_primary, &z0_secondary)?,
            Self::Compressed(p) => p.verify(&pp.pp, pp.vk(), z0_primary, &z0_secondary)?,
        };

        Ok(zi_primary == zi_primary_verified && zi_secondary == &zi_secondary_verified)
    }
}

impl<'a, F: LurkField, Q: Query<F> + Send + Sync> FrameLike<Ptr> for Coroutine<'a, F, Q> {
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

impl<'a, F: CurveCycleEquipped, Q: Query<F> + Send + Sync> Prover<'a, F, Coroutine<'a, F, Q>>
    for MemosetProver<'a, F, Q>
{
    type PublicParams = PublicParams<F, Coroutine<'a, F, Q>>;
    type RecursiveSnark = Proof<F, Coroutine<'a, F, Q>>;

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
        pp: &Self::PublicParams,
        expr: Ptr,
        _env: Ptr,
        store: &'a Store<F>,
        _limit: usize,
    ) -> Result<(Self::RecursiveSnark, Vec<F>, Vec<F>, usize), ProofError> {
        let transcribe_internal = DEFAULT_TRANSCRIBE_INTERNAL_INSERTIONS;
        let circuit_query_rc = DEFAULT_RC_FOR_QUERY;
        let mut scope: Scope<Q, LogMemo<F>> = Scope::new(transcribe_internal, circuit_query_rc);
        scope.query(store, expr);
        scope.finalize_transcript(store);
        let steps = Vec::new();
        self.prove(pp, steps, store)
    }
}
