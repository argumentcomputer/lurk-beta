#![allow(non_snake_case)]

use abomonation::Abomonation;
use bellpepper_core::{num::AllocatedNum, ConstraintSystem};
use ff::PrimeField;
use halo2curves::bn256::Fr as Bn256Scalar;
use nova::{
    errors::NovaError,
    provider::{Bn256Engine, GrumpkinEngine, PallasEngine, VestaEngine},
    traits::{
        circuit::{StepCircuit, TrivialCircuit},
        evaluation::EvaluationEngineTrait,
        snark::RelaxedR1CSSNARKTrait,
        Engine,
    },
    CircuitShape, CompressedSNARK, ProverKey, RecursiveSNARK, VerifierKey,
};
use pasta_curves::pallas;
use serde::{Deserialize, Serialize};
use std::{
    marker::PhantomData,
    sync::{Arc, Mutex},
};

use crate::{
    config::lurk_config,
    coprocessor::Coprocessor,
    error::ProofError,
    eval::lang::Lang,
    field::LurkField,
    proof::{supernova::FoldingConfig, FrameLike, MultiFrameTrait, Prover},
};

use super::{FoldingMode, RecursiveSNARKTrait};

/// This trait defines most of the requirements for programming generically over the supported Nova curve cycles
/// (currently Pallas/Vesta and BN254/Grumpkin). It being pegged on the `LurkField` trait encodes that we do
/// not expect more than one such cycle to be supported at a time for a given field.
pub trait CurveCycleEquipped: LurkField {
    /// ## Why the next 2 types?

    /// In theory it would be sufficient to abstract over the two group types of the curve cycle, but in practice Nova is a
    /// bit idiosyncratic in the [`nova::traits::evaluation::EvaluationEngineTrait<G>`], (PCS) it uses on these (its multilinear IPA : [`nova::provider::ipa_pc::EvaluationEngine<G>`])
    /// *and* that implementation requires an additional trait bound `CommitmentKeyExtTrait` for this type.
    ///
    /// The following abstracts over curve cycle groups for which there exists an implementation of [`nova::traits::evaluation::EvaluationEngineTrait<G>`],
    /// encapsulating these idiosyncracies within Nova.

    /// a concrete implementation of an [`nova::traits::evaluation::EvaluationEngineTrait<G>`] for G1,
    type EE1: EvaluationEngineTrait<Self::E1>;
    /// a concrete implementation of an [`nova::traits::evaluation::EvaluationEngineTrait<G>`] for G2,
    type EE2: EvaluationEngineTrait<Self::E2>;

    /// The group type for the first curve in the cycle.
    type E1: Engine<Base = <Self::E2 as Engine>::Scalar, Scalar = Self>;
    /// The  group type for the second curve in the cycle.
    type E2: Engine<Base = <Self::E1 as Engine>::Scalar>;
}

impl CurveCycleEquipped for pallas::Scalar {
    type EE1 = nova::provider::ipa_pc::EvaluationEngine<Self::E1>;
    type EE2 = nova::provider::ipa_pc::EvaluationEngine<Self::E2>;

    type E1 = PallasEngine;
    type E2 = VestaEngine;
}
// The impl CurveCycleEquipped for vesta::Scalar is academically possible, but voluntarily omitted to avoid confusion.

impl CurveCycleEquipped for Bn256Scalar {
    type EE1 = nova::provider::ipa_pc::EvaluationEngine<Self::E1>;
    type EE2 = nova::provider::ipa_pc::EvaluationEngine<Self::E2>;

    type E1 = Bn256Engine;
    type E2 = GrumpkinEngine;
}
// The impl CurveCycleEquipped for grumpkin::Scalar is academically possible, but voluntarily omitted to avoid confusion.

/// Convenience alias for the primary group type pegged to a LurkField through a CurveCycleEquipped type.
pub type E1<F> = <F as CurveCycleEquipped>::E1;
/// Convenience alias for the secondary group type pegged to a LurkField through a CurveCycleEquipped type.
pub type E2<F> = <F as CurveCycleEquipped>::E2;

/// Type alias for the Evaluation Engine using G1 group elements.
pub type EE1<F> = <F as CurveCycleEquipped>::EE1;
/// Type alias for the Evaluation Engine using G2 group elements.
pub type EE2<F> = <F as CurveCycleEquipped>::EE2;

/// Type alias for the Relaxed R1CS Spartan SNARK using G1 group elements, EE1.
// NOTE: this is not a SNARK that uses computational commitments,
// that SNARK would be found at nova::spartan::ppsnark::RelaxedR1CSSNARK,
pub type SS1<F> = nova::spartan::snark::RelaxedR1CSSNARK<E1<F>, EE1<F>>;
/// Type alias for the Relaxed R1CS Spartan SNARK using G2 group elements, EE2.
// NOTE: this is not a SNARK that uses computational commitments,
// that SNARK would be found at nova::spartan::ppsnark::RelaxedR1CSSNARK,
pub type SS2<F> = nova::spartan::snark::RelaxedR1CSSNARK<E2<F>, EE2<F>>;

/// Type alias for a MultiFrame with S1 field elements.
/// This uses the <<F as CurveCycleEquipped>::G1 as Group>::Scalar type for the G1 scalar field elements
/// to reflect it this should not be used outside the Nova context
pub type C1LEM<'a, F, C> = crate::lem::multiframe::MultiFrame<'a, F, C>;
/// Type alias for a Trivial Test Circuit with G2 scalar field elements.
pub type C2<F> = TrivialCircuit<<E2<F> as Engine>::Scalar>;

/// Type alias for Nova Circuit Parameters with the curve cycle types defined above.
pub type NovaCircuitShape<F> = CircuitShape<E1<F>>;

/// Type alias for Nova Public Parameters with the curve cycle types defined above.
pub type NovaPublicParams<F, C1> = nova::PublicParams<E1<F>, E2<F>, C1, C2<F>>;

/// A struct that contains public parameters for the Nova proving system.
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PublicParams<F, SC: StepCircuit<F>>
where
    F: CurveCycleEquipped,
    // technical bounds that would disappear once associated_type_bounds stabilizes
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pp: NovaPublicParams<F, SC>,
    pk: ProverKey<E1<F>, E2<F>, SC, C2<F>, SS1<F>, SS2<F>>,
    vk: VerifierKey<E1<F>, E2<F>, SC, C2<F>, SS1<F>, SS2<F>>,
}

impl<F: CurveCycleEquipped, SC: StepCircuit<F>> Abomonation for PublicParams<F, SC>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    unsafe fn entomb<W: std::io::Write>(&self, bytes: &mut W) -> std::io::Result<()> {
        self.pp.entomb(bytes)?;
        self.pk.entomb(bytes)?;
        self.vk.entomb(bytes)?;
        Ok(())
    }

    unsafe fn exhume<'b>(&mut self, mut bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
        let temp = bytes;
        bytes = self.pp.exhume(temp)?;
        let temp = bytes;
        bytes = self.pk.exhume(temp)?;
        let temp = bytes;
        bytes = self.vk.exhume(temp)?;
        Some(bytes)
    }

    fn extent(&self) -> usize {
        self.pp.extent() + self.pk.extent() + self.vk.extent()
    }
}

/// An enum representing the two types of proofs that can be generated and verified.
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub enum Proof<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// A proof for the intermediate steps of a recursive computation
    Recursive(
        Box<RecursiveSNARK<E1<F>, E2<F>, M, C2<F>>>,
        PhantomData<&'a C>,
    ),
    /// A proof for the final step of a recursive computation
    Compressed(
        Box<CompressedSNARK<E1<F>, E2<F>, M, C2<F>, SS1<F>, SS2<F>>>,
        PhantomData<&'a C>,
    ),
}

/// Computes a cache key of the primary circuit. The point is that if a circuit
/// changes in any way but has the same `rc`/`Lang`, then we still want the
/// public params to stay in sync with the changes.
///
/// Note: For now, we use ad-hoc circuit cache keys.
/// See: [crate::public_parameters::instance]
pub fn circuit_cache_key<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
) -> F {
    let folding_config = Arc::new(FoldingConfig::new_ivc(lang, 2));
    let circuit = M::blank(folding_config, 0);
    F::from(rc as u64) * nova::circuit_digest::<F::E1, F::E2, _>(&circuit)
}

/// Generates the public parameters for the Nova proving system.
pub fn public_params<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: StepCircuit<F> + MultiFrameTrait<'a, F, C>,
>(
    reduction_count: usize,
    lang: Arc<Lang<F, C>>,
) -> PublicParams<F, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let (circuit_primary, circuit_secondary) = circuits(reduction_count, lang);

    let commitment_size_hint1 = <SS1<F> as RelaxedR1CSSNARKTrait<E1<F>>>::ck_floor();
    let commitment_size_hint2 = <SS2<F> as RelaxedR1CSSNARKTrait<E2<F>>>::ck_floor();

    let pp = nova::PublicParams::setup(
        &circuit_primary,
        &circuit_secondary,
        &*commitment_size_hint1,
        &*commitment_size_hint2,
    );
    let (pk, vk) = CompressedSNARK::setup(&pp).unwrap();
    PublicParams { pp, pk, vk }
}

/// Generates the circuits for the Nova proving system.
pub fn circuits<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>>(
    reduction_count: usize,
    lang: Arc<Lang<F, C>>,
) -> (M, C2<F>) {
    let folding_config = Arc::new(FoldingConfig::new_ivc(lang, reduction_count));
    (M::blank(folding_config, 0), TrivialCircuit::default())
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>>
    RecursiveSNARKTrait<'a, F, C, M> for Proof<'a, F, C, M>
where
    <F as PrimeField>::Repr: Abomonation,
    <<<F as CurveCycleEquipped>::E2 as Engine>::Scalar as PrimeField>::Repr: Abomonation,
{
    type PublicParams = PublicParams<F, M>;

    type ProveOutput = Self;

    /// The number of steps
    type ExtraVerifyInput = usize;

    type ErrorType = NovaError;

    #[tracing::instrument(skip_all, name = "nova::prove_recursively")]
    fn prove_recursively(
        pp: &PublicParams<F, M>,
        z0: &[F],
        steps: Vec<M>,
        store: &'a <M>::Store,
        reduction_count: usize,
        lang: Arc<Lang<F, C>>,
    ) -> Result<Self, ProofError> {
        assert!(!steps.is_empty());
        assert_eq!(steps[0].arity(), z0.len());
        let debug = false;
        let z0_primary = z0;
        let z0_secondary = Self::z0_secondary();

        assert_eq!(steps[0].frames().unwrap().len(), reduction_count);
        let (_circuit_primary, circuit_secondary): (M, TrivialCircuit<<E2<F> as Engine>::Scalar>) =
            circuits(reduction_count, lang);

        tracing::debug!("steps.len: {}", steps.len());

        // produce a recursive SNARK
        let mut recursive_snark: Option<RecursiveSNARK<E1<F>, E2<F>, M, C2<F>>> = None;

        // the shadowing here is voluntary
        let recursive_snark = if lurk_config(None, None)
            .perf
            .parallelism
            .recursive_steps
            .is_parallel()
        {
            let cc = steps.into_iter().map(Mutex::new).collect::<Vec<_>>();

            crossbeam::thread::scope(|s| {
                s.spawn(|_| {
                    // Skip the very first circuit's witness, so `prove_step` can begin immediately.
                    // That circuit's witness will not be cached and will just be computed on-demand.
                    cc.iter().skip(1).for_each(|mf| {
                        mf.lock()
                            .unwrap()
                            .cache_witness(store)
                            .expect("witness caching failed");
                    });
                });

                for circuit_primary in cc.iter() {
                    let circuit_primary = circuit_primary.lock().unwrap();
                    assert_eq!(reduction_count, circuit_primary.frames().unwrap().len());

                    let mut r_snark = recursive_snark.unwrap_or_else(|| {
                        RecursiveSNARK::new(
                            &pp.pp,
                            &circuit_primary,
                            &circuit_secondary,
                            z0_primary,
                            &z0_secondary,
                        )
                        .expect("Failed to construct initial recursive snark")
                    });
                    r_snark
                        .prove_step(&pp.pp, &circuit_primary, &circuit_secondary)
                        .expect("failure to prove Nova step");
                    recursive_snark = Some(r_snark);
                }
                recursive_snark
            })
            .unwrap()
        } else {
            for circuit_primary in steps.iter() {
                assert_eq!(reduction_count, circuit_primary.frames().unwrap().len());
                if debug {
                    // For debugging purposes, synthesize the circuit and check that the constraint system is satisfied.
                    use bellpepper_core::test_cs::TestConstraintSystem;
                    let mut cs = TestConstraintSystem::<<E1<F> as Engine>::Scalar>::new();

                    // This is a CircuitFrame, not an EvalFrame
                    let first_frame = circuit_primary.frames().unwrap().iter().next().unwrap();
                    let zi = M::io_to_scalar_vector(store, first_frame.input());
                    let zi_allocated: Vec<_> = zi
                        .iter()
                        .enumerate()
                        .map(|(i, x)| {
                            AllocatedNum::alloc(cs.namespace(|| format!("z{i}_1")), || Ok(*x))
                        })
                        .collect::<Result<_, _>>()?;

                    circuit_primary.synthesize(&mut cs, zi_allocated.as_slice())?;

                    assert!(cs.is_satisfied());
                }

                let mut r_snark = recursive_snark.unwrap_or_else(|| {
                    RecursiveSNARK::new(
                        &pp.pp,
                        circuit_primary,
                        &circuit_secondary,
                        z0_primary,
                        &z0_secondary,
                    )
                    .expect("Failed to construct initial recursive snark")
                });
                r_snark
                    .prove_step(&pp.pp, circuit_primary, &circuit_secondary)
                    .expect("failure to prove Nova step");
                recursive_snark = Some(r_snark);
            }
            recursive_snark
        };

        Ok(Self::Recursive(
            Box::new(recursive_snark.unwrap()),
            PhantomData,
        ))
    }

    fn compress(self, pp: &PublicParams<F, M>) -> Result<Self, ProofError> {
        match &self {
            Self::Recursive(recursive_snark, _) => Ok(Self::Compressed(
                Box::new(CompressedSNARK::<_, _, _, _, SS1<F>, SS2<F>>::prove(
                    &pp.pp,
                    &pp.pk,
                    recursive_snark,
                )?),
                PhantomData,
            )),
            Self::Compressed(..) => Ok(self),
        }
    }

    fn verify(
        &self,
        pp: &Self::PublicParams,
        z0: &[F],
        zi: &[F],
        num_steps: usize,
    ) -> Result<bool, Self::ErrorType> {
        let (z0_primary, zi_primary) = (z0, zi);
        let z0_secondary = Self::z0_secondary();
        let zi_secondary = &z0_secondary;

        let (zi_primary_verified, zi_secondary_verified) = match self {
            Self::Recursive(p, _) => p.verify(&pp.pp, num_steps, z0_primary, &z0_secondary)?,
            Self::Compressed(p, _) => p.verify(&pp.vk, num_steps, z0_primary, &z0_secondary)?,
        };

        Ok(zi_primary == zi_primary_verified && zi_secondary == &zi_secondary_verified)
    }
}

/// A struct for the Nova prover that operates on field elements of type `F`.
#[derive(Debug)]
pub struct NovaProver<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
> {
    /// The number of small-step reductions performed in each recursive step.
    reduction_count: usize,
    lang: Arc<Lang<F, C>>,
    folding_mode: FoldingMode,
    _phantom: PhantomData<&'a M>,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>>
    NovaProver<'a, F, C, M>
{
    /// Create a new NovaProver with a reduction count and a `Lang`
    #[inline]
    pub fn new(reduction_count: usize, lang: Arc<Lang<F, C>>) -> Self {
        Self {
            reduction_count,
            lang,
            folding_mode: FoldingMode::IVC,
            _phantom: PhantomData,
        }
    }
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>> Prover<'a, F, C, M>
    for NovaProver<'a, F, C, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    type PublicParams = PublicParams<F, M>;
    type ProveOutput = Proof<'a, F, C, M>;
    type RecursiveSnark = Proof<'a, F, C, M>;

    #[inline]
    fn reduction_count(&self) -> usize {
        self.reduction_count
    }

    #[inline]
    fn lang(&self) -> &Arc<Lang<F, C>> {
        &self.lang
    }

    #[inline]
    fn folding_mode(&self) -> &FoldingMode {
        &self.folding_mode
    }
}
