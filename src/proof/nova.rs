use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use halo2curves::bn256::Fr as Bn256Scalar;
use nova::{
    errors::NovaError,
    provider::{Bn256EngineKZG, PallasEngine},
    traits::{
        circuit::{StepCircuit, TrivialCircuit},
        evaluation::EvaluationEngineTrait,
        snark::RelaxedR1CSSNARKTrait,
        CurveCycleEquipped as NovaCurveCycleEquipped, Dual as DualEng, Engine,
    },
    CompressedSNARK, ProverKey, R1CSWithArity, RecursiveSNARK, VerifierKey,
};
use once_cell::sync::OnceCell;
use pasta_curves::pallas;
use serde::{Deserialize, Serialize};
use std::{
    marker::PhantomData,
    sync::{Arc, Mutex},
};
use tracing::info;

use crate::{
    config::lurk_config,
    coprocessor::Coprocessor,
    dual_channel::ChannelTerminal,
    error::ProofError,
    field::LurkField,
    lang::Lang,
    lem::{interpreter::Frame, multiframe::MultiFrame, pointers::Ptr, store::Store},
    proof::{supernova::FoldingConfig, FrameLike, Prover},
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
    /// encapsulating these idiosyncrasies within Nova.
    type E1: NovaCurveCycleEquipped<Scalar = Self>;

    /// a concrete implementation of an [`nova::traits::evaluation::EvaluationEngineTrait<G>`] for G1,
    type EE1: EvaluationEngineTrait<Self::E1>;
    /// a concrete implementation of an [`nova::traits::evaluation::EvaluationEngineTrait<G>`] for G2,
    type EE2: EvaluationEngineTrait<DualEng<Self::E1>>;
}

impl CurveCycleEquipped for pallas::Scalar {
    type E1 = PallasEngine;

    type EE1 = nova::provider::ipa_pc::EvaluationEngine<Self::E1>;
    type EE2 = nova::provider::ipa_pc::EvaluationEngine<DualEng<Self::E1>>;
}
// The impl CurveCycleEquipped for vesta::Scalar is academically possible, but voluntarily omitted to avoid confusion.

impl CurveCycleEquipped for Bn256Scalar {
    type EE1 =
        nova::provider::hyperkzg::EvaluationEngine<halo2curves::bn256::Bn256, Bn256EngineKZG>;
    type EE2 = nova::provider::ipa_pc::EvaluationEngine<DualEng<Self::E1>>;

    type E1 = Bn256EngineKZG;
}
// The impl CurveCycleEquipped for grumpkin::Scalar is academically possible, but voluntarily omitted to avoid confusion.

/// Convenience alias for the primary group type pegged to a LurkField through a CurveCycleEquipped type.
pub type E1<F> = <F as CurveCycleEquipped>::E1;

/// Convenience alias for the Dual field of a CurveCycleEquipped field.
/// By definition, this is both:
/// - the Base field for the associated Primary Engine,
/// - the Scalar field for the Secondary Engine.
pub type Dual<F> =
    <<<F as CurveCycleEquipped>::E1 as NovaCurveCycleEquipped>::Secondary as Engine>::Scalar;

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
pub type SS2<F> = nova::spartan::snark::RelaxedR1CSSNARK<DualEng<E1<F>>, EE2<F>>;

/// Type alias for a MultiFrame with S1 field elements.
/// This uses the <<F as CurveCycleEquipped>::G1 as Group>::Scalar type for the G1 scalar field elements
/// to reflect it this should not be used outside the Nova context
pub type C1LEM<'a, F, C> = crate::lem::multiframe::MultiFrame<'a, F, C>;
/// Type alias for a Trivial Test Circuit with G2 scalar field elements.
pub type C2<F> = TrivialCircuit<Dual<F>>;

/// Type alias for Nova Circuit Parameters with the curve cycle types defined above.
pub type NovaCircuitShape<F> = R1CSWithArity<E1<F>>;

/// Type alias for Nova Public Parameters with the curve cycle types defined above.
pub type NovaPublicParams<F> = nova::PublicParams<E1<F>>;

/// A struct that contains public parameters for the Nova proving system.
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PublicParams<F>
where
    F: CurveCycleEquipped,
{
    /// Public parameters for the Nova proving system.
    pub pp: NovaPublicParams<F>,
    /// Prover and verifier key for final proof compression
    #[serde(skip)]
    pk_and_vk: OnceCell<(
        ProverKey<E1<F>, SS1<F>, SS2<F>>,
        VerifierKey<E1<F>, SS1<F>, SS2<F>>,
    )>,
}

// this avoids dipping into the pk/vk
impl<F: CurveCycleEquipped> std::fmt::Debug for PublicParams<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PublicParams")
            .field("pp", &self.pp)
            .finish()
    }
}

impl<F: CurveCycleEquipped> PublicParams<F> {
    /// provides a reference to a ProverKey suitable for producing a CompressedProof
    pub fn pk(&self) -> &ProverKey<E1<F>, SS1<F>, SS2<F>> {
        let (pk, _vk) = self
            .pk_and_vk
            .get_or_init(|| CompressedSNARK::<E1<F>, SS1<F>, SS2<F>>::setup(&self.pp).unwrap());
        pk
    }

    /// provides a reference to a VerifierKey suitable for verifying a CompressedProof
    pub fn vk(&self) -> &VerifierKey<E1<F>, SS1<F>, SS2<F>> {
        let (_pk, vk) = self
            .pk_and_vk
            .get_or_init(|| CompressedSNARK::<E1<F>, SS1<F>, SS2<F>>::setup(&self.pp).unwrap());
        vk
    }
}

impl<F: CurveCycleEquipped> From<NovaPublicParams<F>> for PublicParams<F> {
    fn from(pp: NovaPublicParams<F>) -> PublicParams<F> {
        PublicParams {
            pp,
            pk_and_vk: OnceCell::new(),
        }
    }
}

/// An enum representing the two types of proofs that can be generated and verified.
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub enum Proof<F: CurveCycleEquipped, S> {
    /// A proof for the intermediate steps of a recursive computation along with
    /// the number of steps used for verification
    Recursive(Box<RecursiveSNARK<E1<F>>>, usize, PhantomData<S>),
    /// A proof for the final step of a recursive computation along with the number
    /// of steps used for verification
    Compressed(
        Box<CompressedSNARK<E1<F>, SS1<F>, SS2<F>>>,
        usize,
        PhantomData<S>,
    ),
}

/// Computes a cache key of the primary circuit. The point is that if a circuit
/// changes in any way but has the same `rc`/`Lang`, then we still want the
/// public params to stay in sync with the changes.
///
/// Note: For now, we use ad-hoc circuit cache keys.
/// See: [crate::public_parameters::instance]
pub fn circuit_cache_key<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
) -> F {
    let folding_config = Arc::new(FoldingConfig::new_ivc(lang, 2));
    let circuit = C1LEM::<'a, F, C>::blank(folding_config, 0);
    F::from(rc as u64) * nova::circuit_digest::<F::E1, _>(&circuit)
}

/// Generates the public parameters for the Nova proving system.
pub fn public_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    reduction_count: usize,
    lang: Arc<Lang<F, C>>,
) -> PublicParams<F> {
    let (circuit_primary, circuit_secondary) = circuits(reduction_count, lang);

    let commitment_size_hint1 = <SS1<F> as RelaxedR1CSSNARKTrait<E1<F>>>::ck_floor();
    let commitment_size_hint2 = <SS2<F> as RelaxedR1CSSNARKTrait<DualEng<E1<F>>>>::ck_floor();

    let pp = nova::PublicParams::setup(
        &circuit_primary,
        &circuit_secondary,
        &*commitment_size_hint1,
        &*commitment_size_hint2,
    )
    .unwrap();
    PublicParams {
        pp,
        pk_and_vk: OnceCell::new(),
    }
}

/// Generates the circuits for the Nova proving system.
pub fn circuits<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    reduction_count: usize,
    lang: Arc<Lang<F, C>>,
) -> (C1LEM<'a, F, C>, C2<F>) {
    let folding_config = Arc::new(FoldingConfig::new_ivc(lang, reduction_count));
    (
        C1LEM::<'a, F, C>::blank(folding_config, 0),
        TrivialCircuit::default(),
    )
}

/// For debugging purposes, synthesize the circuit and check that the constraint
/// system is satisfied
#[inline]
pub(crate) fn debug_step<F: LurkField, C: Coprocessor<F>>(
    circuit: &MultiFrame<'_, F, C>,
    store: &Store<F>,
) -> Result<(), SynthesisError> {
    use bellpepper_core::test_cs::TestConstraintSystem;
    let mut cs = TestConstraintSystem::<F>::new();

    let zi = store.to_scalar_vector(circuit.input());
    let zi_allocated: Vec<_> = zi
        .iter()
        .enumerate()
        .map(|(i, x)| AllocatedNum::alloc(cs.namespace(|| format!("z{i}_1")), || Ok(*x)))
        .collect::<Result<_, _>>()?;

    circuit.synthesize(&mut cs, zi_allocated.as_slice())?;

    assert!(cs.is_satisfied());
    Ok(())
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>> RecursiveSNARKTrait<F, C1LEM<'a, F, C>>
    for Proof<F, C1LEM<'a, F, C>>
{
    type PublicParams = PublicParams<F>;

    type ErrorType = NovaError;

    #[tracing::instrument(skip_all, name = "nova::prove_recursively")]
    fn prove_recursively(
        pp: &PublicParams<F>,
        z0: &[F],
        steps: Vec<C1LEM<'a, F, C>>,
        store: &Store<F>,
    ) -> Result<Self, ProofError> {
        let debug = false;
        assert_eq!(steps[0].arity(), z0.len());

        let secondary_circuit = TrivialCircuit::default();

        let num_steps = steps.len();
        info!("proving {num_steps} steps");

        let mut recursive_snark_option: Option<RecursiveSNARK<E1<F>>> = None;

        let prove_step =
            |i: usize, step: &C1LEM<'a, F, C>, rs: &mut Option<RecursiveSNARK<E1<F>>>| {
                if debug {
                    debug_step(step, store).unwrap();
                }
                let mut recursive_snark = rs.take().unwrap_or_else(|| {
                    RecursiveSNARK::new(&pp.pp, step, &secondary_circuit, z0, &Self::z0_secondary())
                        .expect("failed to construct initial recursive SNARK")
                });
                info!("prove_step {i}");
                recursive_snark
                    .prove_step(&pp.pp, step, &secondary_circuit)
                    .unwrap();
                *rs = Some(recursive_snark);
            };

        recursive_snark_option = if lurk_config(None, None)
            .perf
            .parallelism
            .wit_gen_vs_folding
            .is_parallel()
        {
            let cc = steps.into_iter().map(Mutex::new).collect::<Vec<_>>();

            std::thread::scope(|s| {
                s.spawn(|| {
                    // Skip the very first circuit's witness, so `prove_step` can begin immediately.
                    // That circuit's witness will not be cached and will just be computed on-demand.
                    cc.iter().skip(1).for_each(|mf| {
                        mf.lock()
                            .unwrap()
                            .cache_witness(store)
                            .expect("witness caching failed");
                    });
                });

                for (i, step) in cc.iter().enumerate() {
                    let mut step = step.lock().unwrap();
                    prove_step(i, &step, &mut recursive_snark_option);
                    step.clear_cached_witness();
                }
                recursive_snark_option
            })
        } else {
            for (i, step) in steps.iter().enumerate() {
                prove_step(i, step, &mut recursive_snark_option);
            }
            recursive_snark_option
        };

        Ok(Self::Recursive(
            Box::new(recursive_snark_option.expect("RecursiveSNARK missing")),
            num_steps,
            PhantomData,
        ))
    }

    fn compress(self, pp: &PublicParams<F>) -> Result<Self, ProofError> {
        match self {
            Self::Recursive(recursive_snark, num_steps, _phantom) => Ok(Self::Compressed(
                Box::new(CompressedSNARK::<_, SS1<F>, SS2<F>>::prove(
                    &pp.pp,
                    pp.pk(),
                    &recursive_snark,
                )?),
                num_steps,
                PhantomData,
            )),
            Self::Compressed(..) => Ok(self),
        }
    }

    fn verify(&self, pp: &Self::PublicParams, z0: &[F], zi: &[F]) -> Result<bool, Self::ErrorType> {
        let (z0_primary, zi_primary) = (z0, zi);
        let z0_secondary = Self::z0_secondary();
        let zi_secondary = &z0_secondary;

        let (zi_primary_verified, zi_secondary_verified) = match self {
            Self::Recursive(p, num_steps, _phantom) => {
                p.verify(&pp.pp, *num_steps, z0_primary, &z0_secondary)?
            }
            Self::Compressed(p, num_steps, _phantom) => {
                p.verify(pp.vk(), *num_steps, z0_primary, &z0_secondary)?
            }
        };

        Ok(zi_primary == zi_primary_verified && zi_secondary == &zi_secondary_verified)
    }
}

/// A struct for the Nova prover that operates on field elements of type `F`.
#[derive(Debug)]
pub struct NovaProver<'a, F: CurveCycleEquipped, C: Coprocessor<F>> {
    /// The number of small-step reductions performed in each recursive step.
    reduction_count: usize,
    lang: Arc<Lang<F, C>>,
    folding_mode: FoldingMode,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a> NovaProver<'a, F, C> {
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

    /// Generate a proof from a sequence of frames
    pub fn prove_from_frames(
        &self,
        pp: &PublicParams<F>,
        frames: &[Frame],
        store: &'a Store<F>,
    ) -> Result<(Proof<F, C1LEM<'a, F, C>>, Vec<F>, Vec<F>, usize), ProofError> {
        let folding_config = self
            .folding_mode()
            .folding_config(self.lang().clone(), self.reduction_count());
        let steps = C1LEM::<'a, F, C>::from_frames(frames, store, &folding_config.into());
        self.prove(pp, steps, store)
    }

    #[inline]
    /// Returns the `Lang` wrapped with `Arc` for cheap cloning
    pub fn lang(&self) -> &Arc<Lang<F, C>> {
        &self.lang
    }
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a> Prover<'a, F> for NovaProver<'a, F, C> {
    type Frame = C1LEM<'a, F, C>;
    type PublicParams = PublicParams<F>;
    type RecursiveSnark = Proof<F, C1LEM<'a, F, C>>;

    #[inline]
    fn reduction_count(&self) -> usize {
        self.reduction_count
    }

    #[inline]
    fn folding_mode(&self) -> &FoldingMode {
        &self.folding_mode
    }

    fn evaluate_and_prove(
        &self,
        pp: &Self::PublicParams,
        expr: Ptr,
        env: Ptr,
        store: &'a Store<F>,
        limit: usize,
        ch_terminal: &ChannelTerminal<Ptr>,
    ) -> Result<(Self::RecursiveSnark, Vec<F>, Vec<F>, usize), ProofError> {
        let eval_config = self.folding_mode().eval_config(self.lang());
        let frames =
            C1LEM::<'a, F, C>::build_frames(expr, env, store, limit, &eval_config, ch_terminal)?;
        self.prove_from_frames(pp, &frames, store)
    }
}
