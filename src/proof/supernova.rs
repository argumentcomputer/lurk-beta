use nova::{
    supernova::{
        self,
        error::SuperNovaError,
        snark::{CompressedSNARK, ProverKey, VerifierKey},
        AuxParams, CircuitDigests, NonUniformCircuit, RecursiveSNARK, TrivialSecondaryCircuit,
    },
    traits::{
        snark::{BatchedRelaxedR1CSSNARKTrait, RelaxedR1CSSNARKTrait},
        Dual as DualEng,
    },
};
use once_cell::sync::OnceCell;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use std::{
    marker::PhantomData,
    ops::Index,
    sync::{Arc, Mutex},
};
use tracing::info;

use crate::{
    config::lurk_config,
    coprocessor::Coprocessor,
    error::ProofError,
    eval::lang::Lang,
    field::LurkField,
    lem::{interpreter::Frame, pointers::Ptr, store::Store},
    proof::{
        nova::{CurveCycleEquipped, Dual, NovaCircuitShape, E1},
        Prover, RecursiveSNARKTrait,
    },
};

use super::{nova::C1LEM, FoldingMode};

/// Type alias for a Trivial Test Circuit with G2 scalar field elements.
pub type C2<F> = TrivialSecondaryCircuit<Dual<F>>;

/// Type alias for SuperNova Aux Parameters with the curve cycle types defined above.
pub type SuperNovaAuxParams<F> = AuxParams<E1<F>>;

/// Type alias for SuperNova Public Parameters with the curve cycle types defined above.
pub type SuperNovaPublicParams<F> = supernova::PublicParams<E1<F>>;

/// A struct that contains public parameters for the SuperNova proving system.
pub struct PublicParams<F: CurveCycleEquipped> {
    /// Public params for SuperNova.
    pub pp: SuperNovaPublicParams<F>,
    /// Prover key and Verifier key for SuperNova
    // TODO: mark as #[serde(skip)] when serializing
    pub pk_and_vk: OnceCell<(
        ProverKey<E1<F>, SS1<F>, SS2<F>>,
        VerifierKey<E1<F>, SS1<F>, SS2<F>>,
    )>,
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

impl<F: CurveCycleEquipped> From<SuperNovaPublicParams<F>> for PublicParams<F> {
    fn from(pp: SuperNovaPublicParams<F>) -> PublicParams<F> {
        PublicParams {
            pp,
            pk_and_vk: OnceCell::new(),
        }
    }
}

impl<F: CurveCycleEquipped> Index<usize> for PublicParams<F> {
    type Output = NovaCircuitShape<F>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.pp[index]
    }
}

impl<F: CurveCycleEquipped> PublicParams<F> {
    /// return the digest
    pub fn digest(&self) -> F {
        self.pp.digest()
    }
}

/// Type alias for the Evaluation Engine using G1 group elements.
pub type EE1<F> = <F as CurveCycleEquipped>::EE1;
/// Type alias for the Evaluation Engine using G2 group elements.
pub type EE2<F> = <F as CurveCycleEquipped>::EE2;

/// Type alias for the Relaxed R1CS Spartan SNARK using G1 group elements, EE1.
// NOTE: this is not a SNARK that uses computational commitments,
// that SNARK would be found at nova::spartan::ppsnark::RelaxedR1CSSNARK,
pub type SS1<F> = nova::spartan::batched::BatchedRelaxedR1CSSNARK<E1<F>, EE1<F>>;
/// Type alias for the Relaxed R1CS Spartan SNARK using G2 group elements, EE2.
// NOTE: this is not a SNARK that uses computational commitments,
// that SNARK would be found at nova::spartan::ppsnark::RelaxedR1CSSNARK,
pub type SS2<F> = nova::spartan::snark::RelaxedR1CSSNARK<DualEng<E1<F>>, EE2<F>>;

/// Generates the running claim params for the SuperNova proving system.
pub fn public_params<F: CurveCycleEquipped, C: Coprocessor<F>>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
) -> PublicParams<F> {
    let folding_config = Arc::new(FoldingConfig::new_nivc(lang, rc));
    let non_uniform_circuit = C1LEM::<'_, F, C>::blank(folding_config, 0);

    // grab hints for the compressed SNARK variants we will use this with
    let commitment_size_hint1 = <SS1<F> as BatchedRelaxedR1CSSNARKTrait<E1<F>>>::ck_floor();
    let commitment_size_hint2 = <SS2<F> as RelaxedR1CSSNARKTrait<DualEng<E1<F>>>>::ck_floor();

    let pp = SuperNovaPublicParams::<F>::setup(
        &non_uniform_circuit,
        &*commitment_size_hint1,
        &*commitment_size_hint2,
    );
    PublicParams {
        pp,
        pk_and_vk: OnceCell::new(),
    }
}

/// An enum representing the two types of proofs that can be generated and verified.
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub enum Proof<F: CurveCycleEquipped, S> {
    /// A proof for the intermediate steps of a recursive computation
    Recursive(Box<RecursiveSNARK<E1<F>>>, PhantomData<S>),
    /// A proof for the final step of a recursive computation
    Compressed(Box<CompressedSNARK<E1<F>, SS1<F>, SS2<F>>>, PhantomData<S>),
}

/// A struct for the Nova prover that operates on field elements of type `F`.
#[derive(Debug)]
pub struct SuperNovaProver<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a> {
    /// The number of small-step reductions performed in each recursive step of
    /// the primary Lurk circuit.
    reduction_count: usize,
    lang: Arc<Lang<F, C>>,
    folding_mode: FoldingMode,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a> SuperNovaProver<'a, F, C> {
    /// Create a new SuperNovaProver with a reduction count and a `Lang`
    #[inline]
    pub fn new(reduction_count: usize, lang: Arc<Lang<F, C>>) -> Self {
        Self {
            reduction_count,
            lang,
            folding_mode: FoldingMode::NIVC,
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
    fn lang(&self) -> &Arc<Lang<F, C>> {
        &self.lang
    }
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>> RecursiveSNARKTrait<F, C1LEM<'a, F, C>>
    for Proof<F, C1LEM<'a, F, C>>
{
    type PublicParams = PublicParams<F>;

    type ErrorType = SuperNovaError;

    #[tracing::instrument(skip_all, name = "supernova::prove_recursively")]
    fn prove_recursively(
        pp: &PublicParams<F>,
        z0: &[F],
        steps: Vec<C1LEM<'a, F, C>>,
        store: &Store<F>,
    ) -> Result<Self, ProofError> {
        let mut recursive_snark_option: Option<RecursiveSNARK<E1<F>>> = None;

        let z0_primary = z0;
        let z0_secondary = Self::z0_secondary();

        let mut prove_step = |i: usize, step: &C1LEM<'a, F, C>| {
            info!("prove_recursively, step {i}");

            let secondary_circuit = step.secondary_circuit();

            let mut recursive_snark = recursive_snark_option.clone().unwrap_or_else(|| {
                info!("RecursiveSnark::new {i}");
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

            info!("prove_step {i}");

            recursive_snark
                .prove_step(&pp.pp, step, &secondary_circuit)
                .unwrap();

            recursive_snark_option = Some(recursive_snark);
        };

        if lurk_config(None, None)
            .perf
            .parallelism
            .recursive_steps
            .is_parallel()
        {
            let cc = steps
                .into_iter()
                .map(|mf| (mf.program_counter() == 0, Mutex::new(mf)))
                .collect::<Vec<_>>();

            crossbeam::thread::scope(|s| {
                s.spawn(|_| {
                    // Skip the very first circuit's witness, so `prove_step` can begin immediately.
                    // That circuit's witness will not be cached and will just be computed on-demand.

                    // There are many MultiFrames with PC = 0, each with several inner frames and heavy internal
                    // paralellism for witness generation. So we do it like on Nova's pipeline.
                    cc.iter()
                        .skip(1)
                        .filter(|(is_zero_pc, _)| *is_zero_pc)
                        .for_each(|(_, mf)| {
                            mf.lock()
                                .unwrap()
                                .cache_witness(store)
                                .expect("witness caching failed");
                        });

                    // There shouldn't be as many MultiFrames with PC != 0 and they only have one inner frame, each with
                    // poor internal parallelism for witness generation, so we can generate their witnesses in parallel.
                    // This is mimicking the behavior we had in the Nova pipeline before #941 so...
                    // TODO: once we have robust benchmarking for NIVC, we should test whether merging this loop with
                    // the non-parallel one above (and getting rid of the filters) is better
                    cc.par_iter()
                        .skip(1)
                        .filter(|(is_zero_pc, _)| !*is_zero_pc)
                        .for_each(|(_, mf)| {
                            mf.lock()
                                .unwrap()
                                .cache_witness(store)
                                .expect("witness caching failed");
                        });
                });

                for (i, (_, step)) in cc.iter().enumerate() {
                    let mut step = step.lock().unwrap();
                    prove_step(i, &step);
                    step.clear_cached_witness();
                }
            })
            .unwrap()
        } else {
            for (i, step) in steps.iter().enumerate() {
                prove_step(i, step);
            }
        }

        // This probably should be made unnecessary.
        Ok(Self::Recursive(
            Box::new(recursive_snark_option.expect("RecursiveSNARK missing")),
            PhantomData,
        ))
    }

    fn compress(self, pp: &PublicParams<F>) -> Result<Self, ProofError> {
        match &self {
            Self::Recursive(recursive_snark, _phantom) => {
                let snark =
                    CompressedSNARK::<_, SS1<F>, SS2<F>>::prove(&pp.pp, pp.pk(), recursive_snark)?;
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
            Self::Recursive(p, _phantom) => p.verify(&pp.pp, z0_primary, &z0_secondary)?,
            Self::Compressed(p, _phantom) => {
                p.verify(&pp.pp, pp.vk(), z0_primary, &z0_secondary)?
            }
        };

        Ok(zi_primary == zi_primary_verified && zi_secondary == &zi_secondary_verified)
    }
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>> Prover<'a, F, C1LEM<'a, F, C>>
    for SuperNovaProver<'a, F, C>
{
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
    ) -> Result<(Self::RecursiveSnark, Vec<F>, Vec<F>, usize), ProofError> {
        let eval_config = self.folding_mode().eval_config(self.lang());
        let frames = C1LEM::<'a, F, C>::build_frames(expr, env, store, limit, &eval_config)?;
        self.prove_from_frames(pp, &frames, store)
    }
}

#[derive(Clone, Debug)]
/// Folding configuration specifies the `Lang`, the reduction count and the
/// folding mode for a proving setup.
///
/// NOTE: This is somewhat trivial now, but will likely become more elaborate as
/// NIVC configuration becomes more flexible.
pub enum FoldingConfig<F: LurkField, C: Coprocessor<F>> {
    // TODO: maybe (lang, reduction_count) should be a common struct.
    /// IVC: a single circuit implementing the `Lang`'s reduction will be used
    /// for every folding step
    IVC(Arc<Lang<F, C>>, usize),
    /// NIVC: each folding step will use one of a fixed set of circuits which
    /// together implement the `Lang`'s reduction.
    NIVC(Arc<Lang<F, C>>, usize),
}

impl<F: LurkField, C: Coprocessor<F>> FoldingConfig<F, C> {
    /// Create a new IVC config for `lang`.
    #[inline]
    pub fn new_ivc(lang: Arc<Lang<F, C>>, reduction_count: usize) -> Self {
        Self::IVC(lang, reduction_count)
    }

    /// Create a new NIVC config for `lang`.
    #[inline]
    pub fn new_nivc(lang: Arc<Lang<F, C>>, reduction_count: usize) -> Self {
        Self::NIVC(lang, reduction_count)
    }

    /// Return the total number of NIVC circuits potentially required when folding
    /// programs described by this `FoldingConfig`.
    pub fn num_circuits(&self) -> usize {
        match self {
            Self::IVC(..) => 1,
            Self::NIVC(lang, _) => 1 + lang.coprocessor_count(),
        }
    }

    /// Return a reference to the contained `Lang`.
    pub fn lang(&self) -> &Arc<Lang<F, C>> {
        match self {
            Self::IVC(lang, _) | Self::NIVC(lang, _) => lang,
        }
    }
    /// Return contained reduction count.
    pub fn reduction_count(&self) -> usize {
        match self {
            Self::IVC(_, rc) | Self::NIVC(_, rc) => *rc,
        }
    }
}

/// Computes a cache key of a supernova primary circuit. The point is that if a
/// circuit changes in any way but has the same `rc`/`Lang`, then we still want
/// the public params to stay in sync with the changes.
///
/// Note: For now, we use ad-hoc circuit cache keys.
/// See: [crate::public_parameters::instance]
pub fn circuit_cache_key<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
    circuit_index: usize,
) -> F {
    let folding_config = Arc::new(FoldingConfig::new_nivc(lang, 2));
    let circuit = C1LEM::<'a, F, C>::blank(folding_config, 0);
    let num_circuits = circuit.num_circuits();
    let circuit = circuit.primary_circuit(circuit_index);
    F::from(rc as u64) * supernova::circuit_digest::<F::E1, _>(&circuit, num_circuits)
}

/// Collects all the cache keys of supernova instance. We need all of them to compute
/// a cache key for the digest of the [PublicParams] of the supernova instance.
pub fn circuit_cache_keys<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    rc: usize,
    lang: &Arc<Lang<F, C>>,
) -> CircuitDigests<E1<F>> {
    let num_circuits = lang.coprocessor_count() + 1;
    let digests = (0..num_circuits)
        .map(|circuit_index| circuit_cache_key::<F, C>(rc, lang.clone(), circuit_index))
        .collect();
    CircuitDigests::new(digests)
}
