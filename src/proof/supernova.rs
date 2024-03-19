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
use serde::{Deserialize, Serialize};
use std::{
    borrow::Cow,
    marker::PhantomData,
    ops::Index,
    sync::{mpsc, Arc},
};
use tracing::info;

use crate::{
    config::lurk_config,
    coprocessor::Coprocessor,
    dual_channel::ChannelTerminal,
    error::ProofError,
    field::LurkField,
    lang::Lang,
    lem::{interpreter::Frame, pointers::Ptr, store::Store},
    proof::{
        nova::{debug_step, CurveCycleEquipped, Dual, NovaCircuitShape, E1},
        Prover, RecursiveSNARKTrait, MAX_BUFFERED_FRAMES,
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
    let non_uniform_circuit = C1LEM::<F, C>::blank(folding_config, 0);

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
#[derive(Serialize, Deserialize, Clone)]
#[serde(bound = "")]
pub enum Proof<F: CurveCycleEquipped, S> {
    /// A proof for the intermediate steps of a recursive computation
    Recursive(Box<RecursiveSNARK<E1<F>>>, PhantomData<S>),
    /// A proof for the final step of a recursive computation
    Compressed(Box<CompressedSNARK<E1<F>, SS1<F>, SS2<F>>>, PhantomData<S>),
}

impl<F: CurveCycleEquipped, S> Proof<F, S> {
    /// Extracts the original `CompressedSNARK`
    #[inline]
    pub fn get_compressed(self) -> Option<CompressedSNARK<E1<F>, SS1<F>, SS2<F>>> {
        match_opt::match_opt!(self, Self::Compressed(proof, _) => *proof)
    }

    /// Extracts the original `RecursiveSNARK`
    #[inline]
    pub fn get_recursive(self) -> Option<RecursiveSNARK<E1<F>>> {
        match_opt::match_opt!(self, Self::Recursive(proof, _) => *proof)
    }
}

/// A struct for the Nova prover that operates on field elements of type `F`.
#[derive(Debug)]
pub struct SuperNovaProver<F: CurveCycleEquipped, C: Coprocessor<F>> {
    /// The number of small-step reductions performed in each recursive step of
    /// the primary Lurk circuit.
    reduction_count: usize,
    lang: Arc<Lang<F, C>>,
    folding_mode: FoldingMode,
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> SuperNovaProver<F, C> {
    /// Create a new SuperNovaProver with a reduction count and a `Lang`
    #[inline]
    pub fn new(reduction_count: usize, lang: Arc<Lang<F, C>>) -> Self {
        Self {
            reduction_count,
            lang,
            folding_mode: FoldingMode::NIVC,
        }
    }

    /// Generate a proof from a sequence of frames
    pub fn prove_from_frames(
        &self,
        pp: &PublicParams<F>,
        frames: &[Frame],
        store: &Arc<Store<F>>,
        init: Option<RecursiveSNARK<E1<F>>>,
    ) -> Result<(Proof<F, C1LEM<F, C>>, Vec<F>, Vec<F>, usize), ProofError> {
        let folding_config = self
            .folding_mode()
            .folding_config(self.lang().clone(), self.reduction_count());
        let steps = C1LEM::<F, C>::from_frames(frames, store, &folding_config.into());
        self.prove(pp, steps, store, init)
    }

    #[inline]
    /// Returns the `Lang` wrapped with `Arc` for cheap cloning
    pub fn lang(&self) -> &Arc<Lang<F, C>> {
        &self.lang
    }
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> RecursiveSNARKTrait<F, C1LEM<F, C>>
    for Proof<F, C1LEM<F, C>>
{
    type PublicParams = PublicParams<F>;
    type BaseRecursiveSNARK = RecursiveSNARK<E1<F>>;
    type ErrorType = SuperNovaError;

    #[tracing::instrument(skip_all, name = "supernova::prove_recursively")]
    fn prove_recursively<I: IntoIterator<Item = C1LEM<F, C>>>(
        pp: &PublicParams<F>,
        z0: &[F],
        steps: I,
        store: &Store<F>,
        init: Option<RecursiveSNARK<E1<F>>>,
    ) -> Result<Self, ProofError>
    where
        <I as IntoIterator>::IntoIter: ExactSizeIterator + Send,
    {
        let debug = false;
        let steps = steps.into_iter();

        info!("proving {} steps", steps.len());

        let mut recursive_snark_option = init;

        let prove_step = |i: usize, step: &C1LEM<F, C>, rs: &mut Option<RecursiveSNARK<E1<F>>>| {
            if debug {
                debug_step(step, store).unwrap();
            }
            let secondary_circuit = step.secondary_circuit();
            let mut recursive_snark = rs.take().unwrap_or_else(|| {
                RecursiveSNARK::new(
                    &pp.pp,
                    step,
                    step,
                    &secondary_circuit,
                    z0,
                    &Self::z0_secondary(),
                )
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
            // the sending end of the channel will block if it is at capacity
            let (step_sender, step_receiver) = mpsc::sync_channel(MAX_BUFFERED_FRAMES);

            std::thread::scope(|s| {
                s.spawn(move || {
                    for mut step in steps {
                        step.cache_witness(store).expect("witness caching failed");
                        if step_sender.send(step).is_err() {
                            // The main thread has dropped the receiver, so we can stop
                            return;
                        }
                    }
                });

                let buffered_steps = step_receiver.into_iter();

                for (i, mut step) in buffered_steps.enumerate() {
                    prove_step(i, &step, &mut recursive_snark_option);
                    step.clear_cached_witness();
                }
                recursive_snark_option
            })
        } else {
            for (i, step) in steps.enumerate() {
                prove_step(i, &step, &mut recursive_snark_option);
            }
            recursive_snark_option
        };

        Ok(Self::Recursive(
            Box::new(recursive_snark_option.expect("RecursiveSNARK missing")),
            PhantomData,
        ))
    }

    fn compress(&self, pp: &PublicParams<F>) -> Result<Cow<'_, Self>, ProofError> {
        match &self {
            Self::Recursive(recursive_snark, _phantom) => {
                let snark =
                    CompressedSNARK::<_, SS1<F>, SS2<F>>::prove(&pp.pp, pp.pk(), recursive_snark)?;
                Ok(Cow::Owned(Self::Compressed(Box::new(snark), PhantomData)))
            }
            Self::Compressed(..) => Ok(Cow::Borrowed(self)),
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

impl<F: CurveCycleEquipped, C: Coprocessor<F>> Prover<F> for SuperNovaProver<F, C> {
    type Frame = C1LEM<F, C>;
    type PublicParams = PublicParams<F>;
    type RecursiveSNARK = Proof<F, C1LEM<F, C>>;

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
        store: &Arc<Store<F>>,
        limit: usize,
        ch_terminal: &ChannelTerminal<Ptr>,
    ) -> Result<(Self::RecursiveSNARK, Vec<F>, Vec<F>, usize), ProofError> {
        let eval_config = self.folding_mode().eval_config(self.lang());
        let frames =
            C1LEM::<F, C>::build_frames(expr, env, store, limit, &eval_config, ch_terminal)?;
        self.prove_from_frames(pp, &frames, store, None)
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
    let circuit = C1LEM::<F, C>::blank(folding_config, 0);
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
