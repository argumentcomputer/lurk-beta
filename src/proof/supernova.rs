#![allow(non_snake_case)]

use abomonation::Abomonation;
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::{Field, PrimeField};
use nova::{
    supernova::{
        self, error::SuperNovaError, AuxParams, CircuitDigests, NonUniformCircuit, RecursiveSNARK,
    },
    traits::{
        circuit_supernova::{StepCircuit as SuperStepCircuit, TrivialSecondaryCircuit},
        Group,
    },
};
use serde::{Deserialize, Serialize};
use std::{marker::PhantomData, ops::Index, sync::Arc};
use tracing::{debug, info};

use crate::{
    circuit::MultiFrame,
    coprocessor::Coprocessor,
    error::ProofError,
    eval::{lang::Lang, Meta},
    field::LurkField,
    proof::{
        nova::{CurveCycleEquipped, NovaCircuitShape, G1, G2},
        {FrameLike, MultiFrameTrait, Provable, Prover},
    },
};

/// Type alias for a Trivial Test Circuit with G2 scalar field elements.
pub type C2<F> = TrivialSecondaryCircuit<<G2<F> as Group>::Scalar>;

/// Type alias for SuperNova Aux Parameters with the curve cycle types defined above.
pub type SuperNovaAuxParams<F> = AuxParams<G1<F>, G2<F>>;

/// Type alias for SuperNova Public Parameters with the curve cycle types defined above.
pub type SuperNovaPublicParams<F, C1> = supernova::PublicParams<G1<F>, G2<F>, C1, C2<F>>;

/// A struct that contains public parameters for the SuperNova proving system.
pub struct PublicParams<F: CurveCycleEquipped, SC: SuperStepCircuit<F>>
where
    // technical bounds that would disappear once associated_type_bounds stabilizes
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    /// Public params for SuperNova.
    pub pp: SuperNovaPublicParams<F, SC>,
    // SuperNova does not yet have a `CompressedSNARK`.
    // pk: ProverKey<G1<F>, G2<F>, SC, C2<F>, SS1<F>, SS2<F>>,
    // vk: VerifierKey<G1<F>, G2<F>, SC, C2<F>, SS1<F>, SS2<F>>,
}

impl<F: CurveCycleEquipped, SC: SuperStepCircuit<F>> Index<usize> for PublicParams<F, SC>
where
    // technical bounds that would disappear once associated_type_bounds stabilizes
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    type Output = NovaCircuitShape<F>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.pp[index]
    }
}

impl<F: CurveCycleEquipped, SC: SuperStepCircuit<F>> PublicParams<F, SC>
where
    // technical bounds that would disappear once associated_type_bounds stabilizes
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    /// return the digest
    pub fn digest(&self) -> F {
        self.pp.digest()
    }
}

/// Generates the running claim params for the SuperNova proving system.
pub fn public_params<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C> + SuperStepCircuit<F> + NonUniformCircuit<G1<F>, G2<F>, M, C2<F>>,
>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
) -> PublicParams<F, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let folding_config = Arc::new(FoldingConfig::new_nivc(lang, rc));
    let non_uniform_circuit = M::blank(folding_config, Meta::Lurk, 0);
    let pp = SuperNovaPublicParams::<F, M>::new(&non_uniform_circuit);
    PublicParams { pp }
}

/// An enum representing the two types of proofs that can be generated and verified.
#[derive(Serialize, Deserialize)]
pub enum Proof<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// A proof for the intermediate steps of a recursive computation
    Recursive(Box<RecursiveSNARK<G1<F>, G2<F>>>),
    /// A proof for the final step of a recursive computation
    // Compressed(Box<CompressedSNARK<G1<F>, G2<F>, C1<'a, F, C>, C2<F>, SS1<F>, SS2<F>>>),
    Compressed(PhantomData<&'a (C, M)>),
}

impl<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F>,
        M: MultiFrameTrait<'a, F, C> + SuperStepCircuit<F> + NonUniformCircuit<G1<F>, G2<F>, M, C2<F>>,
    > Proof<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    /// Proves the computation recursively, generating a recursive SNARK proof.
    #[tracing::instrument(skip_all, name = "supernova::prove_recursively")]
    pub fn prove_recursively(
        pp: &PublicParams<F, M>,
        _store: &M::Store,
        nivc_steps: &[M],
        z0: Vec<F>,
    ) -> Result<(Self, usize), ProofError> {
        // Is this assertion strictly necessary?
        assert!(!nivc_steps.is_empty());

        let mut recursive_snark_option: Option<RecursiveSNARK<G1<F>, G2<F>>> = None;

        let z0_primary = z0;
        let z0_secondary = Self::z0_secondary();

        let mut last_circuit_index = 0;

        for (i, step) in nivc_steps.iter().enumerate() {
            info!("prove_recursively, step {i}");
            let augmented_circuit_index = step.circuit_index();
            let program_counter = F::from(augmented_circuit_index as u64);

            let mut recursive_snark = recursive_snark_option.clone().unwrap_or_else(|| {
                info!("iter_base_step {i}");
                RecursiveSNARK::iter_base_step(
                    &pp.pp,
                    augmented_circuit_index,
                    step,
                    &step.secondary_circuit(),
                    Some(program_counter),
                    augmented_circuit_index,
                    step.num_circuits(),
                    &z0_primary,
                    &z0_secondary,
                )
                .unwrap()
            });

            info!("prove_step {i}");

            recursive_snark
                .prove_step(
                    &pp.pp,
                    augmented_circuit_index,
                    step,
                    &step.secondary_circuit(),
                    &z0_primary,
                    &z0_secondary,
                )
                .unwrap();

            recursive_snark_option = Some(recursive_snark);

            last_circuit_index = augmented_circuit_index;
        }

        // This probably should be made unnecessary.
        Ok((
            Self::Recursive(Box::new(
                recursive_snark_option.expect("RecursiveSNARK missing"),
            )),
            last_circuit_index,
        ))
    }

    /// Verifies the proof given the claim, which (for now), contains the public parameters.
    pub fn verify(
        &self,
        pp: &PublicParams<F, M>,
        circuit_index: usize,
        _num_steps: usize,
        z0: &[F],
        zi: &[F],
    ) -> Result<bool, SuperNovaError> {
        let (z0_primary, _zi_primary) = (z0, zi);
        let z0_secondary = Self::z0_secondary();

        match self {
            Self::Recursive(p) => p.verify(&pp.pp, circuit_index, z0_primary, &z0_secondary),
            Self::Compressed(_) => unimplemented!(),
        }?;
        Ok(true)
    }

    fn z0_secondary() -> Vec<<F::G2 as Group>::Scalar> {
        vec![<G2<F> as Group>::Scalar::ZERO]
    }
}

/// A struct for the Nova prover that operates on field elements of type `F`.
#[derive(Debug)]
pub struct SuperNovaProver<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
> {
    // `reduction_count` specifies the number of small-step reductions are performed in each recursive step of the primary Lurk circuit.
    reduction_count: usize,
    lang: Lang<F, C>,
    _phantom: PhantomData<&'a M>,
}

impl<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F>,
        M: MultiFrameTrait<'a, F, C> + SuperStepCircuit<F>,
    > Prover<'a, F, C, M> for SuperNovaProver<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    type PublicParams = PublicParams<F, M>;
    fn new(reduction_count: usize, lang: Lang<F, C>) -> Self {
        SuperNovaProver::<'a, F, C, M> {
            reduction_count,
            lang,
            _phantom: PhantomData,
        }
    }
    fn reduction_count(&self) -> usize {
        self.reduction_count
    }

    fn lang(&self) -> &Lang<F, C> {
        &self.lang
    }
}

impl<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F>,
        M: MultiFrameTrait<'a, F, C> + SuperStepCircuit<F> + NonUniformCircuit<G1<F>, G2<F>, M, C2<F>>,
    > SuperNovaProver<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// Proves the computation given the public parameters, frames, and store.
    pub fn prove(
        &'a self,
        pp: &PublicParams<F, M>,
        frames: &[M::EvalFrame],
        store: &'a M::Store,
        lang: Arc<Lang<F, C>>,
    ) -> Result<(Proof<'a, F, C, M>, Vec<F>, Vec<F>, usize, usize), ProofError> {
        let z0 = M::io_to_scalar_vector(store, frames[0].input()).map_err(|e| e.into())?;
        let zi =
            M::io_to_scalar_vector(store, frames.last().unwrap().output()).map_err(|e| e.into())?;
        let folding_config = Arc::new(FoldingConfig::new_nivc(lang, self.reduction_count));

        let nivc_steps = M::from_frames(self.reduction_count(), frames, store, folding_config);

        let num_steps = nivc_steps.len();
        let (proof, last_running_claim) =
            Proof::prove_recursively(pp, store, &nivc_steps, z0.clone())?;

        Ok((proof, z0, zi, num_steps, last_running_claim))
    }

    /// Evaluates and proves the computation given the public parameters, expression, environment, and store.
    pub fn evaluate_and_prove(
        &'a self,
        pp: &PublicParams<F, M>,
        expr: M::Ptr,
        env: M::Ptr,
        store: &'a M::Store,
        limit: usize,
        lang: Arc<Lang<F, C>>,
    ) -> Result<(Proof<'a, F, C, M>, Vec<F>, Vec<F>, usize, usize), ProofError> {
        let frames = M::get_evaluation_frames(
            |count| self.needs_frame_padding(count),
            expr,
            env,
            store,
            limit,
            &lang,
        )?;
        info!("got {} evaluation frames", frames.len());
        self.prove(pp, &frames, store, lang)
    }
}

#[derive(Clone, Debug)]
/// Folding configuration specifies `Lang` and can be either `IVC` or `NIVC`.
// NOTE: This is somewhat trivial now, but will likely become more elaborate as NIVC configuration becomes more flexible.
pub enum FoldingConfig<F: LurkField, C: Coprocessor<F>> {
    // TODO: maybe (lang, reduction_count) should be a common struct.
    /// IVC: a single circuit implementing the `Lang`'s reduction will be used for every folding step
    IVC(Arc<Lang<F, C>>, usize),
    /// NIVC: each folding step will use one of a fixed set of circuits which together implement the `Lang`'s reduction.
    NIVC(Arc<Lang<F, C>>, usize),
}

impl<F: LurkField, C: Coprocessor<F>> FoldingConfig<F, C> {
    /// Create a new IVC config for `lang`.
    pub fn new_ivc(lang: Arc<Lang<F, C>>, reduction_count: usize) -> Self {
        Self::IVC(lang, reduction_count)
    }

    /// Create a new NIVC config for `lang`.
    pub fn new_nivc(lang: Arc<Lang<F, C>>, reduction_count: usize) -> Self {
        Self::NIVC(lang, reduction_count)
    }

    /// Return the circuit index assigned in this `FoldingConfig` to circuits tagged with this `meta`.
    pub fn circuit_index(&self, meta: &Meta<F>) -> usize {
        match self {
            Self::IVC(_, _) => 0,
            Self::NIVC(lang, _) => match meta {
                Meta::Lurk => 0,
                Meta::Coprocessor(z_ptr) => lang.get_index(z_ptr).unwrap() + 1,
            },
        }
    }

    /// Return the total number of NIVC circuits potentially required when folding programs described by this `FoldingConfig`.
    pub fn num_circuits(&self) -> usize {
        match self {
            Self::IVC(_, _) => 1,
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

impl<'a, F: LurkField, C: Coprocessor<F>> MultiFrame<'a, F, C> {
    /// Return the circuit index assigned to this `MultiFrame`'s inner computation, as labeled by its `Meta`, and determined by its `FoldingConfig`.
    pub fn circuit_index(&self) -> usize {
        debug!(
            "getting circuit_index for {:?}: {}",
            &self.meta,
            self.folding_config.circuit_index(&self.meta)
        );
        self.folding_config.circuit_index(&self.meta)
    }
}

/// Implement `supernova::StepCircuit` for `MultiFrame`. This is the universal Lurk circuit that will be included as the
/// first circuit (index 0) of every Lurk NIVC circuit set.
impl<F: LurkField, C: Coprocessor<F>> SuperStepCircuit<F> for MultiFrame<'_, F, C> {
    fn arity(&self) -> usize {
        self.public_input_size() / 2
    }

    fn circuit_index(&self) -> usize {
        self.circuit_index()
    }

    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        pc: std::option::Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(std::option::Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if let Some(pc) = pc {
            if pc.get_value() == Some(F::ZERO) {
                debug!("synthesizing StepCircuit for Lurk");
            } else {
                debug!(
                    "synthesizing StepCircuit for Coprocessor with pc: {:?}",
                    pc.get_value()
                );
            }
        }
        let output = <MultiFrame<'_, F, C> as nova::traits::circuit::StepCircuit<F>>::synthesize(
            self, cs, z,
        )?;

        let next_pc = AllocatedNum::alloc_infallible(&mut cs.namespace(|| "next_pc"), || {
            self.next_pc
                // This is missing in the case of a final `MultiFrame`. The Lurk circuit is defined to always have index
                // 0, so it is a good default in this case.
                .map_or(F::ZERO, |x| F::from(x as u64))
        });
        debug!("synthesizing with next_pc: {:?}", next_pc.get_value());

        Ok((Some(next_pc), output))
    }
}

/// All steps of an NIVC computation
impl<'a, F, C1> NonUniformCircuit<G1<F>, G2<F>, MultiFrame<'a, F, C1>, C2<F>>
    for MultiFrame<'a, F, C1>
where
    F: CurveCycleEquipped + LurkField,
    C1: Coprocessor<F>,
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    fn num_circuits(&self) -> usize {
        assert!(self.meta.is_lurk());
        self.folding_config.lang().coprocessor_count() + 1
    }

    fn primary_circuit(&self, circuit_index: usize) -> Self {
        debug!(
            "getting primary_circuit for index {circuit_index} and Meta: {:?}",
            self.meta
        );
        if circuit_index == 0 {
            debug!("using Lurk circuit");
            return self.clone();
        };
        if let Some(z_ptr) = self
            .folding_config
            .lang()
            .get_coprocessor_z_ptr(circuit_index - 1)
        {
            let meta = Meta::Coprocessor(*z_ptr);
            debug!(
                "using coprocessor {} with meta: {:?}",
                circuit_index - 1,
                meta
            );
            Self::blank(self.folding_config.clone(), meta)
        } else {
            debug!("unsupported primary circuit index: {circuit_index}");
            panic!("unsupported primary circuit index")
        }
    }

    fn secondary_circuit(&self) -> C2<F> {
        Default::default()
    }
}

/// Computes a cache key of a supernova primary circuit. The point is that if a circuit
/// changes in any way but has the same `rc`/`Lang`, then we still want the
/// public params to stay in sync with the changes.
///
/// Note: For now, we use ad-hoc circuit cache keys.
/// See: [crate::public_parameters::instance]
pub fn circuit_cache_key<F: CurveCycleEquipped, C: Coprocessor<F>>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
    circuit_index: usize,
) -> F
where
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    let folding_config = Arc::new(FoldingConfig::new_nivc(lang, 2));
    let circuit = MultiFrame::blank(folding_config, Meta::Lurk);
    let num_circuits = circuit.num_circuits();
    let circuit = circuit.primary_circuit(circuit_index);
    F::from(rc as u64) * supernova::circuit_digest::<F::G1, F::G2, _>(&circuit, num_circuits)
}

/// Collects all the cache keys of supernova instance. We need all of them to compute
/// a cache key for the digest of the [PublicParams] of the supernova instance.
pub fn circuit_cache_keys<F: CurveCycleEquipped, C: Coprocessor<F>>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
) -> CircuitDigests<G1<F>>
where
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    let num_circuits = lang.coprocessor_count() + 1;
    let digests = (0..num_circuits)
        .map(|circuit_index| circuit_cache_key(rc, lang.clone(), circuit_index))
        .collect::<Vec<_>>();
    CircuitDigests::new(digests)
}
