#![allow(non_snake_case)]
use std::marker::PhantomData;
use std::ops::Index;

use abomonation::Abomonation;
use tracing::{debug, info};

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use nova::{
    self,
    supernova::{self, error::SuperNovaError, CircuitDigests, NonUniformCircuit, RecursiveSNARK},
    traits::{
        circuit_supernova::{StepCircuit, TrivialSecondaryCircuit},
        Group,
    },
};

use ff::{Field, PrimeField};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::circuit::MultiFrame;

use crate::coprocessor::Coprocessor;

use crate::error::ProofError;
use crate::eval::{lang::Lang, Frame, Meta, Witness, IO};
use crate::field::LurkField;
use crate::proof::nova::{CurveCycleEquipped, G1, G2};
use crate::proof::{Provable, Prover, PublicParameters};
use crate::ptr::Ptr;
use crate::store::Store;

use super::nova::NovaCircuitShape;

/// Type alias for a NIVCStep with S1 field elements.
/// This uses the <<F as CurveCycleEquipped>::G1 as Group>::Scalar type for the G1 scalar field elements
/// to reflect it this should not be used outside the Nova context
pub type C1<'a, F, C> = NIVCStep<'a, F, C>;
/// Type alias for a Trivial Test Circuit with G2 scalar field elements.
pub type C2<F> = TrivialSecondaryCircuit<<G2<F> as Group>::Scalar>;

/// Type alias for SuperNova Aux Parameters with the curve cycle types defined above.
pub type SuperNovaAuxParams<F> = supernova::AuxParams<G1<F>, G2<F>>;

/// Type alias for SuperNova Public Parameters with the curve cycle types defined above.
pub type SuperNovaPublicParams<F, C1> = supernova::PublicParams<G1<F>, G2<F>, C1, C2<F>>;

/// A struct that contains public parameters for the SuperNova proving system.
pub struct PublicParams<F: CurveCycleEquipped, SC: StepCircuit<F>>
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

impl<F: CurveCycleEquipped, SC: StepCircuit<F>> Index<usize> for PublicParams<F, SC>
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

impl<F: CurveCycleEquipped, SC: StepCircuit<F>> PublicParams<F, SC>
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
pub fn public_params<'a, F: CurveCycleEquipped, C: Coprocessor<F>>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
) -> PublicParams<F, C1<'a, F, C>>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let folding_config = Arc::new(FoldingConfig::new_nivc(lang, rc));
    let non_uniform_circuit = NIVCStep::blank(folding_config, Meta::Lurk);
    let pp = SuperNovaPublicParams::<F, C1<'a, F, C>>::new(&non_uniform_circuit);
    PublicParams { pp }
}

/// An enum representing the two types of proofs that can be generated and verified.
#[derive(Serialize, Deserialize)]
pub enum Proof<F: CurveCycleEquipped, C: Coprocessor<F>>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// A proof for the intermediate steps of a recursive computation
    Recursive(Box<RecursiveSNARK<G1<F>, G2<F>>>),
    /// A proof for the final step of a recursive computation
    // Compressed(Box<CompressedSNARK<G1<F>, G2<F>, C1<'a, F, C>, C2<F>, SS1<F>, SS2<F>>>),
    Compressed(PhantomData<C>),
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> Proof<F, C>
where
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    /// Proves the computation recursively, generating a recursive SNARK proof.
    #[tracing::instrument(skip_all, name = "supernova::prove_recursively")]
    pub fn prove_recursively<'a>(
        pp: &PublicParams<F, C1<'a, F, C>>,
        _store: &Store<F>,
        nivc_steps: &NIVCSteps<'a, G1<F>, C>,
        z0: Vec<F>,
    ) -> Result<(Self, usize), ProofError> {
        // Is this assertion strictly necessary?
        assert!(nivc_steps.num_steps() != 0);

        let mut recursive_snark_option: Option<RecursiveSNARK<G1<F>, G2<F>>> = None;

        let z0_primary = z0;
        let z0_secondary = Self::z0_secondary();

        let mut last_circuit_index = 0;

        for (i, step) in nivc_steps.steps.iter().enumerate() {
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
        pp: &PublicParams<F, C1<'_, F, C>>,
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

// /// Generates the public parameters for the Nova proving system.
// pub fn public_params<'a, F: CurveCycleEquipped, C: Coprocessor<F>>(
//     num_iters_per_step: usize,
//     lang: Arc<Lang<F, C>>,
// ) -> PublicParams<'a, F, C>
// where
//     <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
//     <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
// {
//     let (circuit_primary, circuit_secondary) = C1::circuits(num_iters_per_step, lang);

//     let commitment_size_hint1 = <SS1<F> as RelaxedR1CSSNARKTrait<G1<F>>>::commitment_key_floor();
//     let commitment_size_hint2 = <SS2<F> as RelaxedR1CSSNARKTrait<G2<F>>>::commitment_key_floor();

//     let pp = nova::PublicParams::setup(
//         &circuit_primary,
//         &circuit_secondary,
//         Some(commitment_size_hint1),
//         Some(commitment_size_hint2),
//     );
//     let (pk, vk) = CompressedSNARK::setup(&pp).unwrap();
//     PublicParams { pp, pk, vk }
// }

/// A struct for the Nova prover that operates on field elements of type `F`.
#[derive(Debug)]
pub struct SuperNovaProver<F: CurveCycleEquipped, C: Coprocessor<F>> {
    // `reduction_count` specifies the number of small-step reductions are performed in each recursive step of the primary Lurk circuit.
    reduction_count: usize,
    lang: Lang<F, C>,
}

impl<F: CurveCycleEquipped, C1: StepCircuit<F>> PublicParameters for PublicParams<F, C1>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a> Prover<'a, F, C, MultiFrame<'a, F, C>>
    for SuperNovaProver<F, C>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    type PublicParams = PublicParams<F, C1<'a, F, C>>;
    fn new(reduction_count: usize, lang: Lang<F, C>) -> Self {
        SuperNovaProver::<F, C> {
            reduction_count,
            lang,
        }
    }
    fn reduction_count(&self) -> usize {
        self.reduction_count
    }

    fn lang(&self) -> &Lang<F, C> {
        &self.lang
    }
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> SuperNovaProver<F, C>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// Proves the computation given the public parameters, frames, and store.
    pub fn prove<'a>(
        &'a self,
        pp: &PublicParams<F, C1<'a, F, C>>,
        frames: &[Frame<IO<F>, Witness<F>, F, C>],
        store: &'a mut Store<F>,
        lang: Arc<Lang<F, C>>,
    ) -> Result<(Proof<F, C>, Vec<F>, Vec<F>, usize, usize), ProofError> {
        let z0 = frames[0].input.to_vector(store)?;
        let zi = frames.last().unwrap().output.to_vector(store)?;
        let folding_config = Arc::new(FoldingConfig::new_nivc(lang, self.reduction_count));

        let nivc_steps =
            NIVCSteps::from_frames(self.reduction_count(), frames, store, folding_config);

        let num_steps = nivc_steps.num_steps();
        let (proof, last_running_claim) =
            Proof::prove_recursively(pp, store, &nivc_steps, z0.clone())?;

        Ok((proof, z0, zi, num_steps, last_running_claim))
    }

    /// Evaluates and proves the computation given the public parameters, expression, environment, and store.
    pub fn evaluate_and_prove<'a>(
        &'a self,
        pp: &PublicParams<F, C1<'a, F, C>>,
        expr: Ptr<F>,
        env: Ptr<F>,
        store: &'a mut Store<F>,
        limit: usize,
        lang: Arc<Lang<F, C>>,
    ) -> Result<(Proof<F, C>, Vec<F>, Vec<F>, usize, usize), ProofError> {
        let frames = self.get_evaluation_frames(expr, env, store, limit, lang.clone())?;
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

#[derive(Clone, Debug)]
/// One step of an NIVC computation
pub struct NIVCStep<'a, F: LurkField, C: Coprocessor<F>> {
    multiframe: MultiFrame<'a, F, C>,
    next: Option<MultiFrame<'a, F, C>>,
    _p: PhantomData<F>,
}

impl<'a, 'b, F: LurkField, C: Coprocessor<F>> NIVCStep<'a, F, C>
where
    'b: 'a,
{
    fn new(multiframe: MultiFrame<'b, F, C>) -> Self {
        Self {
            multiframe,
            next: None,
            _p: Default::default(),
        }
    }

    fn blank(folding_config: Arc<FoldingConfig<F, C>>, meta: Meta<F>) -> Self {
        let multiframe = MultiFrame::blank(folding_config, meta);
        Self::new(multiframe)
    }

    fn lang(&self) -> Arc<Lang<F, C>> {
        self.multiframe.folding_config.lang().clone()
    }

    fn meta(&self) -> Meta<F> {
        self.multiframe.meta
    }

    fn folding_config(&self) -> Arc<FoldingConfig<F, C>> {
        self.multiframe.folding_config.clone()
    }
}

/// Implement `supernova::StepCircuit` for `MultiFrame`. This is the universal Lurk circuit that will be included as the
/// first circuit (index 0) of every Lurk NIVC circuit set.
impl<F: LurkField, C: Coprocessor<F>> StepCircuit<F> for NIVCStep<'_, F, C> {
    fn arity(&self) -> usize {
        self.multiframe.public_input_size() / 2
    }

    fn circuit_index(&self) -> usize {
        self.multiframe.circuit_index()
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
            &self.multiframe,
            cs,
            z,
        )?;

        let next_pc = AllocatedNum::alloc_infallible(&mut cs.namespace(|| "next_pc"), || {
            self.next
                .as_ref()
                // This is missing in the case of a final `MultiFrame`. The Lurk circuit is defined to always have index
                // 0, so it is a good default in this case.
                .map_or(F::ZERO, |x| F::from(x.circuit_index() as u64))
        });
        debug!("synthesizing with next_pc: {:?}", next_pc.get_value());

        Ok((Some(next_pc), output))
    }
}

/// All steps of an NIVC computation
pub struct NIVCSteps<'a, G: Group, C: Coprocessor<G::Scalar>>
where
    G::Scalar: LurkField,
{
    steps: Vec<NIVCStep<'a, G::Scalar, C>>,
}
impl<'a, G1, F, C1> Index<usize> for NIVCSteps<'a, G1, C1>
where
    C1: Coprocessor<F> + 'a,
    G1: Group<Scalar = F> + 'a,
    F: LurkField,
{
    type Output = NIVCStep<'a, G1::Scalar, C1>;

    fn index(&self, idx: usize) -> &<Self as std::ops::Index<usize>>::Output {
        &self.steps[idx]
    }
}

impl<'a, G1, F, C1> NIVCSteps<'a, G1, C1>
where
    C1: Coprocessor<F>,
    G1: Group<Scalar = F>,
    F: LurkField,
{
    /// Number of NIVC steps contained.
    pub fn num_steps(&self) -> usize {
        self.steps.len()
    }
    /// Separate frames according to NIVC circuit requirements.
    pub fn from_frames(
        count: usize,
        frames: &[Frame<IO<F>, Witness<F>, F, C1>],
        store: &'a Store<F>,
        folding_config: Arc<FoldingConfig<F, C1>>,
    ) -> Self {
        let mut steps = Vec::new();
        let mut last_meta = frames[0].meta;
        let mut consecutive_frames = Vec::new();

        for frame in frames {
            if frame.meta == last_meta {
                let padding_frame = frame.clone();
                consecutive_frames.push(padding_frame);
            } else {
                if last_meta == Meta::Lurk {
                    consecutive_frames.push(frame.clone());
                }
                let new_steps = MultiFrame::from_frames(
                    if last_meta == Meta::Lurk { count } else { 1 },
                    &consecutive_frames,
                    store,
                    folding_config.clone(),
                )
                .into_iter()
                .map(NIVCStep::<'_, F, C1>::new);

                steps.extend(new_steps);
                consecutive_frames.truncate(0);
                consecutive_frames.push(frame.clone());
                last_meta = frame.meta;
            }
        }

        // TODO: refactor
        if !consecutive_frames.is_empty() {
            let new_steps =
                MultiFrame::from_frames(count, &consecutive_frames, store, folding_config)
                    .into_iter()
                    .map(NIVCStep::<'_, F, C1>::new);

            steps.extend(new_steps);
        }

        if !steps.is_empty() {
            let penultimate = steps.len() - 1;
            for i in 0..(penultimate - 1) {
                steps[i].next = Some(steps[i + 1].multiframe.clone());
            }
        }
        Self { steps }
    }
}

impl<'a, F, C1> NonUniformCircuit<G1<F>, G2<F>, NIVCStep<'a, F, C1>, C2<F>> for NIVCStep<'a, F, C1>
where
    F: CurveCycleEquipped + LurkField,
    C1: Coprocessor<F>,
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    fn num_circuits(&self) -> usize {
        assert!(self.meta().is_lurk());
        self.lang().coprocessor_count() + 1
    }

    fn primary_circuit(&self, circuit_index: usize) -> Self {
        debug!(
            "getting primary_circuit for index {circuit_index} and Meta: {:?}",
            self.meta()
        );
        if circuit_index == 0 {
            debug!("using Lurk circuit");
            return self.clone();
        };
        if let Some(z_ptr) = self.lang().get_coprocessor_z_ptr(circuit_index - 1) {
            let meta = Meta::Coprocessor(*z_ptr);
            debug!(
                "using coprocessor {} with meta: {:?}",
                circuit_index - 1,
                meta
            );
            Self::blank(self.folding_config(), meta)
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
    let circuit = NIVCStep::blank(folding_config, Meta::Lurk);
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
