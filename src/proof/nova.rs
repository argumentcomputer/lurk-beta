#![allow(non_snake_case)]

use abomonation::Abomonation;
use bellpepper::util_cs::witness_cs::WitnessCS;
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::Field;
use nova::{
    errors::NovaError,
    provider::bn256_grumpkin::{bn256, grumpkin},
    provider::pedersen::CommitmentKeyExtTrait,
    traits::{
        circuit::{StepCircuit, TrivialCircuit},
        commitment::CommitmentEngineTrait,
        snark::RelaxedR1CSSNARKTrait,
        Group,
    },
    CircuitShape, CompressedSNARK, ProverKey, RecursiveSNARK, VerifierKey,
};
use pasta_curves::{pallas, vesta};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::{
    marker::PhantomData,
    sync::{Arc, Mutex},
};

use crate::{
    circuit::{
        gadgets::{
            data::GlobalAllocations,
            pointer::{AllocatedContPtr, AllocatedPtr},
        },
        CircuitFrame, MultiFrame,
    },
    config::CONFIG,
    coprocessor::Coprocessor,
    error::ProofError,
    eval::{lang::Lang, Meta},
    field::LurkField,
    proof::{supernova::FoldingConfig, FrameLike, MultiFrameTrait, Prover},
    store::Store,
};

/// This trait defines most of the requirements for programming generically over the supported Nova curve cycles
/// (currently Pallas/Vesta and BN254/Grumpkin). It being pegged on the `LurkField` trait encodes that we do
/// not expect more than one such cycle to be supported at a time for a given field.
pub trait CurveCycleEquipped: LurkField {
    /// ## Why the next 4 types?
    ///
    /// The next 4 types are purely technical, and aim at laying out type bounds in a way that rust can find them.
    /// They should eventually be replaceable by a bound on projections, once bounds on associated types progress.
    /// They are technically equivalent to bounds of
    ///  <Self::G1::CE as CommitmentEngineTrait<Self::G1>>::CommitmentKey: CommitmentKeyExtTrait<Self::G1, CE = <Self::G1 as Group>::CE>,
    ///  <Self::G2::CE as CommitmentEngineTrait<Self::G2>>::CommitmentKey: CommitmentKeyExtTrait<Self::G2, CE = <G2 as Group>::CE>,
    /// but where clauses can't be *found* by the compiler at the point where Self::G1, Self::G2 are used

    /// ## OK, but why do we need bounds at all in the first place?
    ///
    /// As to *why* those see https://github.com/microsoft/Nova/pull/200
    /// and the bound `CommitmentKey<G>: CommitmentKeyExtTrait<G, CE = G::CE>` on [`nova::provider::ipa_pc::EvaluationEngine<G>`]
    /// Essentially, Nova relies on a commitment scheme that is additively homomorphic, but encodes the practicalities of this
    /// (properties are unwieldy to encode) in the form of this CommitmentKeyExtTrait.

    /// The type of the commitment key used for points of the first curve in the cycle.
    type CK1: CommitmentKeyExtTrait<Self::G1>;
    /// The type of the commitment key used for points of the second curve in the cycle.
    type CK2: CommitmentKeyExtTrait<Self::G2>;
    /// The commitment engine type for the first curve in the cycle.
    type CE1: CommitmentEngineTrait<Self::G1, CommitmentKey = Self::CK1>;
    /// The commitment engine type for the second curve in the cycle.
    type CE2: CommitmentEngineTrait<Self::G2, CommitmentKey = Self::CK2>;

    /// The group type for the first curve in the cycle.
    type G1: Group<Base = <Self::G2 as Group>::Scalar, Scalar = Self, CE = Self::CE1>;
    /// The  group type for the second curve in the cycle.
    type G2: Group<Base = <Self::G1 as Group>::Scalar, CE = Self::CE2>;
}

impl CurveCycleEquipped for pallas::Scalar {
    type CK1 = nova::provider::pedersen::CommitmentKey<pallas::Point>;
    type CK2 = nova::provider::pedersen::CommitmentKey<vesta::Point>;
    type CE1 = nova::provider::pedersen::CommitmentEngine<pallas::Point>;
    type CE2 = nova::provider::pedersen::CommitmentEngine<vesta::Point>;

    type G1 = pallas::Point;
    type G2 = vesta::Point;
}
// The impl CurveCycleEquipped for vesta::Scalar is academically possible, but voluntarily omitted to avoid confusion.

impl CurveCycleEquipped for bn256::Scalar {
    type CK1 = nova::provider::pedersen::CommitmentKey<bn256::Point>;
    type CK2 = nova::provider::pedersen::CommitmentKey<grumpkin::Point>;
    type CE1 = nova::provider::pedersen::CommitmentEngine<bn256::Point>;
    type CE2 = nova::provider::pedersen::CommitmentEngine<grumpkin::Point>;

    type G1 = bn256::Point;
    type G2 = grumpkin::Point;
}
// The impl CurveCycleEquipped for grumpkin::Scalar is academically possible, but voluntarily omitted to avoid confusion.

/// Convenience alias for the primary group type pegged to a LurkField through a CurveCycleEquipped type.
pub type G1<F> = <F as CurveCycleEquipped>::G1;
/// Convenience alias for the secondary group type pegged to a LurkField through a CurveCycleEquipped type.
pub type G2<F> = <F as CurveCycleEquipped>::G2;

/// Type alias for the Evaluation Engine using G1 group elements.
pub type EE1<F> = nova::provider::ipa_pc::EvaluationEngine<G1<F>>;
/// Type alias for the Evaluation Engine using G2 group elements.
pub type EE2<F> = nova::provider::ipa_pc::EvaluationEngine<G2<F>>;

/// Type alias for the Relaxed R1CS Spartan SNARK using G1 group elements, EE1.
// NOTE: this is not a SNARK that uses computational commitments,
// that SNARK would be found at nova::spartan::ppsnark::RelaxedR1CSSNARK,
pub type SS1<F> = nova::spartan::snark::RelaxedR1CSSNARK<G1<F>, EE1<F>>;
/// Type alias for the Relaxed R1CS Spartan SNARK using G2 group elements, EE2.
// NOTE: this is not a SNARK that uses computational commitments,
// that SNARK would be found at nova::spartan::ppsnark::RelaxedR1CSSNARK,
pub type SS2<F> = nova::spartan::snark::RelaxedR1CSSNARK<G2<F>, EE2<F>>;

/// Type alias for a MultiFrame with S1 field elements.
/// This uses the <<F as CurveCycleEquipped>::G1 as Group>::Scalar type for the G1 scalar field elements
/// to reflect it this should not be used outside the Nova context
pub type C1Lurk<'a, F, C> = crate::circuit::circuit_frame::MultiFrame<'a, F, C>;
/// LEM's version of C1
pub type C1LEM<'a, F, C> = crate::lem::multiframe::MultiFrame<'a, F, C>;
/// Type alias for a Trivial Test Circuit with G2 scalar field elements.
pub type C2<F> = TrivialCircuit<<G2<F> as Group>::Scalar>;

/// Type alias for Nova Circuit Parameters with the curve cycle types defined above.
pub type NovaCircuitShape<F> = CircuitShape<G1<F>>;

/// Type alias for Nova Public Parameters with the curve cycle types defined above.
pub type NovaPublicParams<F, C1> = nova::PublicParams<G1<F>, G2<F>, C1, C2<F>>;

/// A struct that contains public parameters for the Nova proving system.
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PublicParams<F, SC: StepCircuit<F>>
where
    F: CurveCycleEquipped,
    // technical bounds that would disappear once associated_type_bounds stabilizes
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pp: NovaPublicParams<F, SC>,
    pk: ProverKey<G1<F>, G2<F>, SC, C2<F>, SS1<F>, SS2<F>>,
    vk: VerifierKey<G1<F>, G2<F>, SC, C2<F>, SS1<F>, SS2<F>>,
}

impl<F: CurveCycleEquipped, SC: StepCircuit<F>> Abomonation for PublicParams<F, SC>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
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
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// A proof for the intermediate steps of a recursive computation
    Recursive(
        Box<RecursiveSNARK<G1<F>, G2<F>, M, C2<F>>>,
        PhantomData<&'a C>,
    ),
    /// A proof for the final step of a recursive computation
    Compressed(
        Box<CompressedSNARK<G1<F>, G2<F>, M, C2<F>, SS1<F>, SS2<F>>>,
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
    let circuit = M::blank(folding_config, Meta::Lurk, 0);
    F::from(rc as u64) * nova::circuit_digest::<F::G1, F::G2, _>(&circuit)
}

/// Generates the public parameters for the Nova proving system.
pub fn public_params<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: StepCircuit<F> + MultiFrameTrait<'a, F, C>,
>(
    num_iters_per_step: usize,
    lang: Arc<Lang<F, C>>,
) -> PublicParams<F, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let (circuit_primary, circuit_secondary) = circuits(num_iters_per_step, lang);

    let commitment_size_hint1 = <SS1<F> as RelaxedR1CSSNARKTrait<G1<F>>>::commitment_key_floor();
    let commitment_size_hint2 = <SS2<F> as RelaxedR1CSSNARKTrait<G2<F>>>::commitment_key_floor();

    let pp = nova::PublicParams::new(
        &circuit_primary,
        &circuit_secondary,
        Some(commitment_size_hint1),
        Some(commitment_size_hint2),
    );
    let (pk, vk) = CompressedSNARK::setup(&pp).unwrap();
    PublicParams { pp, pk, vk }
}

/// Generates the circuits for the Nova proving system.
pub fn circuits<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>>(
    count: usize,
    lang: Arc<Lang<F, C>>,
) -> (M, C2<F>) {
    let folding_config = Arc::new(FoldingConfig::new_ivc(lang, count));
    (
        M::blank(folding_config, Meta::Lurk, 0),
        TrivialCircuit::default(),
    )
}

/// A struct for the Nova prover that operates on field elements of type `F`.
#[derive(Debug)]
pub struct NovaProver<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
> {
    // `reduction_count` specifies the number of small-step reductions are performed in each recursive step.
    reduction_count: usize,
    lang: Lang<F, C>,
    _phantom: PhantomData<&'a M>,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>> Prover<'a, F, C, M>
    for NovaProver<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    type PublicParams = PublicParams<F, M>;
    fn new(reduction_count: usize, lang: Lang<F, C>) -> Self {
        NovaProver::<F, C, M> {
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

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>>
    NovaProver<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// Proves the computation given the public parameters, frames, and store.
    pub fn prove(
        &self,
        pp: &PublicParams<F, M>,
        frames: &[M::EvalFrame],
        store: &'a M::Store,
        lang: &Arc<Lang<F, C>>,
    ) -> Result<(Proof<'a, F, C, M>, Vec<F>, Vec<F>, usize), ProofError> {
        let z0 = M::io_to_scalar_vector(store, frames[0].input()).map_err(|e| e.into())?;
        let zi =
            M::io_to_scalar_vector(store, frames.last().unwrap().output()).map_err(|e| e.into())?;
        let folding_config = Arc::new(FoldingConfig::new_ivc(lang.clone(), self.reduction_count()));
        let circuits = M::from_frames(self.reduction_count(), frames, store, folding_config);

        let num_steps = circuits.len();
        let proof = Proof::prove_recursively(
            pp,
            store,
            &circuits,
            self.reduction_count,
            z0.clone(),
            lang.clone(),
        )?;

        Ok((proof, z0, zi, num_steps))
    }

    /// Evaluates and proves the computation given the public parameters, expression, environment, and store.
    pub fn evaluate_and_prove(
        &self,
        pp: &PublicParams<F, M>,
        expr: M::Ptr,
        env: M::Ptr,
        store: &'a M::Store,
        limit: usize,
        lang: &Arc<Lang<F, C>>,
    ) -> Result<(Proof<'a, F, C, M>, Vec<F>, Vec<F>, usize), ProofError> {
        let frames = M::get_evaluation_frames(
            |count| self.needs_frame_padding(count),
            expr,
            env,
            store,
            limit,
            lang,
        )?;
        self.prove(pp, &frames, store, lang)
    }
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>> Proof<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// Proves the computation recursively, generating a recursive SNARK proof.
    #[tracing::instrument(skip_all, name = "nova::prove_recursively")]
    pub fn prove_recursively(
        pp: &PublicParams<F, M>,
        store: &M::Store,
        circuits: &[M],
        num_iters_per_step: usize,
        z0: Vec<F>,
        lang: Arc<Lang<F, C>>,
    ) -> Result<Self, ProofError> {
        assert!(!circuits.is_empty());
        assert_eq!(circuits[0].arity(), z0.len());
        let debug = false;
        let z0_primary = z0;
        let z0_secondary = Self::z0_secondary();

        assert_eq!(circuits[0].frames().unwrap().len(), num_iters_per_step);
        let (_circuit_primary, circuit_secondary): (
            MultiFrame<'_, F, C>,
            TrivialCircuit<<G2<F> as Group>::Scalar>,
        ) = crate::proof::nova::circuits(num_iters_per_step, lang);

        tracing::debug!("circuits.len: {}", circuits.len());

        // produce a recursive SNARK
        let mut recursive_snark: Option<RecursiveSNARK<G1<F>, G2<F>, M, C2<F>>> = None;

        // the shadowing here is voluntary
        let recursive_snark = if CONFIG.parallelism.recursive_steps.is_parallel() {
            let cc = circuits
                .iter()
                .map(|c| Mutex::new(c.clone()))
                .collect::<Vec<_>>();

            crossbeam::thread::scope(|s| {
                s.spawn(|_| {
                    // Skip the very first circuit's witness, so `prove_step` can begin immediately.
                    // That circuit's witness will not be cached and will just be computed on-demand.
                    cc.par_iter().skip(1).for_each(|mf| {
                        let witness = {
                            let mf1 = mf.lock().unwrap();
                            mf1.compute_witness(store)
                        };
                        let mut mf2 = mf.lock().unwrap();

                        *mf2.cached_witness() = Some(witness);
                    });
                });

                for circuit_primary in cc.iter() {
                    let circuit_primary = circuit_primary.lock().unwrap();
                    assert_eq!(
                        num_iters_per_step,
                        circuit_primary.frames().unwrap().iter().len()
                    );

                    let mut r_snark = recursive_snark.unwrap_or_else(|| {
                        RecursiveSNARK::new(
                            &pp.pp,
                            &circuit_primary,
                            &circuit_secondary,
                            z0_primary.clone(),
                            z0_secondary.clone(),
                        )
                    });
                    r_snark
                        .prove_step(
                            &pp.pp,
                            &circuit_primary,
                            &circuit_secondary,
                            z0_primary.clone(),
                            z0_secondary.clone(),
                        )
                        .expect("failure to prove Nova step");
                    recursive_snark = Some(r_snark);
                }
                recursive_snark
            })
            .unwrap()
        } else {
            for circuit_primary in circuits.iter() {
                assert_eq!(num_iters_per_step, circuit_primary.frames().unwrap().len());
                if debug {
                    // For debugging purposes, synthesize the circuit and check that the constraint system is satisfied.
                    use bellpepper_core::test_cs::TestConstraintSystem;
                    let mut cs = TestConstraintSystem::<<G1<F> as Group>::Scalar>::new();

                    // This is a CircuitFrame, not an EvalFrame
                    let first_frame = circuit_primary.frames().unwrap().iter().next().unwrap();
                    let zi =
                        M::io_to_scalar_vector(store, first_frame.input()).map_err(|e| e.into())?;
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
                        z0_primary.clone(),
                        z0_secondary.clone(),
                    )
                });
                r_snark
                    .prove_step(
                        &pp.pp,
                        circuit_primary,
                        &circuit_secondary,
                        z0_primary.clone(),
                        z0_secondary.clone(),
                    )
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

    /// Compresses the proof using a (Spartan) Snark (finishing step)
    pub fn compress(self, pp: &PublicParams<F, M>) -> Result<Self, ProofError> {
        match &self {
            Self::Recursive(recursive_snark, _) => Ok(Self::Compressed(
                Box::new(CompressedSNARK::<_, _, _, _, SS1<F>, SS2<F>>::prove(
                    &pp.pp,
                    &pp.pk,
                    recursive_snark,
                )?),
                PhantomData,
            )),
            Self::Compressed(_, _) => Ok(self),
        }
    }

    /// Verifies the proof given the public parameters, the number of steps, and the input and output values.
    pub fn verify(
        &self,
        pp: &PublicParams<F, M>,
        num_steps: usize,
        z0: &[F],
        zi: &[F],
    ) -> Result<bool, NovaError> {
        let (z0_primary, zi_primary) = (z0, zi);
        let z0_secondary = Self::z0_secondary();
        let zi_secondary = z0_secondary.clone();

        let (zi_primary_verified, zi_secondary_verified) = match self {
            Self::Recursive(p, _) => p.verify(&pp.pp, num_steps, z0_primary, &z0_secondary),
            Self::Compressed(p, _) => {
                p.verify(&pp.vk, num_steps, z0_primary.to_vec(), z0_secondary)
            }
        }?;

        Ok(zi_primary == zi_primary_verified && zi_secondary == zi_secondary_verified)
    }

    fn z0_secondary() -> Vec<<F::G2 as Group>::Scalar> {
        vec![<G2<F> as Group>::Scalar::ZERO]
    }
}

impl<'a, F: LurkField, C: Coprocessor<F>> StepCircuit<F> for MultiFrame<'a, F, C> {
    fn arity(&self) -> usize {
        6
    }

    #[tracing::instrument(skip_all, name = "<MultiFrame as StepCircuit>::synthesize")]
    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        assert_eq!(self.arity(), z.len());

        if cs.is_witness_generator() {
            if let Some(w) = &self.cached_witness {
                let aux = w.aux_slice();
                let end = aux.len() - 6;
                let inputs = &w.inputs_slice()[1..];

                cs.extend_aux(aux);
                cs.extend_inputs(inputs);

                let scalars = &aux[end..];

                let allocated = {
                    let mut bogus_cs = WitnessCS::new();

                    scalars
                        .iter()
                        .map(|scalar| AllocatedNum::alloc_infallible(&mut bogus_cs, || *scalar))
                        .collect::<Vec<_>>()
                };

                return Ok(allocated);
            }
        };
        let input_expr = AllocatedPtr::by_index(0, z);
        let input_env = AllocatedPtr::by_index(1, z);
        let input_cont = AllocatedContPtr::by_index(2, z);

        let count = self.count;

        let (new_expr, new_env, new_cont) = match self.meta {
            Meta::Lurk => match self.frames.as_ref() {
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
            },
            Meta::Coprocessor(z_ptr) => {
                let c = self
                    .folding_config
                    .lang()
                    .get_coprocessor_from_zptr(&z_ptr)
                    .expect("coprocessor not found for a frame that requires one");
                match self.frames.as_ref() {
                    Some(frames) => {
                        assert_eq!(1, frames.len());
                        let s = self.store.expect("store missing");
                        let g =
                            GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s)?;

                        c.synthesize_step_circuit(
                            cs,
                            s,
                            &g,
                            &z_ptr,
                            &input_expr,
                            &input_env,
                            &input_cont,
                            false,
                        )?
                    }
                    None => {
                        assert!(self.store.is_none());
                        let s = Store::default();

                        let g =
                            GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), &s)?;

                        c.synthesize_step_circuit(
                            cs,
                            &s,
                            &g,
                            &z_ptr,
                            &input_expr,
                            &input_env,
                            &input_cont,
                            false,
                        )?
                    }
                }
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
}

impl<'a, F: LurkField, C: Coprocessor<F>> MultiFrame<'a, F, C> {
    #[allow(dead_code)] // TODO(huitseeker): is this used?
    fn compute_witness(&self, s: &Store<F>) -> WitnessCS<F> {
        let mut wcs = WitnessCS::new();

        let input = self.input.unwrap();

        use crate::tag::Tag;
        let expr = s.hash_expr(&input.expr).unwrap();
        let env = s.hash_expr(&input.env).unwrap();
        let cont = s.hash_cont(&input.cont).unwrap();

        let z_scalar = vec![
            expr.tag().to_field(),
            *expr.value(),
            env.tag().to_field(),
            *env.value(),
            cont.tag().to_field(),
            *cont.value(),
        ];

        let mut bogus_cs = WitnessCS::<F>::new();
        let z: Vec<AllocatedNum<F>> = z_scalar
            .iter()
            .map(|x| AllocatedNum::alloc(&mut bogus_cs, || Ok(*x)).unwrap())
            .collect::<Vec<_>>();

        let _ = self.clone().synthesize(&mut wcs, z.as_slice());

        wcs
    }
}
