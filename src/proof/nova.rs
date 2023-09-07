#![allow(non_snake_case)]
use std::{marker::PhantomData, sync::Mutex};

use abomonation::Abomonation;
use bellpepper::util_cs::witness_cs::WitnessCS;
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::Field;
use nova::{
    errors::NovaError,
    provider::bn256_grumpkin::{bn256, grumpkin},
    provider::pedersen::CommitmentKeyExtTrait,
    traits::{
        circuit::{StepCircuit, TrivialTestCircuit},
        commitment::CommitmentEngineTrait,
        snark::RelaxedR1CSSNARKTrait,
        Group,
    },
    CompressedSNARK, ProverKey, RecursiveSNARK, VerifierKey,
};
use pasta_curves::{pallas, vesta};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::iter::ExactSizeIterator;
use std::sync::Arc;

use crate::circuit::{
    gadgets::{
        data::GlobalAllocations,
        pointer::{AllocatedContPtr, AllocatedPtr},
    },
    CircuitFrame, MultiFrame,
};
use crate::config::CONFIG;

use crate::coprocessor::Coprocessor;
use crate::error::ProofError;
use crate::eval::lang::Lang;
use crate::field::LurkField;
use crate::proof::{MultiFrameTrait, Prover, PublicParameters};
use crate::store::Store;

use super::FrameLike;

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
pub type C1<'a, F, C> = MultiFrame<'a, F, C>;
/// Type alias for a Trivial Test Circuit with G2 scalar field elements.
pub type C2<F> = TrivialTestCircuit<<G2<F> as Group>::Scalar>;

/// Type alias for Nova Public Parameters with the curve cycle types defined above.
pub type NovaPublicParams<F, C1> = nova::PublicParams<G1<F>, G2<F>, C1, C2<F>>;

/// A struct that contains public parameters for the Nova proving system.
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PublicParams<F, M: StepCircuit<F>>
where
    F: CurveCycleEquipped,
    // technical bounds that would disappear once associated_type_bounds stabilizes
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pub(crate) pp: NovaPublicParams<F, M>,
    pub(crate) pk: ProverKey<G1<F>, G2<F>, M, C2<F>, SS1<F>, SS2<F>>,
    pub(crate) vk: VerifierKey<G1<F>, G2<F>, M, C2<F>, SS1<F>, SS2<F>>,
}

impl<F: CurveCycleEquipped, M: StepCircuit<F>> Abomonation for PublicParams<F, M>
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
pub enum Proof<F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// A proof for the intermediate steps of a recursive computation
    Recursive(Box<RecursiveSNARK<G1<F>, G2<F>, M, C2<F>>>, PhantomData<C>),
    /// A proof for the final step of a recursive computation
    Compressed(
        Box<CompressedSNARK<G1<F>, G2<F>, M, C2<F>, SS1<F>, SS2<F>>>,
        PhantomData<C>,
    ),
}

/// Generates the public parameters for the Nova proving system.
pub fn public_params<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F>,
    M: StepCircuit<F> + MultiFrameTrait<F, C>,
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

    let pp = nova::PublicParams::setup(
        &circuit_primary,
        &circuit_secondary,
        Some(commitment_size_hint1),
        Some(commitment_size_hint2),
    )
    .unwrap();
    let (pk, vk) = CompressedSNARK::setup(&pp).unwrap();
    PublicParams { pp, pk, vk }
}

/// Generates the circuits for the Nova proving system.
pub fn circuits<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>>(
    count: usize,
    lang: Arc<Lang<F, C>>,
) -> (M, C2<F>) {
    (M::blank(count, lang), TrivialTestCircuit::default())
}

/// A struct for the Nova prover that operates on field elements of type `F`.
#[derive(Debug)]
pub struct NovaProver<F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>> {
    // `reduction_count` specifies the number of small-step reductions are performed in each recursive step.
    reduction_count: usize,
    lang: Lang<F, C>,
    _phantom: PhantomData<M>,
}

impl<F: CurveCycleEquipped, C1: StepCircuit<F>> PublicParameters for PublicParams<F, C1>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>> Prover<F, C, M>
    for NovaProver<F, C, M>
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

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>> NovaProver<F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// Proves the computation given the public parameters, frames, and store.
    pub fn prove(
        &'a self,
        pp: &'a PublicParams<F, M>,
        frames: &[M::EvalFrame],
        store: &M::Store,
        lang: &Arc<Lang<F, C>>,
    ) -> Result<(Proof<F, C, M>, Vec<F>, Vec<F>, usize), ProofError> {
        let z0 = M::to_io_vector(store, frames[0].input()).map_err(|e| e.into())?;
        let zi = M::to_io_vector(store, frames.last().unwrap().output()).map_err(|e| e.into())?;
        let circuits = M::from_frames(self.reduction_count(), frames, store, lang.clone());

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
        &'a self,
        pp: &'a PublicParams<F, M>,
        expr: M::Ptr,
        env: M::Ptr,
        store: &mut M::Store,
        limit: usize,
        lang: &Arc<Lang<F, C>>,
    ) -> Result<(Proof<F, C, M>, Vec<F>, Vec<F>, usize), ProofError> {
        let frames = M::get_evaluation_frames(self, expr, env, store, limit)?;
        self.prove(pp, &frames, store, lang)
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
                        .map(|scalar| AllocatedNum::alloc(&mut bogus_cs, || Ok(*scalar)).unwrap())
                        .collect::<Vec<_>>()
                };

                return Ok(allocated);
            }
        };
        let input_expr = AllocatedPtr::by_index(0, z);
        let input_env = AllocatedPtr::by_index(1, z);
        let input_cont = AllocatedContPtr::by_index(2, z);

        let count = self.count;

        let (new_expr, new_env, new_cont) = match self.frames.as_ref() {
            Some(frames) => {
                let s = self.store.expect("store missing");
                let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s)?;

                self.synthesize_frames(cs, s, (input_expr, input_env, input_cont), frames, &g)?
            }
            None => {
                assert!(self.store.is_none());
                let s = Store::default();
                let blank_frame = CircuitFrame::blank();
                let frames = vec![blank_frame; count];

                let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), &s)?;

                self.synthesize_frames(cs, &s, (input_expr, input_env, input_cont), &frames, &g)?
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

impl<'a: 'b, 'b, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>> Proof<F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// Proves the computation recursively, generating a recursive SNARK proof.
    #[tracing::instrument(skip_all, name = "Proof::prove_recursively")]
    pub fn prove_recursively(
        pp: &'a PublicParams<F, M>,
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

        assert_eq!(
            circuits[0].frames().unwrap().into_iter().len(),
            num_iters_per_step
        );
        let (_circuit_primary, circuit_secondary): (
            MultiFrame<'_, F, C>,
            TrivialTestCircuit<<G2<F> as Group>::Scalar>,
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
                        circuit_primary.frames().unwrap().into_iter().len()
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
                assert_eq!(
                    num_iters_per_step,
                    circuit_primary.frames().unwrap().into_iter().len()
                );
                if debug {
                    // For debugging purposes, synthesize the circuit and check that the constraint system is satisfied.
                    use bellpepper_core::test_cs::TestConstraintSystem;
                    let mut cs = TestConstraintSystem::<<G1<F> as Group>::Scalar>::new();

                    // This is a CircuitFrame, not an EvalFrame
                    let first_frame = circuit_primary
                        .frames()
                        .unwrap()
                        .into_iter()
                        .next()
                        .unwrap();
                    let zi = M::to_io_vector(store, first_frame.input()).map_err(|e| e.into())?;
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
    pub fn compress(self, pp: &'a PublicParams<F, M>) -> Result<Self, ProofError> {
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

#[cfg(test)]
pub mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use crate::lurk_sym_ptr;
    use crate::num::Num;
    use crate::state::{user_sym, State};

    use super::*;
    use crate::eval::lang::Coproc;
    use crate::eval::Frame;
    use crate::proof::{EvaluationStore, Provable};
    use crate::ptr::ContPtr;
    use crate::tag::{Op, Op1, Op2};

    use super::FrameLike;
    use bellpepper::util_cs::witness_cs::WitnessCS;
    use bellpepper::util_cs::{metric_cs::MetricCS, Comparable};
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bellpepper_core::{Circuit, Delta};
    use pallas::Scalar as Fr;

    const DEFAULT_REDUCTION_COUNT: usize = 5;
    const REDUCTION_COUNTS_TO_TEST: [usize; 3] = [1, 2, 5];

    // Returns index of first mismatch, along with the mismatched elements if they exist.
    fn mismatch<T: PartialEq + Copy>(a: &[T], b: &[T]) -> Option<(usize, (Option<T>, Option<T>))> {
        let min_len = a.len().min(b.len());
        for i in 0..min_len {
            if a[i] != b[i] {
                return Some((i, (Some(a[i]), Some(b[i]))));
            }
        }
        match (a.get(min_len), b.get(min_len)) {
            (Some(&a_elem), None) => Some((min_len, (Some(a_elem), None))),
            (None, Some(&b_elem)) => Some((min_len, (None, Some(b_elem)))),
            _ => None,
        }
    }

    pub fn test_aux<F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>>(
        s: &mut M::Store,
        expr: &str,
        expected_result: Option<M::Ptr>,
        expected_env: Option<M::Ptr>,
        expected_cont: Option<ContPtr<F>>,
        expected_emitted: Option<Vec<M::Ptr>>,
        expected_iterations: usize,
        lang: Option<Arc<Lang<F, C>>>,
    )
    // technical bounds that would disappear once associated_type_bounds stabilizes
    where
        <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        for chunk_size in REDUCTION_COUNTS_TO_TEST {
            nova_test_full_aux::<_, _, M>(
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
                lang,
            )
        }
    }

    fn nova_test_full_aux<F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>>(
        s: &mut M::Store,
        expr: &str,
        expected_result: Option<M::Ptr>,
        expected_env: Option<M::Ptr>,
        expected_cont: Option<ContPtr<F>>,
        expected_emitted: Option<&Vec<M::Ptr>>,
        expected_iterations: usize,
        reduction_count: usize,
        check_nova: bool,
        limit: Option<usize>,
        lang: Option<Arc<Lang<F, C>>>,
    )
    // technical bounds that would disappear once associated_type_bounds stabilizes
    where
        <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        let expr = s.read(expr).unwrap();

        let mut f = |l| {
            nova_test_full_aux2::<_, _, M>(
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
                l,
            )
        };

        if let Some(l) = lang {
            f(l)
        } else {
            let lang = Lang::new();
            f(Arc::new(lang))
        };
    }

    fn nova_test_full_aux2<F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>>(
        s: &mut M::Store,
        expr: M::Ptr,
        expected_result: Option<M::Ptr>,
        expected_env: Option<M::Ptr>,
        expected_cont: Option<ContPtr<F>>,
        expected_emitted: Option<&Vec<M::Ptr>>,
        expected_iterations: usize,
        reduction_count: usize,
        check_nova: bool,
        limit: Option<usize>,
        lang: Arc<Lang<F, C>>,
    )
    // technical bounds that would disappear once associated_type_bounds stabilizes
    where
        <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        let limit = limit.unwrap_or(10000);

        let e = s.initial_empty_env();

        let nova_prover = NovaProver::<F, C, M>::new(reduction_count, (*lang).clone());

        if check_nova {
            let pp = public_params::<_, _, M>(reduction_count, lang.clone());
            let (proof, z0, zi, num_steps) = nova_prover
                .evaluate_and_prove(&pp, expr, e, s, limit, &lang)
                .unwrap();

            let res = proof.verify(&pp, num_steps, &z0, &zi);
            if res.is_err() {
                tracing::debug!("{:?}", &res);
            }
            assert!(res.unwrap());

            let compressed = proof.compress(&pp).unwrap();
            let res2 = compressed.verify(&pp, num_steps, &z0, &zi);

            assert!(res2.unwrap());
        }

        let frames = M::get_evaluation_frames(&nova_prover, expr, e, s, limit).unwrap();

        let multiframes = M::from_frames(nova_prover.reduction_count(), &frames, s, lang.clone());
        let len = multiframes.len();

        let adjusted_iterations = nova_prover.expected_total_iterations(expected_iterations);
        let mut previous_frame: Option<&M> = None;

        let mut cs_blank = MetricCS::<F>::new();

        let blank = M::blank(reduction_count, lang);
        blank
            .synthesize(&mut cs_blank)
            .expect("failed to synthesize blank");

        for (_i, multiframe) in multiframes.iter().enumerate() {
            let mut cs = TestConstraintSystem::new();
            let mut wcs = WitnessCS::new();

            tracing::debug!("synthesizing test cs");
            multiframe.clone().synthesize(&mut cs).unwrap();
            tracing::debug!("synthesizing witness cs");
            multiframe.clone().synthesize(&mut wcs).unwrap();

            if let Some(prev) = previous_frame {
                assert!(prev.precedes(multiframe));
            };
            // tracing::debug!("frame {}" i);
            let unsat = cs.which_is_unsatisfied();
            if unsat.is_some() {
                // For some reason, this isn't getting printed from within the implementation as expected.
                // Since we always want to know this information, if the condition occurs, just print it here.
                tracing::debug!("{:?}", unsat);
            }
            assert!(cs.is_satisfied());
            assert!(cs.verify(&multiframe.public_inputs()));
            tracing::debug!("cs is satisfied!");
            let cs_inputs = cs.scalar_inputs();
            let cs_aux = cs.scalar_aux();

            let wcs_inputs = wcs.scalar_inputs();
            let wcs_aux = wcs.scalar_aux();

            assert_eq!(None, mismatch(&cs_inputs, &wcs_inputs));
            assert_eq!(None, mismatch(&cs_aux, &wcs_aux));

            previous_frame = Some(multiframe);

            let delta = cs.delta(&cs_blank, true);

            assert!(delta == Delta::Equal);
        }
        let output = previous_frame.unwrap().output();

        if let Some(expected_emitted) = expected_emitted {
            let emitted_vec: Vec<_> = frames
                .iter()
                .filter_map(|frame| frame.output().maybe_emitted_expression(s))
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

        assert_eq!(expected_iterations, M::significant_frame_count(&frames));
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
        test_aux::<_, Coproc<Fr>>(
            s,
            "(+ 1 2)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    #[should_panic]
    // This tests the testing mechanism. Since the supplied expected value is wrong,
    // the test should panic on an assertion failure.
    fn test_prove_binop_fail() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(+ 1 2)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_arithmetic_let() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_eq() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, t);
        let terminal = s.get_cont_terminal();
        nova_test_full_aux::<Coproc<Fr>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_num_equal() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, t);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(= 5 5)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );

        let expected = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(= 5 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_invalid_num_equal() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, nil);
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(= 5 nil)",
            Some(expected),
            None,
            Some(error),
            None,
            3,
            None,
        );

        let expected = s.num(5);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(= nil 5)",
            Some(expected),
            None,
            Some(error),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_equal() {
        let s = &mut Store::<Fr>::default();
        let nil = lurk_sym_ptr!(s, nil);
        let t = lurk_sym_ptr!(s, t);
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(eq 5 nil)",
            Some(nil),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(eq nil 5)",
            Some(nil),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(eq nil nil)",
            Some(t),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(eq 5 5)", Some(t), None, Some(terminal), None, 3, None);
    }

    #[test]
    fn test_prove_quote_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(quote (1) (2))", None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_if() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(if t 5 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );

        let expected = s.num(6);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(if nil 5 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        )
    }

    #[test]
    fn test_prove_if_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(if nil 5 6 7)",
            Some(expected),
            None,
            Some(error),
            None,
            2,
            None,
        )
    }

    #[test]
    #[ignore]
    fn test_prove_if_fully_evaluates() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(10);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(if t (+ 5 5) 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
    }

    #[test]
    #[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
    fn test_prove_recursion1() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
    fn test_prove_recursion2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    fn test_prove_unop_regression_aux(chunk_count: usize) {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, t);
        let terminal = s.get_cont_terminal();
        nova_test_full_aux::<Coproc<Fr>>(
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
            None,
        );

        let expected = s.num(1);
        nova_test_full_aux::<Coproc<Fr>>(
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
            None,
        );

        let expected = s.num(2);
        nova_test_full_aux::<Coproc<Fr>>(
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
            None,
        );

        let expected = s.num(123);
        nova_test_full_aux::<Coproc<Fr>>(
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
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(emit 123)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(99);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda (x) x) 99)",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(99);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda (y)
                    ((lambda (x) y) 888))
                  99)",
            Some(expected),
            None,
            Some(terminal),
            None,
            9,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate3() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(999);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate4() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(888);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate5() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(999);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_evaluate_sum() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(9);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(+ 2 (+ 3 4))",
            Some(expected),
            None,
            Some(terminal),
            None,
            6,
            None,
        );
    }

    #[test]
    fn test_prove_binop_rest_is_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(9);
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(- 9 8 7)",
            Some(expected),
            None,
            Some(error),
            None,
            2,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(= 9 8 7)",
            Some(expected),
            None,
            Some(error),
            None,
            2,
            None,
        );
    }

    fn op_syntax_error<T: Op + Copy>() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        let mut test = |op: T| {
            let name = op.symbol_name();

            if !op.supports_arity(0) {
                let expr = format!("({name})");
                tracing::debug!("{:?}", &expr);
                test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
            }
            if !op.supports_arity(1) {
                let expr = format!("({name} 123)");
                tracing::debug!("{:?}", &expr);
                test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
            }
            if !op.supports_arity(2) {
                let expr = format!("({name} 123 456)");
                tracing::debug!("{:?}", &expr);
                test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
            }

            if !op.supports_arity(3) {
                let expr = format!("({name} 123 456 789)");
                tracing::debug!("{:?}", &expr);
                let iterations = if op.supports_arity(2) { 2 } else { 1 };
                test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, iterations, None);
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
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(- 9 5)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_product() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(45);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(* 9 5)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_quotient() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(7);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(/ 21 3)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_error_div_by_zero() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(0);
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(/ 21 0)",
            Some(expected),
            None,
            Some(error),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_error_invalid_type_and_not_cons() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, nil);
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(/ 21 nil)",
            Some(expected),
            None,
            Some(error),
            None,
            3,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_adder() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    fn test_prove_current_env_simple() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(current-env)",
            Some(expected),
            None,
            Some(terminal),
            None,
            1,
            None,
        );
    }

    #[test]
    fn test_prove_current_env_rest_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let expected = s.read("(current-env a)").unwrap();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(current-env a)",
            Some(expected),
            None,
            Some(error),
            None,
            1,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_let_simple() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(1);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(let ((a 1))
                  a)",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_let_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(let ((a 1 2)) a)",
            None,
            None,
            Some(error),
            None,
            1,
            None,
        );
    }

    #[test]
    fn test_prove_letrec_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec ((a 1 2)) a)",
            None,
            None,
            Some(error),
            None,
            1,
            None,
        );
    }

    #[test]
    fn test_prove_lambda_empty_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda (x)) 0)",
            None,
            None,
            Some(error),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_let_empty_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(let)", None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_let_empty_body_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(let ((a 1)))", None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_letrec_empty_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(letrec)", None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_letrec_empty_body_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec ((a 1)))",
            None,
            None,
            Some(error),
            None,
            1,
            None,
        );
    }

    #[test]
    fn test_prove_let_body_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, t);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(eq nil (let () nil))",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
            None,
        );
    }

    #[test]
    fn test_prove_let_rest_body_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(let ((a 1)) a 1)",
            None,
            None,
            Some(error),
            None,
            1,
            None,
        );
    }

    #[test]
    fn test_prove_letrec_rest_body_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec ((a 1)) a 1)",
            None,
            None,
            Some(error),
            None,
            1,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_let_null_bindings() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(let () (+ 1 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
            None,
        );
    }
    #[test]
    #[ignore]
    fn test_prove_letrec_null_bindings() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec () (+ 1 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_let() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(6);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_arithmetic() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(20);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_comparison() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, t);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_conditional() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_conditional2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(6);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_fundamental_conditional_bug() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_fully_evaluates() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(10);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(if t (+ 5 5) 6)",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_recursion() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_recursion_multiarg() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_recursion_optimized() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_tail_recursion() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            93,None
        );
    }

    #[test]
    #[ignore]
    fn test_prove_tail_recursion_somewhat_optimized() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(25);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            81,None
        );
    }

    #[test]
    #[ignore]
    fn test_prove_no_mutual_recursion() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, t);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_no_mutual_recursion_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_cons1() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(1);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(car (cons 1 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
    }

    #[test]
    fn test_prove_car_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(car (1 2) 3)", None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_cdr_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(cdr (1 2) 3)", None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_atom_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(atom 123 4)", None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_emit_end_is_nil_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(emit 123 4)", None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_cons2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(cdr (cons 1 2))",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda1() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda () 123))",
            Some(expected),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(10);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(let ((x 9) (f (lambda () (+ x 1)))) (f))",
            Some(expected),
            None,
            Some(terminal),
            None,
            10,
            None,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda3() {
        let s = &mut Store::<Fr>::default();
        let expected = {
            let arg = s.user_sym("x");
            let num = s.num(123);
            let body = s.list(&[num]);
            let env = lurk_sym_ptr!(s, nil);
            s.intern_fun(arg, body, env)
        };
        let terminal = s.get_cont_terminal();
        nova_test_full_aux::<Coproc<Fr>>(
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
            None,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda4() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda () 123) 1)",
            None,
            None,
            Some(error),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_zero_arg_lambda5() {
        let s = &mut Store::<Fr>::default();
        let expected = s.read("(123)").unwrap();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "(123)", Some(expected), None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_zero_arg_lambda6() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((emit 123))",
            Some(expected),
            None,
            Some(error),
            None,
            5,
            None,
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
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            14,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_minimal_tail_call() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_cons_in_function1() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_cons_in_function2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiarg_eval_bug() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(car (cdr '(1 2 3 4)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiple_letrec_bindings() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_tail_call2() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiple_letrecstar_bindings() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(13);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec ((double (lambda (x) (* 2 x)))
                           (square (lambda (x) (* x x))))
                          (+ (square 3) (double 2)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            22,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiple_letrecstar_bindings_referencing() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(11);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec ((double (lambda (x) (* 2 x)))
                           (double-inc (lambda (x) (+ 1 (double x)))))
                          (+ (double 3) (double-inc 2)))",
            Some(expected),
            None,
            Some(terminal),
            None,
            31,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_multiple_letrecstar_bindings_recursive() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(33);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_dont_discard_rest_env() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(18);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_fibonacci() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(1);
        let terminal = s.get_cont_terminal();
        nova_test_full_aux::<Coproc<Fr>>(
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
            None,
        );
    }

    // #[test]
    // #[ignore]
    // fn test_prove_fibonacci_100() {
    //     let s = &mut Store::<Fr>::default();
    //     let expected = s.read("354224848179261915075").unwrap();
    //     let terminal = s.get_cont_terminal();
    //     nova_test_full_aux::<Coproc<Fr>>::(
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
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec ((a (lambda (x) (cons 2 2))))
               (a 1))",
            None,
            None,
            Some(terminal),
            None,
            9,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_chained_functional_commitment() {
        let s = &mut Store::<Fr>::default();
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
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
            None,
        );
    }

    #[test]
    fn test_prove_begin_empty() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(begin)",
            Some(expected),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_begin_emit() {
        let s = &mut Store::<Fr>::default();
        let expr = "(begin (emit 1) (emit 2) (emit 3))";
        let expected_expr = s.num(3);
        let expected_emitted = vec![s.num(1), s.num(2), s.num(3)];
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            expr,
            Some(expected_expr),
            None,
            None,
            Some(expected_emitted),
            13,
            None,
        );
    }

    #[test]
    fn test_prove_str_car() {
        let s = &mut Store::<Fr>::default();
        let expected_a = s.read(r"#\a").unwrap();
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(car "apple")"#,
            Some(expected_a),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_str_cdr() {
        let s = &mut Store::<Fr>::default();
        let expected_pple = s.read(r#" "pple" "#).unwrap();
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(cdr "apple")"#,
            Some(expected_pple),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_str_car_empty() {
        let s = &mut Store::<Fr>::default();
        let expected_nil = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(car "")"#,
            Some(expected_nil),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_str_cdr_empty() {
        let s = &mut Store::<Fr>::default();
        let expected_empty_str = s.intern_string("");
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(cdr "")"#,
            Some(expected_empty_str),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_strcons() {
        let s = &mut Store::<Fr>::default();
        let expected_apple = s.read(r#" "apple" "#).unwrap();
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(strcons #\a "pple")"#,
            Some(expected_apple),
            None,
            Some(terminal),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_str_cons_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r"(strcons #\a 123)",
            None,
            None,
            Some(error),
            None,
            3,
            None,
        );
    }

    #[test]
    fn test_prove_one_arg_cons_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, r#"(cons "")"#, None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_car_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(car nil)"#,
            Some(expected),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_cdr_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(cdr nil)"#,
            Some(expected),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_car_cdr_invalid_tag_error_sym() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, r#"(car car)"#, None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, r#"(cdr car)"#, None, None, Some(error), None, 2, None);
    }

    #[test]
    fn test_prove_car_cdr_invalid_tag_error_char() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, r"(car #\a)", None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, r"(cdr #\a)", None, None, Some(error), None, 2, None);
    }

    #[test]
    fn test_prove_car_cdr_invalid_tag_error_num() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, r#"(car 42)"#, None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, r#"(cdr 42)"#, None, None, Some(error), None, 2, None);
    }

    #[test]
    fn test_prove_car_cdr_of_cons() {
        let s = &mut Store::<Fr>::default();
        let res1 = s.num(1);
        let res2 = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(car (cons 1 2))"#,
            Some(res1),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(cdr (cons 1 2))"#,
            Some(res2),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
    }

    #[test]
    fn test_prove_car_cdr_invalid_tag_error_lambda() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(car (lambda (x) x))"#,
            None,
            None,
            Some(error),
            None,
            2,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(cdr (lambda (x) x))"#,
            None,
            None,
            Some(error),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_hide_open() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (hide 123 456))";
        let expected = s.num(456);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 5, None);
    }

    #[test]
    fn test_prove_hide_wrong_secret_type() {
        let s = &mut Store::<Fr>::default();
        let expr = "(hide 'x 456)";
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 3, None);
    }

    #[test]
    fn test_prove_hide_secret() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (hide 123 456))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 5, None);
    }

    #[test]
    fn test_prove_hide_open_sym() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (hide 123 'x))";
        let x = s.user_sym("x");
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(x), None, Some(terminal), None, 5, None);
    }

    #[test]
    fn test_prove_commit_open_sym() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (commit 'x))";
        let x = s.user_sym("x");
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(x), None, Some(terminal), None, 4, None);
    }

    #[test]
    fn test_prove_commit_open() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (commit 123))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 4, None);
    }

    #[test]
    fn test_prove_commit_error() {
        let s = &mut Store::<Fr>::default();
        let expr = "(commit 123 456)";
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_open_error() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open 123 456)";
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 1, None);
    }

    #[test]
    fn test_prove_open_wrong_type() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open 'asdf)";
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 2, None);
    }

    #[test]
    fn test_prove_secret_wrong_type() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret 'asdf)";
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 2, None);
    }

    #[test]
    fn test_prove_commit_secret() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (commit 123))";
        let expected = s.num(0);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 4, None);
    }

    #[test]
    fn test_prove_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(num 123)";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 2, None);
    }

    #[test]
    fn test_prove_num_char() {
        let s = &mut Store::<Fr>::default();
        let expr = r"(num #\a)";
        let expected = s.num(97);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 2, None);
    }

    #[test]
    fn test_prove_char_num() {
        let s = &mut Store::<Fr>::default();
        let expr = r#"(char 97)"#;
        let expected_a = s.read(r"#\a").unwrap();
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            expr,
            Some(expected_a),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
    }

    #[test]
    fn test_prove_char_coercion() {
        let s = &mut Store::<Fr>::default();
        let expr = r#"(char (- 0 4294967200))"#;
        let expr2 = r#"(char (- 0 4294967199))"#;
        let expected_a = s.read(r"#\a").unwrap();
        let expected_b = s.read(r"#\b").unwrap();
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            expr,
            Some(expected_a),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            expr2,
            Some(expected_b),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
    }

    #[test]
    fn test_prove_commit_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(num (commit 123))";
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(terminal), None, 4, None);
    }

    #[test]
    fn test_prove_hide_open_comm_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (comm (num (hide 123 456))))";
        let expected = s.num(456);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 9, None);
    }

    #[test]
    fn test_prove_hide_secret_comm_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (comm (num (hide 123 456))))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 9, None);
    }

    #[test]
    fn test_prove_commit_open_comm_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (comm (num (commit 123))))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 8, None);
    }

    #[test]
    fn test_prove_commit_secret_comm_num() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (comm (num (commit 123))))";
        let expected = s.num(0);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 8, None);
    }

    #[test]
    fn test_prove_commit_num_open() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open (num (commit 123)))";
        let expected = s.num(123);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 6, None);
    }

    #[test]
    fn test_prove_num_invalid_tag() {
        let s = &mut Store::<Fr>::default();
        let expr = "(num (quote x))";
        let expr1 = "(num \"asdf\")";
        let expr2 = "(num '(1))";
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr1, None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, None, None, Some(error), None, 2, None);
    }

    #[test]
    fn test_prove_comm_invalid_tag() {
        let s = &mut Store::<Fr>::default();
        let expr = "(comm (quote x))";
        let expr1 = "(comm \"asdf\")";
        let expr2 = "(comm '(1))";
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr1, None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, None, None, Some(error), None, 2, None);
    }

    #[test]
    fn test_prove_char_invalid_tag() {
        let s = &mut Store::<Fr>::default();
        let expr = "(char (quote x))";
        let expr1 = "(char \"asdf\")";
        let expr2 = "(char '(1))";
        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr1, None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, None, None, Some(error), None, 2, None);
    }

    #[test]
    fn test_prove_terminal_sym() {
        let s = &mut Store::<Fr>::default();
        let expr = "(quote x)";
        let x = s.user_sym("x");
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(x), None, Some(terminal), None, 1, None);
    }

    #[test]
    #[should_panic = "hidden value could not be opened"]
    fn test_prove_open_opaque_commit() {
        let s = &mut Store::<Fr>::default();
        let expr = "(open 123)";
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, None, None, 2, None);
    }

    #[test]
    #[should_panic]
    fn test_prove_secret_invalid_tag() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret 123)";
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, None, None, 2, None);
    }

    #[test]
    #[should_panic = "secret could not be extracted"]
    fn test_prove_secret_opaque_commit() {
        let s = &mut Store::<Fr>::default();
        let expr = "(secret (comm 123))";
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, None, None, 2, None);
    }

    #[test]
    fn test_str_car_cdr_cons() {
        let s = &mut Store::<Fr>::default();
        let a = s.read(r"#\a").unwrap();
        let apple = s.read(r#" "apple" "#).unwrap();
        let a_pple = s.read(r#" (#\a . "pple") "#).unwrap();
        let pple = s.read(r#" "pple" "#).unwrap();
        let empty = s.intern_string("");
        let nil = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();
        let error = s.get_cont_error();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(car "apple")"#,
            Some(a),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(cdr "apple")"#,
            Some(pple),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(car "")"#,
            Some(nil),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(cdr "")"#,
            Some(empty),
            None,
            Some(terminal),
            None,
            2,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(cons #\a "pple")"#,
            Some(a_pple),
            None,
            Some(terminal),
            None,
            3,
            None,
        );

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(strcons #\a "pple")"#,
            Some(apple),
            None,
            Some(terminal),
            None,
            3,
            None,
        );

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r"(strcons #\a #\b)",
            None,
            None,
            Some(error),
            None,
            3,
            None,
        );

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(strcons "a" "b")"#,
            None,
            None,
            Some(error),
            None,
            3,
            None,
        );

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            r#"(strcons 1 2)"#,
            None,
            None,
            Some(error),
            None,
            3,
            None,
        );
    }

    fn relational_aux(s: &mut Store<Fr>, op: &str, a: &str, b: &str, res: bool) {
        let expr = &format!("({op} {a} {b})");
        let expected = if res {
            lurk_sym_ptr!(s, t)
        } else {
            lurk_sym_ptr!(s, nil)
        };
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
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
        let t = lurk_sym_ptr!(s, t);
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(t), None, Some(terminal), None, 19, None);
    }

    #[test]
    fn test_prove_test_eval() {
        let s = &mut Store::<Fr>::default();
        let expr = "(* 3 (eval  (cons '+ (cons 1 (cons 2 nil)))))";
        let expr2 = "(* 5 (eval '(+ 1 a) '((a . 3))))"; // two-arg eval, optional second arg is env.
        let res = s.num(9);
        let res2 = s.num(20);
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 17, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res2), None, Some(terminal), None, 9, None);
    }

    #[test]
    fn test_prove_test_keyword() {
        let s = &mut Store::<Fr>::default();

        let expr = ":asdf";
        let expr2 = "(eq :asdf :asdf)";
        let expr3 = "(eq :asdf 'asdf)";
        let res = s.key("asdf");
        let res2 = lurk_sym_ptr!(s, t);
        let res3 = lurk_sym_ptr!(s, nil);

        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 1, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr3, Some(res3), None, Some(terminal), None, 3, None);
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

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 25, None);
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

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 108, None);
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

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 152, None);
    }

    #[test]
    fn test_prove_test_lambda_args_regression() {
        let s = &mut Store::<Fr>::default();

        let expr = "(cons (lambda (x y) nil) nil)";
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(terminal), None, 3, None);
    }

    #[test]
    fn test_prove_reduce_sym_contradiction_regression() {
        let s = &mut Store::<Fr>::default();

        let expr = "(eval 'a '(nil))";
        let error = s.get_cont_error();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 4, None);
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
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(terminal), None, 3, None);
    }

    #[test]
    fn test_prove_test_self_eval_nil() {
        let s = &mut Store::<Fr>::default();

        // nil doesn't have SYM tag
        let expr = "nil";

        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(terminal), None, 1, None);
    }

    #[test]
    fn test_prove_test_env_not_nil_and_binding_nil() {
        let s = &mut Store::<Fr>::default();

        let expr = "(let ((a 1) (b 2)) c)";

        let error = s.get_cont_error();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 7, None);
    }

    #[test]
    fn test_prove_test_eval_bad_form() {
        let s = &mut Store::<Fr>::default();
        let expr = "(* 5 (eval '(+ 1 a) '((0 . 3))))"; // two-arg eval, optional second arg is env. This tests for error on malformed env.
        let error = s.get_cont_error();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 8, None);
    }

    #[test]
    fn test_prove_test_u64_self_evaluating() {
        let s = &mut Store::<Fr>::default();

        let expr = "123u64";
        let res = s.uint64(123);
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 1, None);
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

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 7, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr3, Some(res), None, Some(terminal), None, 6, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr4, Some(res2), None, Some(terminal), None, 2, None);
    }

    #[test]
    fn test_prove_test_u64_add() {
        let s = &mut Store::<Fr>::default();

        let expr = "(+ 18446744073709551615u64 2u64)";
        let expr2 = "(+ (- 0u64 1u64) 2u64)";
        let res = s.uint64(1);
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res), None, Some(terminal), None, 6, None);
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

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr3, Some(res3), None, Some(terminal), None, 6, None);
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

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr3, None, None, Some(error), None, 3, None);
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

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr3, None, None, Some(error), None, 3, None);
    }

    #[test]
    fn test_prove_test_num_mod() {
        let s = &mut Store::<Fr>::default();

        let expr = "(% 100 3)";
        let expr2 = "(% 100 3u64)";
        let expr3 = "(% 100u64 3)";

        let error = s.get_cont_error();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, None, None, Some(error), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr3, None, None, Some(error), None, 3, None);
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

        let t = lurk_sym_ptr!(s, t);
        let nil = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(t), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(nil), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr3, Some(t), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr4, Some(nil), None, Some(terminal), None, 3, None);

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr5, Some(nil), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr6, Some(t), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr7, Some(nil), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr8, Some(t), None, Some(terminal), None, 3, None);

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr9, Some(t), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr10, Some(t), None, Some(terminal), None, 3, None);
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
        let res3 = s.intern_u64(2);
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res), None, Some(terminal), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr3, Some(res2), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr4, Some(res3), None, Some(terminal), None, 5, None);
    }

    #[test]
    fn test_prove_test_u64_num_comparison() {
        let s = &mut Store::<Fr>::default();

        let expr = "(= 1 1u64)";
        let expr2 = "(= 1 2u64)";
        let t = lurk_sym_ptr!(s, t);
        let nil = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(t), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(nil), None, Some(terminal), None, 3, None);
    }

    #[test]
    fn test_prove_test_u64_num_cons() {
        let s = &mut Store::<Fr>::default();

        let expr = "(cons 1 1u64)";
        let expr2 = "(cons 1u64 1)";
        let res = s.read("(1 . 1u64)").unwrap();
        let res2 = s.read("(1u64 . 1)").unwrap();
        let terminal = s.get_cont_terminal();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
    }

    #[test]
    fn test_prove_test_hide_u64_secret() {
        let s = &mut Store::<Fr>::default();

        let expr = "(hide 0u64 123)";
        let error = s.get_cont_error();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 3, None);
    }

    #[test]
    fn test_prove_test_mod_by_zero_error() {
        let s = &mut Store::<Fr>::default();

        let expr = "(% 0 0)";
        let error = s.get_cont_error();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 3, None);
    }

    #[test]
    fn test_prove_dotted_syntax_error() {
        let s = &mut Store::<Fr>::default();
        let expr = "(let ((a (lambda (x) (+ x 1)))) (a . 1))";
        let error = s.get_cont_error();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, expr, None, None, Some(error), None, 3, None);
    }

    #[test]
    fn test_prove_call_literal_fun() {
        let s = &mut Store::<Fr>::default();
        let empty_env = lurk_sym_ptr!(s, nil);
        let arg = s.user_sym("x");
        let body = s.read("((+ x 1))").unwrap();
        let fun = s.intern_fun(arg, body, empty_env);
        let input = s.num(9);
        let expr = s.list(&[fun, input]);
        let res = s.num(10);
        let terminal = s.get_cont_terminal();
        let lang: Arc<Lang<Fr, Coproc<Fr>>> = Arc::new(Lang::new());

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
            lang,
        );
    }

    #[test]
    fn test_prove_lambda_body_syntax() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();

        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, "((lambda ()))", None, None, Some(error), None, 2, None);
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda () 1 2))",
            None,
            None,
            Some(error),
            None,
            2,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda (x)) 1)",
            None,
            None,
            Some(error),
            None,
            3,
            None,
        );
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda (x) 1 2) 1)",
            None,
            None,
            Some(error),
            None,
            3,
            None,
        );
    }

    #[test]
    #[ignore]
    fn test_prove_non_symbol_binding_error() {
        let s = &mut Store::<Fr>::default();
        let error = s.get_cont_error();

        let mut test = |x| {
            let expr = format!("(let (({x} 123)) {x})");
            let expr2 = format!("(letrec (({x} 123)) {x})");
            let expr3 = format!("(lambda ({x}) {x})");

            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr2, None, None, Some(error), None, 1, None);
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr3, None, None, Some(error), None, 1, None);
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

        let hash_num = |s: &mut Store<Fr>, state: Rc<RefCell<State>>, name| {
            let sym = s.read_with_state(state, name).unwrap();
            let z_ptr = s.hash_expr(&sym).unwrap();
            let hash = *z_ptr.value();
            Num::Scalar(hash)
        };

        let state = State::init_lurk_state().rccell();
        {
            // binop
            let expr = format!("({} 1 1)", hash_num(s, state.clone(), "+"));
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
        }
        {
            // unop
            let expr = format!("({} '(1 . 2))", hash_num(s, state.clone(), "car"));
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
        }
        {
            // let_or_letrec
            let expr = format!("({} ((a 1)) a)", hash_num(s, state.clone(), "let"));
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
        }
        {
            // current-env
            let expr = format!("({})", hash_num(s, state.clone(), "current-env"));
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
        }
        {
            // lambda
            let expr = format!("({} (x) 123)", hash_num(s, state.clone(), "lambda"));
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
        }
        {
            // quote
            let expr = format!("({} asdf)", hash_num(s, state.clone(), "quote"));
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
        }
        {
            // if
            let expr = format!("({} t 123 456)", hash_num(s, state, "if"));
            test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(s, &expr, None, None, Some(error), None, 1, None);
        }
    }

    #[test]
    fn test_dumb_lang() {
        use crate::coprocessor::test::DumbCoprocessor;
        use crate::eval::tests::coproc::DumbCoproc;

        let s = &mut Store::<Fr>::new();

        let mut lang = Lang::<Fr, DumbCoproc<Fr>>::new();
        let name = user_sym("cproc-dumb");
        let dumb = DumbCoprocessor::new();
        let coproc = DumbCoproc::DC(dumb);

        lang.add_coprocessor(name, coproc, s);

        // 9^2 + 8 = 89
        let expr = "(cproc-dumb 9 8)";

        // The dumb coprocessor cannot be shadowed.
        let expr2 = "(let ((cproc-dumb (lambda (a b) (* a b))))
                   (cproc-dumb 9 8))";

        let expr3 = "(cproc-dumb 9 8 123)";
        let expr4 = "(cproc-dumb 9)";

        let res = s.num(89);
        let error = s.get_cont_error();
        let lang = Arc::new(lang);

        test_aux(s, expr, Some(res), None, None, None, 1, Some(lang.clone()));
        test_aux(s, expr2, Some(res), None, None, None, 3, Some(lang.clone()));
        test_aux(
            s,
            expr3,
            None,
            None,
            Some(error),
            None,
            1,
            Some(lang.clone()),
        );
        test_aux(s, expr4, None, None, Some(error), None, 1, Some(lang));
    }

    // This is related to issue #426
    #[test]
    fn test_prove_lambda_body_nil() {
        let s = &mut Store::<Fr>::default();
        let expected = lurk_sym_ptr!(s, nil);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "((lambda (x) nil) 0)",
            Some(expected),
            None,
            Some(terminal),
            None,
            4,
            None,
        );
    }

    // The following 3 tests are related to issue #424
    #[test]
    fn test_letrec_let_nesting() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(2);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec ((x (let ((z 0)) 1))) 2)",
            Some(expected),
            None,
            Some(terminal),
            None,
            6,
            None,
        );
    }
    #[test]
    fn test_let_sequencing() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(1);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(let ((x 0) (y x)) 1)",
            Some(expected),
            None,
            Some(terminal),
            None,
            5,
            None,
        );
    }
    #[test]
    fn test_letrec_sequencing() {
        let s = &mut Store::<Fr>::default();
        let expected = s.num(3);
        let terminal = s.get_cont_terminal();
        test_aux::<_, _, C1<'_, Fr, Coproc<Fr>>>(
            s,
            "(letrec ((x 0) (y (letrec ((inner 1)) 2))) 3)",
            Some(expected),
            None,
            Some(terminal),
            None,
            8,
            None,
        );
    }
}
