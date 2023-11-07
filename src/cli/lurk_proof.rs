use std::{collections::HashMap, sync::Arc};

use ::nova::{
    supernova::NonUniformCircuit,
    traits::{circuit_supernova::StepCircuit as SuperStepCircuit, Group},
};
use abomonation::Abomonation;
use anyhow::Result;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

use crate::{
    coprocessor::Coprocessor,
    eval::lang::{Coproc, Lang},
    field::LurkField,
    lem::{pointers::ZPtr, store::Store},
    proof::{
        nova::{self, CurveCycleEquipped, G1, G2},
        supernova::C2,
        MultiFrameTrait,
    },
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
    state::{initial_lurk_state, State},
};

use super::{
    field_data::{dump, load, HasFieldModulus},
    paths::{proof_meta_path, proof_path},
    zstore::{populate_store, ZStore},
};

/// Carries extra information to help with visualization, experiments etc.
///
/// Note: the `ZStore` in this struct only has enough data to recover the meaning
/// of the claim being proven: `expr`, when evaluated in the context of `env` and
/// continuation `cont`, is reduced to `expr_out`, resulting on environment
/// `env_out` and continuation `cont_out`. It doesn't contain private data.
#[derive(Serialize, Deserialize)]
pub(crate) struct LurkProofMeta<F: LurkField> {
    pub(crate) iterations: usize,
    pub(crate) expr: ZPtr<F>,
    pub(crate) env: ZPtr<F>,
    pub(crate) cont: ZPtr<F>,
    pub(crate) expr_out: ZPtr<F>,
    pub(crate) env_out: ZPtr<F>,
    pub(crate) cont_out: ZPtr<F>,
    pub(crate) z_store: ZStore<F>,
}

impl<F: LurkField> HasFieldModulus for LurkProofMeta<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

/// Minimal data structure containing just enough for proof verification
#[non_exhaustive]
#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: DeserializeOwned"))]
pub(crate) enum LurkProof<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F>,
    M: MultiFrameTrait<'a, F, C>,
> where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    Nova {
        proof: nova::Proof<'a, F, C, M>,
        public_inputs: Vec<F>,
        public_outputs: Vec<F>,
        num_steps: usize,
        rc: usize,
        lang: Lang<F, Coproc<F>>,
    },
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>>
    HasFieldModulus for LurkProof<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

impl<F: LurkField + Serialize> LurkProofMeta<F> {
    #[inline]
    pub(crate) fn persist(self, proof_key: &str) -> Result<()> {
        dump(self, &proof_meta_path(proof_key))
    }
}

impl<F: LurkField + DeserializeOwned> LurkProofMeta<F> {
    pub(crate) fn inspect_proof(
        proof_key: &str,
        store_state: Option<(&Store<F>, &State)>,
        full: bool,
    ) -> Result<()> {
        let proof_meta: LurkProofMeta<F> = load(&proof_meta_path(proof_key))?;
        let do_inspect = |store: &Store<F>, state: &State| {
            let mut cache = HashMap::default();
            let z_store = &proof_meta.z_store;
            let expr = populate_store(store, &proof_meta.expr, z_store, &mut cache)?;
            let expr_out = populate_store(store, &proof_meta.expr_out, z_store, &mut cache)?;
            if full {
                let env = populate_store(store, &proof_meta.env, z_store, &mut cache)?;
                let cont = populate_store(store, &proof_meta.cont, z_store, &mut cache)?;
                let env_out = populate_store(store, &proof_meta.env_out, z_store, &mut cache)?;
                let cont_out = populate_store(store, &proof_meta.cont_out, z_store, &mut cache)?;
                println!(
                    "Input:\n  Expr: {}\n  Env:  {}\n  Cont: {}",
                    expr.fmt_to_string(store, state),
                    env.fmt_to_string(store, state),
                    cont.fmt_to_string(store, state),
                );
                println!(
                    "Output:\n  Expr: {}\n  Env:  {}\n  Cont: {}",
                    expr_out.fmt_to_string(store, state),
                    env_out.fmt_to_string(store, state),
                    cont_out.fmt_to_string(store, state),
                );
            } else {
                println!(
                    "Input:\n  {}\nOutput:\n  {}",
                    expr.fmt_to_string(store, state),
                    expr_out.fmt_to_string(store, state)
                );
            }
            println!("Iterations: {}", proof_meta.iterations);
            Ok(())
        };
        if let Some((store, state)) = store_state {
            do_inspect(store, state)
        } else {
            do_inspect(&Store::default(), initial_lurk_state())
        }
    }
}

impl<'a, F: CurveCycleEquipped + Serialize, M: MultiFrameTrait<'a, F, Coproc<F>>>
    LurkProof<'a, F, Coproc<F>, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    #[inline]
    pub(crate) fn persist(self, proof_key: &str) -> Result<()> {
        dump(self, &proof_path(proof_key))
    }
}

impl<
        F: CurveCycleEquipped + DeserializeOwned,
        M: MultiFrameTrait<'static, F, Coproc<F>>
            + SuperStepCircuit<F>
            + NonUniformCircuit<G1<F>, G2<F>, M, C2<F>>
            + 'static,
    > LurkProof<'static, F, Coproc<F>, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pub(crate) fn verify_proof(proof_key: &str) -> Result<()> {
        let lurk_proof: LurkProof<'_, F, Coproc<F>, M> = load(&proof_path(proof_key))?;
        if lurk_proof.verify()? {
            println!("✓ Proof \"{proof_key}\" verified");
        } else {
            println!("✗ Proof \"{proof_key}\" failed on verification");
        }
        Ok(())
    }

    fn verify(self) -> Result<bool> {
        match self {
            Self::Nova {
                proof,
                public_inputs,
                public_outputs,
                num_steps,
                rc,
                lang,
            } => {
                tracing::info!("Loading public parameters");
                let instance = Instance::new(rc, Arc::new(lang), true, Kind::NovaPublicParams);
                let pp = public_params(&instance)?;
                Ok(proof.verify(&pp, num_steps, &public_inputs, &public_outputs)?)
            }
        }
    }
}
