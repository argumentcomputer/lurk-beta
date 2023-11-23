use ::nova::{
    supernova::NonUniformCircuit,
    traits::{circuit_supernova::StepCircuit as SuperStepCircuit, Engine},
};
use abomonation::Abomonation;
use anyhow::{bail, Result};
use camino::Utf8PathBuf;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{collections::HashMap, sync::Arc};

use crate::{
    coprocessor::Coprocessor,
    eval::lang::Lang,
    field::LurkField,
    lem::{pointers::ZPtr, store::Store},
    proof::{
        nova::{self, CurveCycleEquipped, E1, E2},
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
    zstore::ZDag,
};

/// Carries information to help with visualization
#[derive(Serialize, Deserialize)]
pub(crate) struct LurkProofMeta<F: LurkField> {
    pub(crate) iterations: usize,
    pub(crate) expr_io: (ZPtr<F>, ZPtr<F>),
    pub(crate) env_io: Option<(ZPtr<F>, ZPtr<F>)>,
    pub(crate) cont_io: (ZPtr<F>, ZPtr<F>),
    pub(crate) z_dag: ZDag<F>,
}

impl<F: LurkField> HasFieldModulus for LurkProofMeta<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

impl<F: LurkField> LurkProofMeta<F> {
    fn without_envs(self) -> Result<Self> {
        if self.env_io.is_none() {
            return Ok(self);
        }
        let Self {
            iterations,
            expr_io: (expr, expr_out),
            env_io: _,
            cont_io: (cont, cont_out),
            z_dag,
        } = self;
        // creating a new `ZDag` without data from envs
        let z_dag = z_dag.filtered(&[&expr, &expr_out, &cont, &cont_out])?;
        Ok(Self {
            iterations,
            expr_io: (expr, expr_out),
            env_io: None,
            cont_io: (cont, cont_out),
            z_dag,
        })
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
        let Ok(proof_meta) = load::<Self>(&proof_meta_path(proof_key)) else {
            bail!("Missing or corrupted proof meta file. Prove again to regenerate.")
        };
        let do_inspect = |store: &Store<F>, state: &State| {
            let mut cache = HashMap::default();
            let z_dag = &proof_meta.z_dag;
            let (expr, expr_out) = &proof_meta.expr_io;
            let expr = z_dag.populate_store(expr, store, &mut cache)?;
            let expr_out = z_dag.populate_store(expr_out, store, &mut cache)?;
            if full {
                let envs = match &proof_meta.env_io {
                    Some((env, env_out)) => Some((
                        z_dag.populate_store(env, store, &mut cache)?,
                        z_dag.populate_store(env_out, store, &mut cache)?,
                    )),
                    None => None,
                };
                let (cont, cont_out) = &proof_meta.cont_io;
                let cont = z_dag.populate_store(cont, store, &mut cache)?;
                let cont_out = z_dag.populate_store(cont_out, store, &mut cache)?;
                if let Some((env, env_out)) = envs {
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
                        "Input:\n  Expr: {}\n  Cont: {}",
                        expr.fmt_to_string(store, state),
                        cont.fmt_to_string(store, state),
                    );
                    println!(
                        "Output:\n  Expr: {}\n  Cont: {}",
                        expr_out.fmt_to_string(store, state),
                        cont_out.fmt_to_string(store, state),
                    );
                }
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

/// Minimal data structure containing just enough for proof verification
#[non_exhaustive]
#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: DeserializeOwned"))]
pub(crate) enum LurkProof<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + Serialize + DeserializeOwned,
    M: MultiFrameTrait<'a, F, C>,
> where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    Nova {
        proof: nova::Proof<'a, F, C, M>,
        public_inputs: Vec<F>,
        public_outputs: Vec<F>,
        num_steps: usize,
        rc: usize,
        lang: Lang<F, C>,
    },
}

impl<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'a + Serialize + DeserializeOwned,
        M: MultiFrameTrait<'a, F, C>,
    > HasFieldModulus for LurkProof<'a, F, C, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

impl<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F> + Serialize + DeserializeOwned,
        M: MultiFrameTrait<'a, F, C>,
    > LurkProof<'a, F, C, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    #[inline]
    fn public_io(&self) -> (&[F], &[F]) {
        match self {
            Self::Nova {
                proof: _,
                public_inputs,
                public_outputs,
                ..
            } => (public_inputs, public_outputs),
        }
    }

    fn matches_meta(&self, meta: &LurkProofMeta<F>) -> bool {
        let (public_input, public_output) = self.public_io();
        let matches_exprs = {
            let (expr, expr_out) = &meta.expr_io;
            public_input[0] == expr.tag_field()
                && &public_input[1] == expr.value()
                && public_output[0] == expr_out.tag_field()
                && &public_output[1] == expr_out.value()
        };
        let matches_envs = {
            if let Some((env, env_out)) = &meta.env_io {
                public_input[2] == env.tag_field()
                    && &public_input[3] == env.value()
                    && public_output[2] == env_out.tag_field()
                    && &public_output[3] == env_out.value()
            } else {
                // no data to trigger inconsistency
                true
            }
        };
        let matches_conts = {
            let (cont, cont_out) = &meta.cont_io;
            public_input[4] == cont.tag_field()
                && &public_input[5] == cont.value()
                && public_output[4] == cont_out.tag_field()
                && &public_output[5] == cont_out.value()
        };
        matches_exprs && matches_envs && matches_conts
    }
}

impl<
        'a,
        F: CurveCycleEquipped + Serialize,
        C: Coprocessor<F> + Serialize + DeserializeOwned,
        M: MultiFrameTrait<'a, F, C>,
    > LurkProof<'a, F, C, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    #[inline]
    pub(crate) fn persist(self, proof_key: &str) -> Result<()> {
        dump(self, &proof_path(proof_key))
    }
}

impl<
        F: CurveCycleEquipped + DeserializeOwned,
        C: Coprocessor<F> + Serialize + DeserializeOwned + 'static,
        M: MultiFrameTrait<'static, F, C>
            + SuperStepCircuit<F>
            + NonUniformCircuit<E1<F>, E2<F>, M, C2<F>>
            + 'static,
    > LurkProof<'static, F, C, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pub(crate) fn verify_proof(proof_key: &str) -> Result<()> {
        let lurk_proof = load::<Self>(&proof_path(proof_key))?;
        if lurk_proof.verify()? {
            println!("✓ Proof \"{proof_key}\" verified");
        } else {
            println!("✗ Proof \"{proof_key}\" failed on verification");
        }
        Ok(())
    }

    #[inline]
    pub(crate) fn is_cached(proof_key: &str) -> bool {
        load::<Self>(&proof_path(proof_key)).is_ok()
    }

    fn verify(&self) -> Result<bool> {
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
                let instance =
                    Instance::new(*rc, Arc::new(lang.clone()), true, Kind::NovaPublicParams);
                let pp = public_params(&instance)?;
                Ok(proof.verify(&pp, *num_steps, public_inputs, public_outputs)?)
            }
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: DeserializeOwned"))]
pub(crate) struct PackedLurkProof<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + Serialize + DeserializeOwned,
    M: MultiFrameTrait<'a, F, C>,
> where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    proof: LurkProof<'a, F, C, M>,
    meta: Option<LurkProofMeta<F>>,
    key: String,
}

impl<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'a + Serialize + DeserializeOwned,
        M: MultiFrameTrait<'a, F, C>,
    > HasFieldModulus for PackedLurkProof<'a, F, C, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

impl<
        F: CurveCycleEquipped + Serialize + DeserializeOwned,
        C: Coprocessor<F> + 'static + Serialize + DeserializeOwned,
        M: MultiFrameTrait<'static, F, C>
            + SuperStepCircuit<F>
            + NonUniformCircuit<E1<F>, E2<F>, M, C2<F>>
            + 'static,
    > PackedLurkProof<'static, F, C, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pub(crate) fn pack(
        proof_key: String,
        path: &Utf8PathBuf,
        exclude_meta: bool,
        include_envs: bool,
    ) -> Result<()> {
        let proof: LurkProof<'_, F, C, M> = load(&proof_path(&proof_key))?;
        let meta = if exclude_meta {
            None
        } else {
            let meta: LurkProofMeta<F> = load(&proof_meta_path(&proof_key))?;
            if include_envs {
                Some(meta)
            } else {
                Some(meta.without_envs()?)
            }
        };
        let packed_proof = PackedLurkProof {
            proof,
            meta,
            key: proof_key,
        };
        dump(packed_proof, path)
    }

    pub(crate) fn unpack(path: &Utf8PathBuf) -> Result<()> {
        let PackedLurkProof { proof, meta, key } = load::<Self>(path)?;
        if !proof.verify()? {
            bail!("Proof verification failed")
        }
        if let Some(meta) = meta {
            if !proof.matches_meta(&meta) {
                bail!("Meta data is incompatible with the proof")
            }
            meta.persist(&key)?;
        }
        proof.persist(&key)?;
        println!("Proof {key} unpacked");
        Ok(())
    }
}
