use serde::{Deserialize, Serialize};

use lurk::{
    coprocessor::Coprocessor,
    eval::lang::{Coproc, Lang},
    field::LurkField,
    proof::nova::{self, CurveCycleEquipped},
    z_ptr::{ZContPtr, ZExprPtr},
    z_store::ZStore,
};

use super::field_data::HasFieldModulus;

/// Carries extra information to help with visualization, experiments etc.
///
/// Note: the `ZStore` in this struct only has enough data to recover the meaning
/// of the claim being proven: `expr`, when evaluated in the context of `env` and
/// continuation `cont`, is reduced to `expr_out`, resulting on environment
/// `env_out` and continuation `cont_out`. It doesn't contain private data.
#[derive(Serialize, Deserialize)]
pub struct LurkProofMeta<F: LurkField> {
    pub(crate) iterations: usize,
    pub(crate) expr: ZExprPtr<F>,
    pub(crate) env: ZExprPtr<F>,
    pub(crate) cont: ZContPtr<F>,
    pub(crate) expr_out: ZExprPtr<F>,
    pub(crate) env_out: ZExprPtr<F>,
    pub(crate) cont_out: ZContPtr<F>,
    pub(crate) zstore: ZStore<F>,
}

impl<F: LurkField> HasFieldModulus for LurkProofMeta<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

/// Minimal data structure containing just enough for proof verification
#[derive(Serialize, Deserialize)]
pub enum LurkProof<'a, F: CurveCycleEquipped>
where
    Coproc<F>: Coprocessor<F>,
{
    Nova {
        proof: nova::Proof<'a, F, Coproc<F>>,
        public_inputs: Vec<F>,
        public_outputs: Vec<F>,
        num_steps: usize,
        rc: usize,
        lang: Lang<F, Coproc<F>>,
    },
}

impl<'a, F: CurveCycleEquipped> HasFieldModulus for LurkProof<'a, F>
where
    Coproc<F>: Coprocessor<F>,
{
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

use crate::cli::{
    field_data::{dump, load},
    paths::{proof_meta_path, proof_path, public_params_dir},
};
use anyhow::Result;
use lurk::public_parameters::public_params;

use pasta_curves::pallas::Scalar;

impl<F: LurkField + Serialize> LurkProofMeta<F> {
    #[inline]
    pub fn persist(self, proof_key: &str) -> Result<()> {
        dump(self, proof_meta_path(proof_key))
    }
}

impl<'a, F: CurveCycleEquipped + Serialize> LurkProof<'a, F>
where
    Coproc<F>: Coprocessor<F>,
{
    #[inline]
    pub fn persist(self, proof_key: &str) -> Result<()> {
        dump(self, proof_path(proof_key))
    }
}

impl<'a> LurkProof<'a, Scalar> {
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
                log::info!("Loading public parameters");
                let pp = public_params(rc, std::sync::Arc::new(lang), &public_params_dir())?;
                Ok(proof.verify(&pp, num_steps, &public_inputs, &public_outputs)?)
            }
        }
    }

    pub fn verify_proof(proof_key: &str) -> Result<()> {
        let lurk_proof: LurkProof<'_, Scalar> = load(proof_path(proof_key))?;
        if lurk_proof.verify()? {
            println!("✓ Proof \"{proof_key}\" verified");
        } else {
            println!("✗ Proof \"{proof_key}\" failed on verification");
        }
        Ok(())
    }
}
