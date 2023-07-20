use serde::{Deserialize, Serialize};

use lurk::{
    coprocessor::Coprocessor,
    eval::lang::{Coproc, Lang},
    field::LurkField,
    proof::nova,
    z_ptr::{ZContPtr, ZExprPtr},
    z_store::ZStore,
};

use super::field_data::HasFieldModulus;

/// Carries extra information to help with visualization, experiments etc.
///
/// Note: the `ZStore` in this struct only has enough data to recover the meaning
/// of the claim being proven: `expression`, when evaluated in the context of
/// `environment`, is reduced to `result`. It doesn't contain private data.
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

type Pallas = pasta_curves::pallas::Scalar; // TODO: generalize this

/// Minimal data structure containing just enough for proof verification
#[derive(Serialize, Deserialize)]
pub enum LurkProof<'a, F: LurkField>
where
    Coproc<F>: Coprocessor<Pallas>,
{
    Nova {
        proof: nova::Proof<'a, Coproc<F>>,
        public_inputs: Vec<F>,
        public_outputs: Vec<F>,
        num_steps: usize,
        rc: usize,
        lang: Lang<F, Coproc<F>>,
    },
}

impl<'a, F: LurkField> HasFieldModulus for LurkProof<'a, F>
where
    Coproc<F>: Coprocessor<Pallas>,
{
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

#[cfg(not(target_arch = "wasm32"))]
mod non_wasm {
    use crate::cli::{
        field_data::non_wasm::{dump, load},
        paths::non_wasm::{proof_meta_path, proof_path},
    };
    use anyhow::Result;
    use lurk::{
        coprocessor::Coprocessor, eval::lang::Coproc, field::LurkField,
        public_parameters::public_params,
    };
    use serde::Serialize;

    use super::{LurkProof, LurkProofMeta, Pallas};

    impl<F: LurkField + Serialize> LurkProofMeta<F> {
        #[inline]
        pub fn persist(self, id: &str) -> Result<()> {
            dump(self, proof_meta_path(id))
        }
    }

    impl<'a, F: LurkField + Serialize> LurkProof<'a, F>
    where
        Coproc<F>: Coprocessor<Pallas>,
    {
        #[inline]
        pub fn persist(self, id: &str) -> Result<()> {
            dump(self, proof_path(id))
        }
    }

    impl<'a> LurkProof<'a, Pallas> {
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
                    let pp = public_params(rc, std::sync::Arc::new(lang))?;
                    Ok(proof.verify(&pp, num_steps, &public_inputs, &public_outputs)?)
                }
            }
        }

        pub fn verify_proof(proof_id: &str) -> Result<()> {
            let lurk_proof: LurkProof<'_, Pallas> = load(proof_path(proof_id))?;
            if lurk_proof.verify()? {
                println!("✓ Proof \"{proof_id}\" verified");
            } else {
                println!("✗ Proof \"{proof_id}\" failed on verification");
            }
            Ok(())
        }
    }
}
