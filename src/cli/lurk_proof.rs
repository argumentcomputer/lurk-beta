use serde::{Deserialize, Serialize};

use anyhow::Result;

use lurk::{
    eval::{
        lang::{Coproc, Lang},
        Status,
    },
    field::{LanguageField, LurkField},
    proof::nova,
    public_parameters::public_params,
    z_ptr::ZExprPtr,
    z_store::ZStore,
};

/// A wrapper for data whose deserialization depends on a certain LurkField
#[derive(Serialize, Deserialize)]
pub struct FieldData {
    field: LanguageField,
    data: Vec<u8>,
}

#[allow(dead_code)]
impl FieldData {
    #[inline]
    pub fn wrap<F: LurkField, T: Serialize>(t: &T) -> Result<Self> {
        Ok(Self {
            field: F::FIELD,
            data: bincode::serialize(t)?,
        })
    }

    #[inline]
    pub fn open<'a, T: Deserialize<'a>>(&'a self) -> Result<T> {
        Ok(bincode::deserialize(&self.data)?)
    }
}

/// Carries extra information to help with visualization, experiments etc
#[derive(Serialize, Deserialize)]
pub struct LurkProofMeta<F: LurkField> {
    pub iterations: usize,
    pub evaluation_cost: u128,
    pub generation_cost: u128,
    pub compression_cost: u128,
    pub status: Status,
    pub expression: ZExprPtr<F>,
    pub environment: ZExprPtr<F>,
    pub result: ZExprPtr<F>,
    pub zstore: ZStore<F>,
}

type F = pasta_curves::pallas::Scalar; // TODO: generalize this

/// Minimal data structure containing just enough for proof verification
#[derive(Serialize, Deserialize)]
pub enum LurkProof<'a> {
    Nova {
        proof: nova::Proof<'a, Coproc<F>>,
        public_inputs: Vec<F>,
        public_outputs: Vec<F>,
        num_steps: usize,
        rc: usize,
        lang: Lang<F, Coproc<F>>,
    },
}

impl<'a> LurkProof<'a> {
    #[allow(dead_code)]
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

    #[allow(dead_code)]
    fn print_verification(proof_id: &str, success: bool) {
        if success {
            println!("✓ Proof \"{proof_id}\" verified");
        } else {
            println!("✗ Proof \"{proof_id}\" failed on verification");
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    pub fn verify_proof(proof_id: &str) -> Result<()> {
        use super::paths::proof_path;
        use std::{fs::File, io::BufReader};

        let file = File::open(proof_path(proof_id))?;
        let fd: FieldData = bincode::deserialize_from(BufReader::new(file))?;
        let lurk_proof: LurkProof = fd.open()?;
        Self::print_verification(proof_id, lurk_proof.verify()?);
        Ok(())
    }
}
