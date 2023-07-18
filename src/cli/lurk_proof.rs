use serde::{Deserialize, Serialize};

use anyhow::Result;

use lurk::{
    eval::{
        lang::{Coproc, Lang},
        Status,
    },
    field::LurkField,
    proof::nova,
    public_parameters::public_params,
    z_ptr::ZExprPtr,
    z_store::ZStore,
};

#[cfg(not(target_arch = "wasm32"))]
use std::{fs::File, io::BufReader, io::BufWriter};

#[cfg(not(target_arch = "wasm32"))]
use super::{
    field_data::FieldData,
    paths::{proof_meta_path, proof_path},
};

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

impl<F: LurkField + Serialize> LurkProofMeta<F> {
    #[cfg(not(target_arch = "wasm32"))]
    pub fn persist(&self, id: &str) -> Result<()> {
        let fd = &FieldData::wrap::<F, LurkProofMeta<F>>(self)?;
        bincode::serialize_into(BufWriter::new(&File::create(proof_meta_path(id))?), fd)?;
        Ok(())
    }
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
    #[cfg(not(target_arch = "wasm32"))]
    pub fn persist(&self, id: &str) -> Result<()> {
        let fd = &FieldData::wrap::<F, LurkProof<'_>>(self)?;
        bincode::serialize_into(BufWriter::new(&File::create(proof_path(id))?), fd)?;
        Ok(())
    }

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
        let file = File::open(proof_path(proof_id))?;
        let fd: FieldData = bincode::deserialize_from(BufReader::new(file))?;
        let lurk_proof: LurkProof = fd.extract()?;
        Self::print_verification(proof_id, lurk_proof.verify()?);
        Ok(())
    }
}
