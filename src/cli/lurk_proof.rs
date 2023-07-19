use serde::{Deserialize, Serialize};

use lurk::{
    coprocessor::Coprocessor,
    eval::{
        lang::{Coproc, Lang},
        Status,
    },
    field::LurkField,
    proof::nova,
    z_ptr::ZExprPtr,
    z_store::ZStore,
};

/// Carries extra information to help with visualization, experiments etc.
///
/// Note: the `ZStore` in this struct only has enough data to recover the meaning
/// of the claim being proven: `expression`, when evaluated in the context of
/// `environment`, is reduced to `result`. It doesn't contain private data.
#[derive(Serialize, Deserialize)]
pub struct LurkProofMeta<F: LurkField> {
    pub(crate) iterations: usize,
    pub(crate) evaluation_cost: u128,
    pub(crate) generation_cost: u128,
    pub(crate) compression_cost: u128,
    pub(crate) status: Status,
    pub(crate) expression: ZExprPtr<F>,
    pub(crate) environment: ZExprPtr<F>,
    pub(crate) result: ZExprPtr<F>,
    pub(crate) zstore: ZStore<F>,
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

#[cfg(not(target_arch = "wasm32"))]
mod cli {
    use crate::cli::{
        field_data::FieldData,
        paths::{proof_meta_path, proof_path},
    };
    use anyhow::Result;
    use lurk::{
        coprocessor::Coprocessor, eval::lang::Coproc, field::LurkField,
        public_parameters::public_params,
    };
    use serde::Serialize;
    use std::{fs::File, io::BufReader, io::BufWriter};

    use super::{LurkProof, LurkProofMeta, Pallas};

    impl<F: LurkField + Serialize> LurkProofMeta<F> {
        pub fn persist(&self, id: &str) -> Result<()> {
            let fd = &FieldData::wrap::<F, LurkProofMeta<F>>(self)?;
            bincode::serialize_into(BufWriter::new(&File::create(proof_meta_path(id))?), fd)?;
            Ok(())
        }
    }

    impl<'a, F: LurkField + Serialize> LurkProof<'a, F>
    where
        Coproc<F>: Coprocessor<Pallas>,
    {
        pub fn persist(&self, id: &str) -> Result<()> {
            let fd = &FieldData::wrap::<F, LurkProof<'_, F>>(self)?;
            bincode::serialize_into(BufWriter::new(&File::create(proof_path(id))?), fd)?;
            Ok(())
        }

        fn print_verification(proof_id: &str, success: bool) {
            if success {
                println!("✓ Proof \"{proof_id}\" verified");
            } else {
                println!("✗ Proof \"{proof_id}\" failed on verification");
            }
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

        pub fn verify_proof<F: LurkField>(proof_id: &str) -> Result<()> {
            let file = File::open(proof_path(proof_id))?;
            let fd: FieldData = bincode::deserialize_from(BufReader::new(file))?;
            let lurk_proof = fd.extract::<F, LurkProof<'_, Pallas>>()?;
            Self::print_verification(proof_id, lurk_proof.verify()?);
            Ok(())
        }
    }
}
