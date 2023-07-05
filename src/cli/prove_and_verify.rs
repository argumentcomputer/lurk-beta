use anyhow::Result;
use lurk::{
    field::LurkField,
    public_parameters::{Claim, Proof},
};
use std::path::PathBuf;

pub fn prove_claim<F: LurkField>(claim: &Claim<F>) -> Result<Proof<F>> {
    // TODO: mimic clutch
    todo!()
}

pub fn verify_proof(proof_file: &PathBuf) -> Result<()> {
    // TODO: mimic clutch
    todo!()
}
