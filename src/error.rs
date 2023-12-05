use crate::store;

use bellpepper_core::SynthesisError;
use nova::errors::NovaError;
use nova::supernova::error::SuperNovaError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProofError {
    #[error("Nova error")]
    Nova(#[from] NovaError),
    #[error("SuperNova error")]
    SuperNova(#[from] SuperNovaError),
    #[error("Synthesis error: {0}")]
    Synthesis(#[from] SynthesisError),
    #[error("Reduction error: {0}")]
    Reduction(#[from] ReductionError),
}

impl From<store::Error> for ProofError {
    fn from(e: store::Error) -> Self {
        Self::Reduction(e.into())
    }
}

#[derive(Error, Debug, Clone)]
pub enum ReductionError {
    #[error("Miscellaneous error: {0}")]
    Misc(String),
    #[error("Lookup error: {0}")]
    Store(#[from] store::Error),
}
