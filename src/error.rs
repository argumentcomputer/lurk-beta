use crate::eval::IO;
use crate::field::LurkField;
use crate::hash_witness::ConsName;
use crate::store;

use bellperson::SynthesisError;
use nova::errors::NovaError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProofError {
    #[error("Nova error")]
    Nova(NovaError),
    #[error("Synthesis error: {0}")]
    Synthesis(#[from] SynthesisError),
    #[error("Reduction error: {0}")]
    Reduction(#[from] ReductionError),
}

impl From<NovaError> for ProofError {
    fn from(e: NovaError) -> Self {
        Self::Nova(e)
    }
}

impl From<store::Error> for ProofError {
    fn from(e: store::Error) -> Self {
        Self::Reduction(e.into())
    }
}

#[derive(Error, Debug, Clone)]
pub enum ReductionError {
    #[error("car_cdr of named cons {0:?} requires a cons or nil.")]
    CarCdrType(ConsName),
    #[error("Miscellaneous error: {0}")]
    Misc(String),
    #[error("Lookup error: {0}")]
    Store(#[from] store::Error),
}

#[derive(Error, Debug, Clone)]
pub enum LurkError<F: LurkField> {
    #[error("Explicit Lurk error; IO: {0}")]
    IO(IO<F>),
}
