use crate::field;
use crate::parser;
use crate::store::{self, Ptr};
use bellperson::SynthesisError;
use nova::errors::NovaError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProofError {
    #[error("Nova error")]
    Nova(NovaError),
    #[error("Synthesis error: {0}")]
    Synthesis(#[from] SynthesisError),
    #[error("Runtime error: {0}")]
    RuntimeError(#[from] RuntimeError),
}

#[derive(Error, Debug, Clone)]
pub enum RuntimeError {
    #[error("Reduction error: {0}")]
    Reduce(String),
    #[error("Lookup error: {0}")]
    Store(#[from] store::Error),
    #[error("Parser error: {0}")]
    Parser(#[from] parser::Error),
}

#[derive(Error, Debug, Clone)]
pub enum ReduceError<F: field::LurkField> {
    #[error("Runtime error: {0}")]
    Runtime(#[from] RuntimeError),
    #[error("Explicit error: {0}")]
    Explicit(String, Ptr<F>),
}
