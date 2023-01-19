use crate::eval;
use crate::field;
use crate::parser;
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
    #[error("Lurk error: {0}")]
    Lurk(#[from] LurkError),
}

#[derive(Error, Debug, Clone)]
pub enum LurkError {
    #[error("Evaluation error: {0}")]
    Reduce(String),
    #[error("Lookup error: {0}")]
    Store(#[from] store::Error),
    #[error("Parser error: {0}")]
    Parser(#[from] parser::Error),
}

#[derive(Error, Debug, Clone)]
pub enum ReduceError<F: field::LurkField> {
    #[error("Lurk error: {0}")]
    Lurk(#[from] LurkError),
    #[error("Explicit error: {0}")]
    Explicit(#[from] eval::ExplicitError<F>),
}
