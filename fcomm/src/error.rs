use anyhow;
use bellperson::SynthesisError;
use lurk::error::ReductionError;
use lurk::public_parameters::error;
use lurk::store;
use std::io;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Verification error: {0}")]
    VerificationError(String),
    #[error("Unsupported reduction count: {0}")]
    UnsupportedReductionCount(usize),
    #[error("IO error: {0}")]
    IOError(#[from] io::Error),
    #[error("JSON error: {0}")]
    JsonError(#[from] serde_json::Error),
    #[error("Synthesis error: {0}")]
    SynthesisError(#[from] SynthesisError),
    #[error("Commitment parser error: {0}")]
    CommitmentParseError(#[from] hex::FromHexError),
    #[error("Unknown commitment")]
    UnknownCommitment,
    #[error("Opening Failure: {0}")]
    OpeningFailure(String),
    #[error("Evaluation Failure")]
    EvaluationFailure(ReductionError),
    #[error("Store error: {0}")]
    StoreError(#[from] store::Error),
    #[error("Serde error: {0}")]
    SerdeError(#[from] lurk::z_data::serde::SerdeError),
    #[error("Anyhow error: {0}")]
    AnyhowError(#[from] anyhow::Error),
    #[error("Cache error: {0}")]
    CacheError(#[from] error::Error),
}
