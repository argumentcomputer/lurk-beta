use bellperson::SynthesisError;
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
    EvaluationFailure,
    #[error("Store error: {0}")]
    StoreError(#[from] store::Error),
    #[error("Cache error: {0}")]
    CacheError(String),
}
