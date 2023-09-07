use std::io;
use thiserror::Error;

#[non_exhaustive]
#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IOError(#[from] io::Error),
    #[error("Cache error: {0}")]
    CacheError(String),
    #[error("JSON error: {0}")]
    JsonError(#[from] serde_json::Error),
}
