use std::io;
use thiserror::Error;

#[non_exhaustive]
#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(#[from] io::Error),
    #[error("Cache error: {0}")]
    Cache(String),
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
}
