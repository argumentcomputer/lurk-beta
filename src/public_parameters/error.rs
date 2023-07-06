use std::io;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IOError(#[from] io::Error),
    #[error("Cache error: {0}")]
    CacheError(String),
}
