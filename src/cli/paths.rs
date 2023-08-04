use anyhow::Result;
use camino::{Utf8Path, Utf8PathBuf};

use crate::cli::{COMMITS_DIR, PROOFS_DIR, PUBLIC_PARAMS_DIR};
use std::fs;

#[cfg(not(target_arch = "wasm32"))]
fn home_dir() -> Utf8PathBuf {
    Utf8PathBuf::from_path_buf(home::home_dir().expect("missing home directory"))
        .expect("path contains invalid Unicode")
}

#[cfg(not(target_arch = "wasm32"))]
pub fn lurk_dir() -> Utf8PathBuf {
    home_dir().join(Utf8Path::new(".lurk"))
}

#[cfg(target_arch = "wasm32")]
pub fn lurk_dir() -> Utf8PathBuf {
    Utf8PathBuf::from(".lurk")
}

pub fn public_params_dir() -> Utf8PathBuf {
    PUBLIC_PARAMS_DIR
        .get()
        .expect("failed to initialize beforehand with `set_lurk_dirs()`")
        .join(Utf8Path::new("public_params"))
}

pub fn proofs_dir() -> Utf8PathBuf {
    PROOFS_DIR
        .get()
        .expect("failed to initialize beforehand with `set_lurk_dirs()`")
        .join(Utf8Path::new("proofs"))
}

pub fn commits_dir() -> Utf8PathBuf {
    COMMITS_DIR
        .get()
        .expect("failed to initialize beforehand with `set_lurk_dirs()`")
        .join(Utf8Path::new("commits"))
}

pub fn lurk_leaf_dirs() -> [Utf8PathBuf; 3] {
    [proofs_dir(), commits_dir(), public_params_dir()]
}

pub fn create_lurk_dirs() -> Result<()> {
    for dir in lurk_leaf_dirs() {
        fs::create_dir_all(dir)?;
    }
    Ok(())
}

// Not currently configurable
pub fn repl_history() -> Utf8PathBuf {
    lurk_dir().join(Utf8Path::new("repl-history"))
}

pub fn commitment_path(name: &str) -> Utf8PathBuf {
    commits_dir().join(Utf8Path::new(name))
}

pub fn proof_path(name: &str) -> Utf8PathBuf {
    proofs_dir()
        .join(Utf8Path::new(name))
        .with_extension("proof")
}

pub fn proof_meta_path(name: &str) -> Utf8PathBuf {
    proofs_dir()
        .join(Utf8Path::new(name))
        .with_extension("meta")
}
