#[cfg(not(target_arch = "wasm32"))]
use anyhow::Result;

#[cfg(not(target_arch = "wasm32"))]
use std::{
    fs,
    path::{Path, PathBuf},
};

#[cfg(not(target_arch = "wasm32"))]
fn home_dir() -> PathBuf {
    home::home_dir().expect("missing home directory")
}

#[cfg(not(target_arch = "wasm32"))]
pub fn lurk_dir() -> PathBuf {
    home_dir().join(Path::new(".lurk"))
}

#[cfg(not(target_arch = "wasm32"))]
pub fn proofs_dir() -> PathBuf {
    lurk_dir().join(Path::new("proofs"))
}

#[cfg(not(target_arch = "wasm32"))]
pub fn lurk_leaf_dirs() -> [PathBuf; 1] {
    [proofs_dir()]
}

#[cfg(not(target_arch = "wasm32"))]
pub fn create_lurk_dirs() -> Result<()> {
    for dir in lurk_leaf_dirs() {
        fs::create_dir_all(dir)?;
    }
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
pub fn proof_path(name: &str) -> PathBuf {
    proofs_dir().join(Path::new(name)).with_extension("proof")
}

#[cfg(not(target_arch = "wasm32"))]
pub fn proof_meta_path(name: &str) -> PathBuf {
    proofs_dir().join(Path::new(name)).with_extension("meta")
}

#[cfg(not(target_arch = "wasm32"))]
pub fn repl_history() -> PathBuf {
    lurk_dir().join(Path::new("repl-history"))
}
