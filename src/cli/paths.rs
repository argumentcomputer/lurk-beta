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
pub fn create_lurk_dir() -> Result<()> {
    let dir_path = lurk_dir();
    Ok(fs::create_dir_all(dir_path)?)
}

#[cfg(not(target_arch = "wasm32"))]
pub fn repl_history() -> PathBuf {
    lurk_dir().join(Path::new("repl-history"))
}
