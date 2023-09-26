use anyhow::Result;
use camino::{Utf8Path, Utf8PathBuf};

use std::fs;

use crate::cli::config::cli_config;
use crate::public_parameters::disk_cache::public_params_dir;

#[cfg(not(target_arch = "wasm32"))]
fn home_dir() -> Utf8PathBuf {
    Utf8PathBuf::from_path_buf(home::home_dir().expect("missing home directory"))
        .expect("path contains invalid Unicode")
}

#[cfg(not(target_arch = "wasm32"))]
pub fn lurk_default_dir() -> Utf8PathBuf {
    home_dir().join(Utf8Path::new(".lurk"))
}

#[cfg(target_arch = "wasm32")]
pub fn lurk_default_dir() -> Utf8PathBuf {
    Utf8PathBuf::from(".lurk")
}

pub(crate) fn proofs_default_dir() -> Utf8PathBuf {
    lurk_default_dir().join("proofs")
}

pub(crate) fn commits_default_dir() -> Utf8PathBuf {
    lurk_default_dir().join("commits")
}

pub(crate) fn circom_default_dir() -> Utf8PathBuf {
    lurk_default_dir().join("circom")
}

pub(crate) fn proofs_dir() -> &'static Utf8PathBuf {
    &cli_config(None, None).proofs_dir
}

pub(crate) fn commits_dir() -> &'static Utf8PathBuf {
    &cli_config(None, None).commits_dir
}

pub(crate) fn circom_dir() -> &'static Utf8PathBuf {
    &cli_config(None, None).circom_dir
}

fn lurk_leaf_dirs() -> [&'static Utf8PathBuf; 4] {
    [
        proofs_dir(),
        commits_dir(),
        public_params_dir(),
        circom_dir(),
    ]
}

// Creates dirs for public params, proofs, commits, and circom
// NOTE: call this function after `cli_config()` or `lurk_config()` if non-default
// config settings are desired, as it will initialize them if unset
pub(crate) fn create_lurk_dirs() -> Result<()> {
    for dir in lurk_leaf_dirs() {
        fs::create_dir_all(dir)?;
    }
    Ok(())
}

// Not currently configurable
pub(crate) fn repl_history() -> Utf8PathBuf {
    lurk_default_dir().join(Utf8Path::new("repl-history"))
}

pub(crate) fn commitment_path(name: &str) -> Utf8PathBuf {
    commits_dir().join(Utf8Path::new(&format!("{name}.commit")))
}

pub(crate) fn proof_path(name: &str) -> Utf8PathBuf {
    proofs_dir()
        .join(Utf8Path::new(name))
        .with_extension("proof")
}

pub(crate) fn proof_meta_path(name: &str) -> Utf8PathBuf {
    proofs_dir()
        .join(Utf8Path::new(name))
        .with_extension("meta")
}

pub(crate) fn circom_binary_path() -> Utf8PathBuf {
    circom_dir().join("circom")
}
