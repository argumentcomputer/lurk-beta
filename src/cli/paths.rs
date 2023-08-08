use anyhow::Result;
use camino::{Utf8Path, Utf8PathBuf};
use once_cell::sync::OnceCell;

use std::collections::HashMap;
use std::fs;

use crate::public_parameters::public_params_default_dir;

pub(crate) static LURK_DIRS: OnceCell<LurkDirs> = OnceCell::new();

pub(crate) struct LurkDirs {
    public_params: Utf8PathBuf,
    proofs: Utf8PathBuf,
    commits: Utf8PathBuf,
    circom: Utf8PathBuf,
}

#[cfg(not(target_arch = "wasm32"))]
fn home_dir() -> Utf8PathBuf {
    Utf8PathBuf::from_path_buf(home::home_dir().expect("missing home directory"))
        .expect("path contains invalid Unicode")
}

#[cfg(not(target_arch = "wasm32"))]
fn lurk_dir() -> Utf8PathBuf {
    home_dir().join(Utf8Path::new(".lurk"))
}

#[cfg(target_arch = "wasm32")]
pub(crate) fn lurk_dir() -> Utf8PathBuf {
    Utf8PathBuf::from(".lurk")
}

#[cfg(not(target_arch = "wasm32"))]
pub(crate) fn proofs_default_dir() -> Utf8PathBuf {
    let home = home::home_dir().unwrap();
    Utf8PathBuf::from_path_buf(home.join(".lurk/proofs")).expect("path contains invalid Unicode")
}

#[cfg(target_arch = "wasm32")]
pub(crate) fn proofs_default_dir() -> Utf8PathBuf {
    Utf8PathBuf::from(".lurk/public_params")
}

pub(crate) fn commits_default_dir() -> Utf8PathBuf {
    Utf8PathBuf::from(".lurk/commits")
}

pub(crate) fn circom_default_dir() -> Utf8PathBuf {
    Utf8PathBuf::from(".lurk/circom")
}

pub(crate) fn public_params_dir() -> Utf8PathBuf {
    LURK_DIRS
        .get()
        .expect("failed to initialize beforehand with `set_lurk_dirs()`")
        .public_params
        .to_owned()
}

pub(crate) fn proofs_dir() -> Utf8PathBuf {
    LURK_DIRS
        .get()
        .expect("failed to initialize beforehand with `set_lurk_dirs()`")
        .proofs
        .to_owned()
}

pub(crate) fn commits_dir() -> Utf8PathBuf {
    LURK_DIRS
        .get()
        .expect("failed to initialize beforehand with `set_lurk_dirs()`")
        .commits
        .to_owned()
}

pub(crate) fn circom_dir() -> Utf8PathBuf {
    LURK_DIRS
        .get()
        .expect("failed to initialize beforehand with `set_lurk_dirs()`")
        .circom
        .to_owned()
}


fn lurk_leaf_dirs() -> [Utf8PathBuf; 3] {
    [proofs_dir(), commits_dir(), public_params_dir()]
}

pub(crate) fn set_lurk_dirs(
    config: &HashMap<String, String>,
    public_params_dir: &Option<Utf8PathBuf>,
    proofs_dir: &Option<Utf8PathBuf>,
    commits_dir: &Option<Utf8PathBuf>,
    circom_dir: &Option<Utf8PathBuf>,
) {
    let get_path = |given_path: &Option<Utf8PathBuf>, config_key: &str, default: Utf8PathBuf| {
        given_path.clone().unwrap_or_else(|| {
            config
                .get(config_key)
                .map_or_else(|| default, Utf8PathBuf::from)
        })
    };

    let public_params = get_path(
        public_params_dir,
        "public_params",
        public_params_default_dir(),
    );
    let proofs = get_path(proofs_dir, "proofs", proofs_default_dir());
    let commits = get_path(commits_dir, "commits", commits_default_dir());
    let circom = get_path(circom_dir, "circom", commits_default_dir());

    LURK_DIRS.get_or_init(|| LurkDirs {
        public_params,
        proofs,
        commits,
        circom,
    });

    create_lurk_dirs().unwrap();
}

/// Must call this function after setting `LURK_DIRS` via the `set_lurk_dirs()` function
pub(crate) fn create_lurk_dirs() -> Result<()> {
    for dir in lurk_leaf_dirs() {
        fs::create_dir_all(dir)?;
    }
    Ok(())
}

// Not currently configurable
pub(crate) fn repl_history() -> Utf8PathBuf {
    lurk_dir().join(Utf8Path::new("repl-history"))
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