#[cfg(not(target_arch = "wasm32"))]
pub mod non_wasm {
    use anyhow::Result;

    use crate::cli::{COMMIT_DIR, PROOF_DIR, PUBLIC_PARAM_DIR};
    use std::{
        fs,
        path::{Path, PathBuf},
    };

    fn home_dir() -> PathBuf {
        home::home_dir().expect("missing home directory")
    }

    pub fn lurk_dir() -> PathBuf {
        home_dir().join(Path::new(".lurk"))
    }

    pub fn public_param_dir() -> PathBuf {
        PUBLIC_PARAM_DIR
            .get()
            .unwrap()
            .join(Path::new("public_params"))
    }

    pub fn proof_dir() -> PathBuf {
        PROOF_DIR.get().unwrap().join(Path::new("proofs"))
    }

    pub fn commit_dir() -> PathBuf {
        COMMIT_DIR.get().unwrap().join(Path::new("commits"))
    }

    pub fn lurk_leaf_dirs() -> [PathBuf; 3] {
        [proof_dir(), commit_dir(), public_param_dir()]
    }

    pub fn create_lurk_dirs() -> Result<()> {
        for dir in lurk_leaf_dirs() {
            fs::create_dir_all(dir)?;
        }
        Ok(())
    }

    // Not currently configurable
    pub fn repl_history() -> PathBuf {
        lurk_dir().join(Path::new("repl-history"))
    }

    pub fn commitment_path(name: &str) -> PathBuf {
        commit_dir().join(Path::new(name))
    }

    pub fn proof_path(name: &str) -> PathBuf {
        proof_dir().join(Path::new(name)).with_extension("proof")
    }

    pub fn proof_meta_path(name: &str) -> PathBuf {
        proof_dir().join(Path::new(name)).with_extension("meta")
    }
}
