#[cfg(not(target_arch = "wasm32"))]
pub mod non_wasm {
    use anyhow::Result;

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

    pub fn proofs_dir() -> PathBuf {
        lurk_dir().join(Path::new("proofs"))
    }

    pub fn commits_dir() -> PathBuf {
        lurk_dir().join(Path::new("commits"))
    }

    pub fn lurk_leaf_dirs() -> [PathBuf; 2] {
        [proofs_dir(), commits_dir()]
    }

    pub fn create_lurk_dirs() -> Result<()> {
        for dir in lurk_leaf_dirs() {
            fs::create_dir_all(dir)?;
        }
        Ok(())
    }

    pub fn repl_history() -> PathBuf {
        lurk_dir().join(Path::new("repl-history"))
    }

    pub fn commitment_path(name: &str) -> PathBuf {
        commits_dir().join(Path::new(name))
    }

    pub fn proof_path(name: &str) -> PathBuf {
        proofs_dir().join(Path::new(name)).with_extension("proof")
    }

    pub fn proof_meta_path(name: &str) -> PathBuf {
        proofs_dir().join(Path::new(name)).with_extension("meta")
    }
}
