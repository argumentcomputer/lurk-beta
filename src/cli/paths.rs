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

pub fn create_lurk_dir() -> Result<()> {
    let dir_path = lurk_dir();
    if !dir_path.exists() {
        fs::create_dir(dir_path)?;
    }
    Ok(())
}

pub fn repl_history() -> PathBuf {
    lurk_dir().join(Path::new("repl-history"))
}
