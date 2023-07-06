use anyhow::Result;

use std::{path::{Path, PathBuf}, fs};

fn home_dir() -> PathBuf {
    home::home_dir().expect("missing home directory")
}

pub fn lurk_dir() -> PathBuf {
    home_dir().join(Path::new(".lurk"))
}

pub fn create_lurk_dir() -> Result<()> {
    let dir_path = lurk_dir();
    if !dir_path.exists() {
        fs::create_dir(lurk_dir())?;
    }
    Ok(())
}

pub fn repl_history() -> PathBuf {
    lurk_dir().join(Path::new("repl-history"))
}
