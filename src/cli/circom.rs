use std::{
    fs::{self, File},
    io::copy,
    path::PathBuf,
    process::Command,
};

use anyhow::Result;
use sha2::{Digest, Sha256};

use super::paths::non_wasm::{circom_binary, circom_gadgets};

/// Attempts to verify the checksum and version of the circom binary.
/// If the binary does not exist, it is downloaded.
/// TODO
fn verify_circom_binary() -> Result<()> {
    let output = Command::new(circom_binary())
        .arg("--version")
        .output()
        .expect("TODO: handle case where circom binary does not exist");

    // version check
    let version = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        version, "circom compiler 2.1.6\n",
        "TODO: handle the case where the circom version is incorrect"
    );

    // sha256 checksum
    let mut file = File::open(circom_binary())?;
    let mut hasher = Sha256::new();
    let _ = copy(&mut file, &mut hasher)?;
    let digest = hasher.finalize();

    assert_eq!(
        format!("{:X}", digest).to_ascii_lowercase(),
        "560a7f24dbb79940860e9ed9ce99731171734593cdeb0477a6a2ba33123fa4d4", // TODO: this is only macOS
        "TODO: handle the case where the checksum does not match"
    );
    Ok(())
}

pub fn create_circom_gadget(circom_folder: PathBuf, name: Option<String>) -> Result<()> {
    println!("Verifying Circom binary");
    verify_circom_binary()?;

    // name cannot be `main`
    let folder_name = circom_folder
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .expect("folder is not valid");
    let name = name.unwrap_or(folder_name);

    let circom_gadget = circom_gadgets().join(&name);
    let circom_file = circom_folder.join(&name).with_extension("circom");

    println!(
        "Running circom binary to generate r1cs and witness files to {:?}",
        circom_gadget
    );
    fs::create_dir_all(&circom_gadget)?;
    Command::new(circom_binary())
        .arg(circom_file)
        .arg("--r1cs")
        .arg("--wasm")
        .arg("--output")
        .arg(&circom_gadget)
        .arg("--prime")
        .arg("vesta")
        .output()
        .expect("circom failed");

    // get out `name`_js/`name`.wasm and `name`.r1cs
    // and put them in circom_gadgets()/`name`/*
    println!("Cleaning up");
    fs::copy(
        circom_gadget.join(format!("{}_js/{}.wasm", &name, &name)),
        circom_gadget.join(format!("{}.wasm", &name)),
    )?;
    fs::remove_dir_all(circom_gadget.join(format!("{}_js", &name)))?;

    println!("Circom success");
    Ok(())
}
