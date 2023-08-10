use std::{
    env,
    fs::{self, File},
    io::Write,
    os::unix::prelude::PermissionsExt,
    path::Path,
    process::{exit, Command},
};

use ansi_term::Colour::{Green, Red};
use anyhow::{bail, Result};
use camino::Utf8PathBuf;

use crate::cli::paths::{circom_binary_path, circom_dir};

const CIRCOM_VERSION: &str = "2.1.6";

fn download_circom_binary(path: impl AsRef<Path>) -> Result<Command> {
    let url = match env::consts::OS {
        "linux" => "https://github.com/iden3/circom/releases/download/v2.1.6/circom-linux-amd64",
        "macos" => "https://github.com/iden3/circom/releases/download/v2.1.6/circom-macos-amd64",
        "windows" => {
            "https://github.com/iden3/circom/releases/download/v2.1.6/circom-windows-amd64.exe"
        }
        _ => {
            eprintln!("Unsupported OS");
            exit(1);
        }
    };

    let response = reqwest::blocking::get(url)?.bytes()?;
    let mut out = File::create(path.as_ref())?;
    out.write_all(&response)?;

    #[cfg(unix)]
    fs::set_permissions(path.as_ref(), fs::Permissions::from_mode(0o755))?;

    Ok(Command::new(path.as_ref().as_os_str()))
}

/// We try to find the circom binary at `<CIRCOM_DIR>/circom`,
/// where `<CIRCOM_DIR>` can be configured via the config file,
/// a environment variable, or through a CLI argument, in that order.
///
/// We *do not* consider the case where the user already has some
/// `circom` binary downloaded. The user will have two possibly
/// conflicting circom binaries floating around. However, things
/// should be kept separate as Lurk will never touch the user binary
/// and the user should never manually call the Lurk Circom binary.
///
/// Whatever path is chosen, we then test if the `circom` binary
/// exists. If it does, we return the path. Otherwise we download
/// the binary to the location and return the path.
fn get_circom_binary() -> Result<Command> {
    let circom_path = circom_binary_path();

    let output = Command::new(&circom_path).arg("--version").output();

    let success = match output {
        Ok(output) => {
            // TODO: in future add back checksum check?
            output.status.success()
                && String::from_utf8_lossy(&output.stdout).contains(CIRCOM_VERSION)
        }
        Err(_) => false,
    };

    if success {
        Ok(Command::new(circom_path))
    } else {
        download_circom_binary(circom_path)
    }
}

pub(crate) fn create_circom_gadget(circom_folder: Utf8PathBuf, name: String) -> Result<()> {
    let circom_gadget = circom_dir().join(&name);
    let circom_file = circom_folder.join(&name).with_extension("circom");

    println!(
        "Running circom binary to generate r1cs and witness files to {:?}",
        circom_gadget
    );
    fs::create_dir_all(&circom_gadget)?;
    let output = get_circom_binary()?
        .arg(circom_file)
        .arg("--r1cs")
        .arg("--wasm")
        .arg("--output")
        .arg(&circom_gadget)
        .arg("--prime")
        .arg("vesta")
        .output()
        .expect("circom failed");

    if !output.status.success() {
        println!(
            "{} Please check that your input files are correct,",
            Red.bold().paint("Circom failed.")
        );
        println!("  and refer to the circom stderr output for further information:\n");
        bail!("{}", String::from_utf8_lossy(&output.stderr));
    }

    // get out `name`_js/`name`.wasm and `name`.r1cs
    // and put them in <CIRCOM_DIR>/`name`/*
    fs::copy(
        circom_gadget.join(format!("{}_js/{}.wasm", &name, &name)),
        circom_gadget.join(format!("{}.wasm", &name)),
    )?;
    fs::remove_dir_all(circom_gadget.join(format!("{}_js", &name)))?;

    println!("{}", Green.bold().paint("Circom success"));
    Ok(())
}
