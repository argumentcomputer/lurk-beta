use std::{fs, path::Path, process::Command};

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

use ansi_term::Colour::{Green, Red};
use anyhow::{anyhow, bail, Result};
use camino::Utf8PathBuf;

use crate::cli::paths::{circom_binary_path, circom_dir};

const CIRCOM_VERSION: &str = "2.1.6";

#[cfg(target_arch = "wasm32")]
fn download_circom_binary(_path: impl AsRef<Path>) -> Result<Command> {
    bail!("wasm does not support downloading")
}

#[cfg(not(target_arch = "wasm32"))]
fn download_circom_binary(path: impl AsRef<Path>) -> Result<Command> {
    use std::io::Write;

    let url = match std::env::consts::OS {
        "linux" => format!("https://github.com/iden3/circom/releases/download/v{CIRCOM_VERSION}/circom-linux-amd64"),
        "macos" => format!("https://github.com/iden3/circom/releases/download/v{CIRCOM_VERSION}/circom-macos-amd64"),
        "windows" => {
            format!("https://github.com/iden3/circom/releases/download/v{CIRCOM_VERSION}/circom-windows-amd64.exe")
        }
        os => {
            bail!("Unsupported OS: {os}. Unable to automatically download the necessary circom binary, please manually download Circom v{CIRCOM_VERSION} to `.lurk/circom/circom`");
        }
    };

    let response = reqwest::blocking::get(url)?.bytes()?;
    let mut out = fs::File::create(path.as_ref())?;
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
/// `circom` binary available in their `$PATH`. The user will have two
/// possibly conflicting circom binaries floating around. However, things
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

/// This method will compile a designated Circom circuit and store the generated static files in our
/// lurk folder.
pub(crate) fn create_circom_gadget(circom_folder: &Utf8PathBuf, reference: &str) -> Result<()> {
    let circom_gadget = circom_dir().join(reference);

    // We expect a format <AUTHOR>/<NAME> for the name.
    // TODO: should we switch to check regex: ^[a-zA-Z0-9]+([_-]?[a-zA-Z0-9]+)*\/[a-zA-Z0-9]+([_-]?[a-zA-Z0-9]+)*$ ?
    let reference_split: Vec<&str> = reference.split("/").collect();
    if reference_split.len() != 2 {
        bail!("Expected a reference of format \"<AUTHOR>/<NAME>\", got \"{reference}\"");
    }

    let circom_file = circom_folder
        .join(reference_split[1])
        .with_extension("circom");

    // TODO: support for other fields
    let default_field = "vesta";
    let field = if let Ok(lurk_field) = std::env::var("LURK_FIELD") {
        // FG: The prime is actually the reverse of the field in $LURK_FIELD,
        // because circom and lurk have different semantics about which field should be specified
        // (circom wants the base field and lurk the scalar field).
        match lurk_field.as_str() {
            "PALLAS" => "vesta",
            "VESTA" => "pallas",
            _ => bail!("Unsupported field: {lurk_field}"),
        }
    } else {
        default_field
    };

    println!("Running circom binary to generate r1cs and witness files to {circom_gadget:?}");
    fs::create_dir_all(&circom_gadget)
        .map_err(|err| anyhow!("Couldn't create folder for static files: {err}"))?;
    let output = get_circom_binary()?
        .args(&[
            circom_file,
            "--r1cs".into(),
            "--wasm".into(),
            "--output".into(),
            circom_gadget.clone(),
            "--prime".into(),
            field.into(),
        ])
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

    // Get out <NAME>_js/<NAME>.wasm and <NAME>.r1cs and put them in <CIRCOM_DIR>/<AUTHOR>/<NAME>/*.
    fs::copy(
        circom_gadget.join(format!(
            "{}_js/{}.wasm",
            &reference_split[1], &reference_split[1]
        )),
        circom_gadget.join(format!("{}.wasm", &reference_split[1])),
    )
    .map_err(|err| {
        anyhow!(
            "Couldn't move compilation artifacts to Lurk folder: {}",
            err
        )
    })?;
    fs::remove_dir_all(circom_gadget.join(format!("{}_js", &reference_split[1])))
        .map_err(|err| anyhow!("Couldn't clean up temporary artifacts: {err}"))?;

    println!("{}", Green.bold().paint("Circom success"));
    Ok(())
}
