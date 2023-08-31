use assert_cmd::prelude::*;
use camino::Utf8Path;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;
use tempfile::Builder;
use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};
use tracing_texray::TeXRayLayer;

fn lurk_cmd() -> Command {
    Command::cargo_bin("lurk").unwrap()
}

#[test]
fn test_help_subcommand() {
    let mut cmd = lurk_cmd();

    cmd.arg("help");
    cmd.assert().success();
}

#[test]
fn test_help_flag_command() {
    let mut cmd = lurk_cmd();

    cmd.arg("--help");
    cmd.assert().success();
}

#[test]
fn test_repl_command() {
    let mut cmd = lurk_cmd();

    cmd.arg("repl");
    cmd.assert().success();
}

#[test]
fn test_bad_command() {
    let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
    let bad_file = tmp_dir.path().join("uiop");

    let mut cmd = lurk_cmd();
    cmd.arg(bad_file.to_str().unwrap());
    cmd.assert().failure();
}

#[test]
fn test_config_file() {
    let subscriber = Registry::default()
        .with(fmt::layer().pretty().with_test_writer())
        .with(EnvFilter::from_default_env())
        // note: we don't `tracing_texray::examine` anything below, so no spans are printed
        // but we add the layer to allow the option in the future, maybe with a feature?
        .with(TeXRayLayer::new());

    tracing::subscriber::set_global_default(subscriber).unwrap();

    let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
    let tmp_dir = Utf8Path::from_path(tmp_dir.path()).unwrap();
    let config_dir = tmp_dir.join("lurk.toml");
    let public_params_dir = tmp_dir.join("public_params").into_string();
    let proofs_dir = tmp_dir.join("proofs").into_string();
    let commits_dir = tmp_dir.join("commits").into_string();

    let mut config_file = File::create(&config_dir).unwrap();
    config_file
        .write_all(format!("public_params = \"{}\"\n", public_params_dir).as_bytes())
        .unwrap();
    config_file
        .write_all(format!("proofs = \"{}\"\n", proofs_dir).as_bytes())
        .unwrap();
    config_file
        .write_all(format!("commits = \"{}\"\n", commits_dir).as_bytes())
        .unwrap();

    // Overwrite proof dir with env var
    let proofs_dir_env = tmp_dir.join("proofs_env").into_string();

    std::env::set_var("LURK_PROOFS", proofs_dir_env.clone());

    let config = lurk::cli::get_config(&Some(config_dir)).unwrap();

    assert_eq!(config.get("public_params").unwrap(), &public_params_dir);
    assert_eq!(config.get("proofs").unwrap(), &proofs_dir_env);
    assert_eq!(config.get("commits").unwrap(), &commits_dir);
}

// TODO: Use a snapshot test for the proof ID and/or test the REPL process
#[test]
fn test_prove_and_verify() {
    let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
    let tmp_dir = Utf8Path::from_path(tmp_dir.path()).unwrap();
    let public_param_dir = tmp_dir.join("public_params");
    let proof_dir = tmp_dir.join("proofs");
    let commit_dir = tmp_dir.join("commits");
    let lurk_file = tmp_dir.join("prove_verify.lurk");

    let mut file = File::create(lurk_file.clone()).unwrap();
    file.write_all(b"!(prove (+ 1 1))\n").unwrap();
    file.write_all(b"!(verify \"Nova_Pallas_10_0d723f6dd68729d7d119a13386f81d04daf6e1715f9ad53fb1ea54646771108a\")\n").unwrap();

    let mut cmd = lurk_cmd();
    cmd.arg("load");
    cmd.arg(lurk_file.into_string());
    cmd.arg("--public-params-dir");
    cmd.arg(public_param_dir);
    cmd.arg("--proofs-dir");
    cmd.arg(proof_dir);
    cmd.arg("--commits-dir");
    cmd.arg(commit_dir);

    cmd.assert().success();
}
