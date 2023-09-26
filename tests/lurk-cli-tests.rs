use assert_cmd::prelude::*;
use camino::Utf8Path;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;
use tempfile::Builder;

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
    file.write_all(b"!(verify \"Nova_Pallas_10_3f2526abf20fc9006dd93c0d3ff49954ef070ef52d2e88426974de42cc27bdb2\")\n").unwrap();

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
