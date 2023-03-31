use assert_cmd::prelude::*;
use std::path::{Path, PathBuf};
use std::process::Command;

fn lurkrs_cmd() -> std::process::Command {
    Command::cargo_bin("clutch").unwrap()
}

fn demo_file(name: &str) -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));

    let demo_dir = manifest_dir.join("demo/");

    demo_dir.join(name)
}

#[test]
fn test_help_command() {
    let mut cmd = lurkrs_cmd();

    cmd.arg("--help");
    cmd.assert().success();
}

fn test_demo(name: &str) {
    let mut cmd = lurkrs_cmd();

    cmd.arg(demo_file(name));

    cmd.assert().success();
}

#[test]
#[ignore]
fn test_functional_commitments_demo() {
    test_demo("functional-commitment.lurk");
}

#[test]
#[ignore]
fn test_chained_functional_commitments_demo() {
    test_demo("chained-functional-commitment.lurk");
}
