use assert_cmd::prelude::*;
use std::process::Command;

/// TODO: replace this test for more granular ones, specific for the NIVC
/// pipeline steps
#[test]
#[ignore]
fn test_sha256_nivc() {
    let mut cmd = Command::new("cargo");
    cmd.args(["run", "--release", "--example", "sha256_nivc"]);
    cmd.assert().success();
}
