use assert_cmd::prelude::*;
use std::process::Command;

fn lurkrs_cmd() -> std::process::Command {
    Command::cargo_bin("lurkrs").unwrap()
}

#[test]
fn test_help_command() {
    let mut cmd = lurkrs_cmd();

    cmd.arg("--help");
    cmd.assert().success();
}
