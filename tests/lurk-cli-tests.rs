use assert_cmd::prelude::*;
use std::process::Command;

fn lurk_cmd() -> std::process::Command {
    Command::cargo_bin("lurk").unwrap()
}

#[test]
fn test_help_command() {
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
