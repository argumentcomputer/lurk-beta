use std::process::Command;

use assert_cmd::prelude::{CommandCargoExt, OutputAssertExt};
use camino::Utf8PathBuf;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};

#[inline]
fn lurk_cmd() -> Command {
    Command::cargo_bin("lurk").unwrap()
}

#[test]
#[ignore]
fn test_lurk_lib() {
    const LURK_LIB_EXAMPLES_DIR: &str = "lurk-lib/example";

    assert!(
        Utf8PathBuf::from(LURK_LIB_EXAMPLES_DIR).exists(),
        "The lurk-lib example directory does not exist. \
            Please update the submodule by running the following commands:\n\
            git submodule init\n\
            git submodule update"
    );

    let lurk_lib_examples = [
        "test.lurk",
        "micro-tests.lurk",
        "meta-tests.lurk",
        "meta-letrec-tests.lurk",
        "fibonacci-tests.lurk",
        "tests/spec.lurk",
        "tests/eval.lurk",
        "tests/begin.lurk",
        "tests/auto-curry.lurk",
    ];

    lurk_lib_examples.into_par_iter().for_each(|f| {
        let mut cmd = lurk_cmd();
        cmd.current_dir(LURK_LIB_EXAMPLES_DIR);
        cmd.env("LURK_PANIC_IF_CANT_LOAD", "true");
        cmd.arg(f);
        cmd.assert().success();
    });
}

#[test]
#[ignore]
fn test_demo() {
    // proving involved!
    let demo_examples = [
        "demo/simple.lurk",
        "demo/functional-commitment.lurk",
        "demo/chained-functional-commitment.lurk",
        "demo/bank.lurk",
        "demo/vdf.lurk",
    ];

    demo_examples.into_par_iter().for_each(|f| {
        let mut cmd = lurk_cmd();
        cmd.env("LURK_PERF", "max-parallel-simple");
        cmd.arg(f);
        cmd.assert().success();
    });
}
