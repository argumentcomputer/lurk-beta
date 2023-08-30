use camino::Utf8PathBuf;
use lurk::{
    cli::{backend::Backend, repl_lem::ReplLEM},
    eval::lang::{Coproc, Lang},
    repl::{repl, ReplState},
};
use pasta_curves::pallas::Scalar as S1;
use std::path::Path;

const TEST_FILES: [&str; 9] = [
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

#[test]
#[ignore]
fn lurk_cli_tests() {
    let example_dir = Path::new("lurk-lib/example/");

    if example_dir
        .read_dir()
        .map_or(true, |mut r| r.next().is_none())
    {
        panic!(
            "The example directory is empty. \
                Please update the submodule by running the following commands:\n\
                git submodule init\n\
                git submodule update"
        );
    }

    for f in TEST_FILES {
        let joined = example_dir.join(f);

        repl::<S1, ReplState<S1, Coproc<S1>>, _, Coproc<S1>>(Some(joined), Lang::new()).unwrap();
    }
}

#[test]
#[ignore]
fn lurk_cli_tests_lem() {
    let example_dir = Path::new("lurk-lib/example/");

    if example_dir
        .read_dir()
        .map_or(true, |mut r| r.next().is_none())
    {
        panic!(
            "The example directory is empty. \
                Please update the submodule by running the following commands:\n\
                git submodule init\n\
                git submodule update"
        );
    }

    let mut repl = ReplLEM::new(None, 10, 100000000, Backend::Nova);

    for f in TEST_FILES {
        let joined = Utf8PathBuf::from_path_buf(example_dir.join(f)).unwrap();

        let _ = repl.load_file(&joined);
    }
}
