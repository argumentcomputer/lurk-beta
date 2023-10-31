use camino::Utf8PathBuf;
use lurk::{
    cli::{backend::Backend, repl::Repl},
    eval::lang::{Coproc, Lang},
    lem::store::Store,
    repl::{repl, ReplState},
};
use pasta_curves::pallas::Scalar as S1;
use std::path::Path;

#[test]
#[ignore]
fn lurk_cli_tests() {
    let test_files = [
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
    let mut repl_new = Repl::new(Store::default(), 10, 100000000, Backend::Nova);

    for f in test_files {
        let joined = example_dir.join(f);
        let joined_new = Utf8PathBuf::from_path_buf(joined.clone()).unwrap();

        repl::<S1, ReplState<S1, Coproc<S1>>, _, Coproc<S1>>(Some(joined), Lang::new()).unwrap();
        let _ = repl_new.load_file(&joined_new, false);
    }
}
