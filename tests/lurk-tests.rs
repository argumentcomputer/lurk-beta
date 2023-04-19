use lurk::{
    eval::lang::{Coproc, Lang},
    proof::nova,
    repl::{repl, ReplState},
};
use std::path::Path;

#[test]
#[ignore]
fn lurk_tests() {
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

    for f in test_files {
        let joined = example_dir.join(f);

        repl::<nova::S1, ReplState<nova::S1, Coproc<nova::S1>>, _, Coproc<nova::S1>>(
            Some(joined),
            Lang::new(),
        )
        .unwrap();
    }
}
