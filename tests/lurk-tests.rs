use lurk::{
    proof::nova,
    repl::{repl, ReplState},
};
use std::path::Path;

#[test]
fn lurk_tests() {
    let test_files = [
        "test.lurk",
        "micro-tests.lurk",
        "meta-tests.lurk",
        "meta-letrec-tests.lurk",
        "fibonacci-tests.lurk",
        "tests/spec.lurk",
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

        repl::<nova::S1, ReplState<nova::S1>, _>(Some(joined)).unwrap();
    }
}
