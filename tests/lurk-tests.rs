use lurk::{proof, repl::repl};
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

    for f in test_files {
        let joined = example_dir.join(f);

        repl::<_, proof::nova::S1>(Some(joined)).unwrap();
    }
}
