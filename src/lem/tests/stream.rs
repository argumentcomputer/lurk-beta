use expect_test::{expect, Expect};
use halo2curves::bn256::Fr;

use crate::{
    dual_channel::{dummy_terminal, pair_terminals},
    lang::Coproc,
    lem::{
        eval::{evaluate_simple, resume_stream_simple, start_stream_simple},
        pointers::Ptr,
        store::Store,
    },
};

const LIMIT: usize = 200;

fn get_callable(callable_str: &str, store: &Store<Fr>) -> Ptr {
    let callable = store.read_with_default_state(callable_str).unwrap();
    let (io, _) =
        evaluate_simple::<Fr, Coproc<Fr>>(None, callable, store, LIMIT, &dummy_terminal()).unwrap();
    io[0]
}

#[inline]
fn expect_eq(computed: usize, expected: &Expect) {
    expected.assert_eq(&computed.to_string());
}

fn assert_start_stream(
    callable: Ptr,
    arg: Ptr,
    store: &Store<Fr>,
    expected_result: Ptr,
    expected_iterations: &Expect,
) -> Vec<Ptr> {
    let (t1, t2) = pair_terminals();
    t2.send(arg).unwrap();
    let (output, iterations) =
        start_stream_simple::<Fr, Coproc<Fr>>(None, callable, store, LIMIT, &t1).unwrap();
    let (result, _) = store.fetch_cons(&output[0]).unwrap();
    assert_eq!(result, expected_result);
    expect_eq(iterations, expected_iterations);
    output
}

fn assert_resume_stream(
    input: Vec<Ptr>,
    arg: Ptr,
    store: &Store<Fr>,
    expected_result: Ptr,
    expected_iterations: &Expect,
) -> Vec<Ptr> {
    let (t1, t2) = pair_terminals();
    t2.send(store.intern_nil()).unwrap(); // send nil to skip stuttering
    t2.send(arg).unwrap();
    let (output, iterations) =
        resume_stream_simple::<Fr, Coproc<Fr>>(None, input, store, LIMIT, &t1).unwrap();
    let (result, _) = store.fetch_cons(&output[0]).unwrap();
    assert_eq!(result, expected_result);
    expect_eq(iterations, expected_iterations);
    output
}

#[test]
fn test_comm_callable() {
    let callable_str = "(commit (letrec ((add (lambda (counter x)
            (let ((counter (+ counter x)))
            (cons counter (commit (add counter)))))))
        (add 0)))";
    let store = Store::<Fr>::default();
    let callable = get_callable(callable_str, &store);
    let expected_iterations = &expect!["16"];

    let output = assert_start_stream(
        callable,
        store.num_u64(123),
        &store,
        store.num_u64(123),
        expected_iterations,
    );
    let output = assert_resume_stream(
        output,
        store.num_u64(321),
        &store,
        store.num_u64(444),
        expected_iterations,
    );
    assert_resume_stream(
        output,
        store.num_u64(111),
        &store,
        store.num_u64(555),
        expected_iterations,
    );
}

#[test]
fn test_fun_callable() {
    let callable_str = "(letrec ((add (lambda (counter x)
            (let ((counter (+ counter x)))
            (cons counter (add counter))))))
        (add 0))";
    let store = Store::<Fr>::default();
    let callable = get_callable(callable_str, &store);
    let expected_iterations = &expect!["14"];

    let output = assert_start_stream(
        callable,
        store.num_u64(123),
        &store,
        store.num_u64(123),
        expected_iterations,
    );
    let output = assert_resume_stream(
        output,
        store.num_u64(321),
        &store,
        store.num_u64(444),
        expected_iterations,
    );
    assert_resume_stream(
        output,
        store.num_u64(111),
        &store,
        store.num_u64(555),
        expected_iterations,
    );
}
