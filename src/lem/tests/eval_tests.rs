use expect_test::{expect, Expect};
use pasta_curves::pallas::Scalar as Fr;
use std::{cell::RefCell, rc::Rc};

use crate::{
    coprocessor::Coprocessor,
    eval::lang::{Coproc, Lang},
    lem::{
        eval::{evaluate_simple, make_eval_step_from_config, EvalConfig},
        pointers::Ptr,
        store::Store,
        Tag,
    },
    state::State,
    tag::Op,
};

fn test_aux<C: Coprocessor<Fr>>(
    s: &Store<Fr>,
    expr: &str,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<Vec<Ptr>>,
    expected_iterations: &Expect,
    lang: &Option<&Lang<Fr, C>>,
) {
    let ptr = s.read_with_default_state(expr).unwrap();
    do_test_aux(
        s,
        &ptr,
        expected_result,
        expected_env,
        expected_cont,
        expected_emitted,
        expected_iterations,
        lang,
    );
}

fn test_aux_with_state<C: Coprocessor<Fr>>(
    s: &Store<Fr>,
    state: Rc<RefCell<State>>,
    expr: &str,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<Vec<Ptr>>,
    expected_iterations: &Expect,
    lang: &Option<&Lang<Fr, C>>,
) {
    let ptr = s.read(state, expr).unwrap();
    do_test_aux(
        s,
        &ptr,
        expected_result,
        expected_env,
        expected_cont,
        expected_emitted,
        expected_iterations,
        lang,
    );
}

#[inline]
fn do_test_aux<C: Coprocessor<Fr>>(
    s: &Store<Fr>,
    ptr: &Ptr,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<Vec<Ptr>>,
    expected_iterations: &Expect,
    lang: &Option<&Lang<Fr, C>>,
) {
    if let Some(lang) = lang {
        do_test(
            s,
            ptr,
            expected_result,
            expected_env,
            expected_cont,
            expected_emitted,
            expected_iterations,
            lang,
        )
    } else {
        let lang = Lang::<Fr, Coproc<Fr>>::new();
        do_test(
            s,
            ptr,
            expected_result,
            expected_env,
            expected_cont,
            expected_emitted,
            expected_iterations,
            &lang,
        )
    }
}

fn do_test<C: Coprocessor<Fr>>(
    s: &Store<Fr>,
    expr: &Ptr,
    expected_result: Option<Ptr>,
    expected_env: Option<Ptr>,
    expected_cont: Option<Ptr>,
    expected_emitted: Option<Vec<Ptr>>,
    expected_iterations: &Expect,
    lang: &Lang<Fr, C>,
) {
    let limit = 100000;
    let (output, iterations, emitted) = if lang.is_default() {
        evaluate_simple::<Fr, C>(None, *expr, s, limit).unwrap()
    } else {
        let func = make_eval_step_from_config(&EvalConfig::new_ivc(lang));
        evaluate_simple(Some((&func, lang)), *expr, s, limit).unwrap()
    };
    let new_expr = output[0];
    let new_env = output[1];
    let new_cont = output[2];

    if let Some(expected_result) = expected_result {
        assert!(s.ptr_eq(&expected_result, &new_expr));
    }
    if let Some(expected_env) = expected_env {
        assert!(s.ptr_eq(&expected_env, &new_env));
    }
    if let Some(expected_cont) = expected_cont {
        assert_eq!(expected_cont, new_cont);
    } else {
        assert_eq!(s.cont_terminal(), new_cont);
    }
    if let Some(expected_emitted) = expected_emitted {
        assert_eq!(expected_emitted.len(), emitted.len());

        assert!(expected_emitted
            .iter()
            .zip(emitted)
            .all(|(a, b)| s.ptr_eq(a, &b)));
    }
    let data = expected_iterations.data().parse::<usize>().unwrap();
    assert!(iterations <= data);
    expected_iterations.assert_eq(&iterations.to_string())
}

#[test]
fn self_evaluating() {
    let s = &Store::<Fr>::default();
    let expr_num = "999";
    let expt_num = s.num_u64(999);

    let expr_u64 = "999u64";
    let expt_u64 = s.u64(999);

    let expr_char = "'a'";
    let expt_char = s.char('a');

    let expr_str = "\"abc\"";
    let expt_str = s.intern_string("abc");

    let expr_nil = "nil";
    let expt_nil = s.intern_nil();

    let expr_t = "t";
    let expt_t = s.intern_lurk_symbol("t");

    let expr_key = ":key";
    let expt_key = s.key("key");

    [
        (expr_num, expt_num),
        (expr_u64, expt_u64),
        (expr_char, expt_char),
        (expr_str, expt_str),
        (expr_nil, expt_nil),
        (expr_t, expt_t),
        (expr_key, expt_key),
    ]
    .into_iter()
    .for_each(|(expr, expt)| {
        test_aux::<Coproc<Fr>>(s, expr, Some(expt), None, None, None, &expect!["1"], &None);
    });

    let fun = s.intern_fun(s.intern_user_symbol("x"), s.list(vec![expt_nil]), expt_nil);
    do_test_aux::<Coproc<Fr>>(s, &fun, Some(fun), None, None, None, &expect!["1"], &None);
}

#[test]
fn evaluate_cons() {
    let s = &Store::<Fr>::default();
    let expr = "(cons 1 2)";

    let car = s.num_u64(1);
    let cdr = s.num_u64(2);
    let expected = s.cons(car, cdr);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn emit_output() {
    let s = &Store::<Fr>::default();
    let expr = "(emit 123)";
    let expected = s.num_u64(123);
    let emitted = vec![expected];
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        Some(emitted),
        &expect!["3"],
        &None,
    );
}

#[test]
fn evaluate_lambda() {
    let s = &Store::<Fr>::default();
    let expr = "((lambda (x) x) 123)";

    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["4"],
        &None,
    );
}

#[test]
fn evaluate_empty_args_lambda() {
    let s = &Store::<Fr>::default();
    let expr = "((lambda () 123))";

    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn evaluate_lambda2() {
    let s = &Store::<Fr>::default();
    let expr = "((lambda (y) ((lambda (x) y) 321)) 123)";

    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["9"],
        &None,
    );
}

#[test]
fn evaluate_lambda3() {
    let s = &Store::<Fr>::default();
    let expr = "((lambda (y) ((lambda (x) ((lambda (z) z) x)) y)) 123)";

    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["10"],
        &None,
    );
}

#[test]
fn evaluate_lambda4() {
    let s = &Store::<Fr>::default();
    let expr =
        // NOTE: We pass two different values. This tests which is returned.
            "((lambda (y) ((lambda (x) ((lambda (z) z) x)) 888)) 999)";

    let expected = s.num_u64(888);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["10"],
        &None,
    );
}

#[test]
fn evaluate_lambda5() {
    let s = &Store::<Fr>::default();
    let expr =
        // Bind a function to the name FN, then call it.
            "(((lambda (fn) (lambda (x) (fn x))) (lambda (y) y)) 999)";

    let expected = s.num_u64(999);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["13"],
        &None,
    );
}

#[test]
fn evaluate_sum() {
    let s = &Store::<Fr>::default();
    let expr = "(+ 2 (+ 3 4))";

    let expected = s.num_u64(9);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["6"],
        &None,
    );
}

#[test]
fn evaluate_diff() {
    let s = &Store::<Fr>::default();
    let expr = "(- 9 5)";

    let expected = s.num_u64(4);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn evaluate_product() {
    let s = &Store::<Fr>::default();
    let expr = "(* 9 5)";

    let expected = s.num_u64(45);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn evaluate_quotient() {
    let s = &Store::<Fr>::default();
    let expr = "(/ 21 7)";

    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn evaluate_quotient_divide_by_zero() {
    let s = &Store::<Fr>::default();
    let expr = "(/ 21 0)";

    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["3"], &None);
}

#[test]
fn evaluate_num_equal() {
    let s = &Store::<Fr>::default();

    {
        let expr = "(= 5 5)";

        let expected = s.intern_lurk_symbol("t");
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
    {
        let expr = "(= 5 6)";

        let expected = s.intern_nil();
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
}

#[test]
fn evaluate_adder1() {
    let s = &Store::<Fr>::default();
    let expr = "(((lambda (x) (lambda (y) (+ x y))) 2) 3)";

    let expected = s.num_u64(5);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["13"],
        &None,
    );
}

// Enable this when we have LET.
#[test]
fn evaluate_adder2() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((make-adder (lambda (x) (lambda (y) (+ x y)))))
                   ((make-adder 2) 3))";

    let expected = s.num_u64(5);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["15"],
        &None,
    );
}

#[test]
fn evaluate_let_simple() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((a 1)) a)";

    let expected = s.num_u64(1);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn evaluate_empty_let_bug() {
    let s = &Store::<Fr>::default();
    let expr = "(let () (+ 1 2))";

    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["4"],
        &None,
    );
}

#[test]
fn evaluate_let() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((a 1)
                        (b 2))
                   (+ a b))";

    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["10"],
        &None,
    );
}

#[test]
fn evaluate_let_empty_error() {
    let s = &Store::<Fr>::default();
    let expr = "(let)";

    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn evaluate_let_empty_body_error() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((a 1)))";

    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn evaluate_letrec_empty_error() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec)";

    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn evaluate_letrec_empty_body_error() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((a 1)))";

    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn evaluate_letrec_body_nil() {
    let s = &Store::<Fr>::default();
    let expr = "(eq nil (let () nil))";

    let expected = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["4"],
        &None,
    );
}

#[test]
fn evaluate_let_parallel_binding() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((a 1) (b a)) b)";

    let expected = s.num_u64(1);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["5"],
        &None,
    );
}

#[test]
fn evaluate_arithmetic_let() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((a 5)
                        (b 1)
                        (c 2))
                   (/ (+ a b) c))";

    let expected = s.num_u64(3);
    let new_env = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        Some(new_env),
        Some(terminal),
        None,
        &expect!["18"],
        &None,
    );
}

#[test]
// Not because it's efficient, but to prove we can.
fn evaluate_fundamental_conditional() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(let ((true (lambda (a)
                                    (lambda (b)
                                      a)))
                            (false (lambda (a)
                                     (lambda (b)
                                      b)))
                            (iff (lambda (a)
                                   (lambda (b)
                                     (lambda (cond)
                                       ((cond a) b))))))
                       (((iff 5) 6) true))";

        let expected = s.num_u64(5);
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["35"],
            &None,
        );
    }
    {
        let s = &Store::<Fr>::default();
        let expr = "(let ((true (lambda (a)
                                    (lambda (b)
                                   a)))
                            (false (lambda (a)
                                  (lambda (b)
                                   b)))
                            (iff (lambda (a)
                                   (lambda (b)
                                     (lambda (cond)
                                       ((cond a) b))))))
                       (((iff 5) 6) false))";

        let expected = s.num_u64(6);
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["32"],
            &None,
        );
    }
}

#[test]
fn evaluate_if() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(if t 5 6)";

        let expected = s.num_u64(5);
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
    {
        let s = &Store::<Fr>::default();
        let expr = "(if nil 5 6)";

        let expected = s.num_u64(6);
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
}

#[test]
fn evaluate_fully_evaluates() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(if t (+ 5 5) 6)";

        let expected = s.num_u64(10);
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["5"],
            &None,
        );
    }
}

#[test]
fn evaluate_recursion1() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base)
                                  (lambda (exponent)
                                    (if (= 0 exponent)
                                        1
                                        (* base ((exp base) (- exponent 1))))))))
                   ((exp 5) 3))";

    let expected = s.num_u64(125);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["91"],
        &None,
    );
}

#[test]
fn evaluate_recursion2() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base)
                                  (lambda (exponent)
                                     (lambda (acc)
                                       (if (= 0 exponent)
                                          acc
                                          (((exp base) (- exponent 1)) (* acc base))))))))
                   (((exp 5) 5) 1))";

    let expected = s.num_u64(3125);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["201"],
        &None,
    );
}

#[test]
fn evaluate_recursion_multiarg() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp base (- exponent 1)))))))
                          (exp 5 3))";

    let expected = s.num_u64(125);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["95"],
        &None,
    );
}

#[test]
fn evaluate_recursion_optimized() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((exp (lambda (base)
                               (letrec ((base-inner
                                          (lambda (exponent)
                                            (if (= 0 exponent)
                                                1
                                                (* base (base-inner (- exponent 1)))))))
                                        base-inner))))
                    ((exp 5) 3))";

    let expected = s.num_u64(125);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["75"],
        &None,
    );
}

#[test]
fn evaluate_tail_recursion() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base)
                                  (lambda (exponent-remaining)
                                    (lambda (acc)
                                      (if (= 0 exponent-remaining)
                                          acc
                                          (((exp base) (- exponent-remaining 1)) (* acc base))))))))
                          (((exp 5) 3) 1))";

    let expected = s.num_u64(125);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["129"],
        &None,
    );
}

#[test]
fn evaluate_tail_recursion_somewhat_optimized() {
    let s = &Store::<Fr>::default();
    let expr =
            "(letrec ((exp (lambda (base)
                             (letrec ((base-inner
                                        (lambda (exponent-remaining)
                                          (lambda (acc)
                                            (if (= 0 exponent-remaining)
                                              acc
                                             ((base-inner (- exponent-remaining 1)) (* acc base)))))))
                                      base-inner))))
                   (((exp 5) 3) 1))";

    let expected = s.num_u64(125);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["110"],
        &None,
    );
}

#[test]
fn evaluate_multiple_letrec_bindings() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((double (lambda (x) (* 2 x)))
                           (square (lambda (x) (* x x))))
                   (+ (square 3) (double 2)))";

    let expected = s.num_u64(13);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["22"],
        &None,
    );
}

#[test]
fn evaluate_multiple_letrec_bindings_referencing() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((double (lambda (x) (* 2 x)))
                           (double-inc (lambda (x) (+ 1 (double x)))))
                   (+ (double 3) (double-inc 2)))";

    let expected = s.num_u64(11);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["31"],
        &None,
    );
}

#[test]
fn evaluate_multiple_letrec_bindings_recursive() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp base (- exponent 1))))))
                           (exp2 (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp2 base (- exponent 1))))))
                           (exp3 (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp3 base (- exponent 1)))))))
                   (+ (+ (exp 3 2) (exp2 2 3))
                      (exp3 4 2)))";

    let expected = s.num_u64(33);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["242"],
        &None,
    );
}

#[test]
fn nested_let_closure_regression() {
    let s = &Store::<Fr>::default();
    let terminal = s.cont_terminal();
    let expected = s.num_u64(6);

    {
        // This always works.
        let expr = "(let ((x 6)
                              (data-function (lambda () 123))
                              (data (data-function)))
                          x)";
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["13"],
            &None,
        );
    }
    {
        // This fails if zero-arg functions don't save and restore the env.
        let expr = "(let ((data-function (lambda () 123))
                              (x 6)
                              (data (data-function)))
                          x)";
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["14"],
            &None,
        );
    }
}

#[test]
fn evaluate_eq() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(eq 'a 'a)";

        let expected = s.intern_lurk_symbol("t");
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
    {
        let s = &Store::<Fr>::default();
        let expr = "(eq 1 1)";

        let expected = s.intern_lurk_symbol("t");
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
    {
        let s = &Store::<Fr>::default();
        let expr = "(eq 'a 1)";

        let expected = s.intern_nil();
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }

    {
        let s = &Store::<Fr>::default();
        let expr = "(eq 1 'a)";

        let expected = s.intern_nil();
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
}

#[test]
fn evaluate_zero_arg_lambda() {
    let s = &Store::<Fr>::default();
    let terminal = s.cont_terminal();
    {
        let expr = "((lambda () 123))";

        let expected = s.num_u64(123);
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
    {
        let expected = {
            let arg = s.intern_user_symbol("x");
            let num = s.num_u64(123);
            let body = s.list(vec![num]);
            let env = s.intern_nil();
            s.intern_fun(arg, body, env)
        };

        // One arg expected but zero supplied.
        let expr = "((lambda (x) 123))";
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
    {
        let expr = "(letrec ((x 9) (f (lambda () (+ x 1)))) (f))";

        let expected = s.num_u64(10);
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["12"],
            &None,
        );
    }
}

#[test]
fn evaluate_zero_arg_lambda_variants() {
    {
        let s = &Store::<Fr>::default();
        let expr = "((lambda () 123) 1)";

        let error = s.cont_error();
        test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["3"], &None);
    }
    {
        let s = &Store::<Fr>::default();
        let expr = "(123)";

        let error = s.cont_error();
        test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
    }
}

#[test]
fn evaluate_make_tree() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(letrec ((mapcar (lambda (f list)
                                                        (if (eq list nil)
                                                            nil
                                                            (cons (f (car list)) (mapcar f (cdr list))))))
                                    (make-row (lambda (list)
                                                (if (eq list nil)
                                                    nil
                                                    (let ((cdr (cdr list)))
                                                    (cons (cons (car list) (car cdr))
                                                            (make-row (cdr cdr)))))))
                                    (make-tree-aux (lambda (list)
                                                    (let ((row (make-row list)))
                                                    (if (eq (cdr row) nil)
                                                        row
                                                        (make-tree-aux row)))))
                                    (make-tree (lambda (list)
                                                (car (make-tree-aux list))))
                                    (reverse-tree (lambda (tree)
                                                    (if (atom tree)
                                                        tree
                                                        (cons (reverse-tree (cdr tree))
                                                            (reverse-tree (car tree)))))))
                        (reverse-tree (make-tree '(a b c d e f g h))))";

        let expected = s
            .read_with_default_state("(((h . g) . (f . e)) . ((d . c) . (b . a)))")
            .unwrap();
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["493"],
            &None,
        );
    }
}

#[test]
fn evaluate_make_tree_minimal_regression() {
    let s = &Store::<Fr>::default();
    let limit = 100;
    let expr = s
        .read_with_default_state(
            "(letrec ((fn-1 (lambda (x)
                                    (let ((y x))
                                       y)))
                               (fn-2 (lambda (list)
                                       (let ((z (fn-1 list)))
                                         (fn-2 z)))))
                                 (fn-2 '(a b c d e f g h)))",
        )
        .unwrap();

    let (_, iterations, _) = evaluate_simple::<Fr, Coproc<Fr>>(None, expr, s, limit).unwrap();
    assert_eq!(100, iterations);
}

#[test]
fn evaluate_map_tree_bug() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(letrec ((map-tree (lambda (f tree)
                      (if (atom tree)
                          (f tree)
                          (cons (map-tree f (car tree))
                                (map-tree f (cdr tree)))))))
         (map-tree (lambda (x) (+ 1 x)) '((1 . 2) . (3 . 4))))";

        let expected = s.read_with_default_state("((2 . 3) . (4 . 5))").unwrap();
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["170"],
            &None,
        );
    }
}

#[test]
fn evaluate_map_tree_numequal_bug() {
    {
        // Reuse map-tree failure case to test Relop behavior.
        // This failed initially and tests regression.
        let s = &Store::<Fr>::default();
        let expr = "(letrec ((map-tree (lambda (f tree)
                                           (if (atom tree)
                                             (f tree)
                                               (= (map-tree f (car tree))
                                                  (map-tree f (cdr tree)))))))
                       (map-tree (lambda (x) (+ 1 x)) '((1 . 2) . (3 . 4))))";
        let expected = s.intern_nil();
        let error = s.cont_error();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(error),
            None,
            &expect!["169"],
            &None,
        );
    }
}

#[test]
fn env_lost_bug() {
    {
        // previously, an unbound variable `u` error
        let s = &Store::<Fr>::default();
        let expr = "
(letrec
    (
     (id
      (lambda (x) x))
     (id2
      (lambda (x) (id x)))
     (foo
      (lambda (u)
        (if (id2 0)
            u
            0)))
     )
  (foo '()))
";
        let expected = s.intern_nil();
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["25"],
            &None,
        );
    }
}

#[test]
fn dont_discard_rest_env() {
    {
        // previously: Unbound variable: Sym("Z")
        let s = &Store::<Fr>::default();
        let expr = "(let ((z 9))
                       (letrec ((a 1)
                                 (b 2)
                                 (l (lambda (x) (+ z x))))
                         (l 9)))";
        let expected = s.num_u64(18);
        let terminal = s.cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            &expect!["22"],
            &None,
        );
    }
}

#[test]
fn test_str_car_cdr_cons() {
    let s = &Store::<Fr>::default();
    let state = State::init_lurk_state().rccell();
    let a = s.read(state.clone(), r"#\a").unwrap();
    let apple = s.read(state.clone(), r#" "apple" "#).unwrap();
    let a_pple = s.read(state.clone(), r#" (#\a . "pple") "#).unwrap();
    let pple = s.read(state, r#" "pple" "#).unwrap();
    let empty = s.intern_string("");
    let nil = s.intern_nil();
    let terminal = s.cont_terminal();
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(
        s,
        r#"(car "apple")"#,
        Some(a),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr "apple")"#,
        Some(pple),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(car "")"#,
        Some(nil),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr "")"#,
        Some(empty),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cons #\a "pple")"#,
        Some(a_pple),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(strcons #\a "pple")"#,
        Some(apple),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r"(strcons #\a #\b)",
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(strcons "a" "b")"#,
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(strcons 1 2)"#,
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(strcons)"#,
        None,
        None,
        Some(error),
        None,
        &expect!["1"],
        &None,
    );
}

#[test]
fn test_one_arg_cons_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cons "")"#,
        None,
        None,
        Some(error),
        None,
        &expect!["1"],
        &None,
    );
}

#[test]
fn test_car_nil() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(car nil)"#,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn test_cdr_nil() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr nil)"#,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn test_car_cdr_invalid_tag_error_sym() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(car 'car)"#,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr 'car)"#,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn test_car_cdr_invalid_tag_error_char() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(
        s,
        r"(car #\a)",
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r"(cdr #\a)",
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn test_car_cdr_invalid_tag_error_num() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(car 42)"#,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr 42)"#,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn test_car_cdr_invalid_tag_error_lambda() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(car (lambda (x) x))"#,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr (lambda (x) x))"#,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn go_translate() {
    // func Foo(a int, b int) int {
    //     x := a * b + 4
    //     for i := 0; i < b; i++ {
    //         x += a
    //         a += b * 2
    //    }
    //    return x
    // }

    let s = &Store::<Fr>::default();
    let n = s.num_u64(0x1044);
    test_aux::<Coproc<Fr>>(
        s,
        r#"
(let ((foo (lambda (a b)
              (letrec ((aux (lambda (i a x)
                               (if (= i b)
                                     x
                                     (let ((x (+ x a))
                                            (a (+ a (* b 2))))
                                       (aux (+ i 1) a x))))))
                       (let ((x (+ (* a b) 4)))
                         (aux 0 a x))))))
  (foo 10 16))
"#,
        Some(n),
        None,
        None,
        None,
        &expect!["1114"],
        &None,
    );
}

#[test]
fn begin_current_env() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(begin (current-env))";
        let expected = s.intern_nil();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            None,
            None,
            &expect!["2"],
            &None,
        );
    }
}

#[test]
fn begin() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(car (begin 1 2 '(3 . 4)))";
        let expected = s.num_u64(3);
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            None,
            None,
            &expect!["6"],
            &None,
        );
    }
}

#[test]
fn begin_current_env1() {
    {
        let s = &Store::<Fr>::default();
        let expr = "(let ((a 1))
                       (begin 123 (current-env)))";
        let a = s.intern_user_symbol("a");
        let one = s.num_u64(1);
        let binding = s.cons(a, one);
        let expected = s.list(vec![binding]);
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            None,
            None,
            &expect!["5"],
            &None,
        );
    }
}

#[test]
fn hide_open() {
    let s = &Store::<Fr>::default();
    let expr = "(open (hide 123 'x))";
    let x = s.intern_user_symbol("x");
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, None, None, &expect!["5"], &None);
}

#[test]
fn hide_opaque_open_available() {
    let s = &Store::<Fr>::default();
    let expr = s.read_with_default_state("(hide 123 'x)").unwrap();
    let (output, ..) = evaluate_simple::<Fr, Coproc<Fr>>(None, expr, s, 10).unwrap();

    let c = *s.hash_ptr(&output[0]).value();
    let comm = s.comm(c);

    let open = s.intern_lurk_symbol("open");
    let x = s.intern_user_symbol("x");
    let lang = Lang::new();

    {
        let expr = s.list(vec![open, comm]);
        do_test::<Coproc<Fr>>(s, &expr, Some(x), None, None, None, &expect!["2"], &lang);
    }

    {
        let secret = s.intern_lurk_symbol("secret");
        let expr = s.list(vec![secret, comm]);
        let sec = s.num_u64(123);
        do_test::<Coproc<Fr>>(s, &expr, Some(sec), None, None, None, &expect!["2"], &lang);
    }

    {
        // We can open a commitment identified by its corresponding `Num`.
        let comm_num = s.num(c);
        let expr2 = s.list(vec![open, comm_num]);
        do_test::<Coproc<Fr>>(s, &expr2, Some(x), None, None, None, &expect!["2"], &lang);
    }
}

#[test]
#[should_panic]
fn hide_opaque_open_unavailable() {
    let s = &Store::<Fr>::default();
    let expr = s.read_with_default_state("(hide 123 'x)").unwrap();
    let (output, ..) = evaluate_simple::<Fr, Coproc<Fr>>(None, expr, s, 10).unwrap();

    let c = *s.hash_ptr(&output[0]).value();

    let s2 = &Store::<Fr>::default();
    let comm = s.comm(c);
    let open = s2.intern_lurk_symbol("open");
    let x = s2.intern_user_symbol("x");

    let expr = s2.list(vec![open, comm]);
    let lang = Lang::new();

    do_test::<Coproc<Fr>>(s2, &expr, Some(x), None, None, None, &expect!["2"], &lang);
}

#[test]
fn commit_open_sym() {
    let s = &Store::<Fr>::default();
    let expr = "(open (commit 'x))";
    let x = s.intern_user_symbol("x");
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, None, None, &expect!["4"], &None);
}

#[test]
fn commitment_value() {
    let s = &Store::<Fr>::default();
    let expr = "(num (commit 123))";
    let x = s
        .read_with_default_state(
            "0x2937881eff06c2bcc2c8c1fa0818ae3733c759376f76fc10b7439269e9aaa9bc",
        )
        .unwrap();
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, None, None, &expect!["4"], &None);
}

#[test]
fn commit_nil() {
    let s = &Store::<Fr>::default();
    let x = s
        .read_with_default_state(
            "0x1f7f3e554ed27c104d79bb69346996d61a735d5bbedc2da7da2935036d9c4fad",
        )
        .unwrap();

    let expr = "(num (commit nil))";
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, None, None, &expect!["4"], &None);

    let expr = "(num (commit '.lurk.nil))";
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, None, None, &expect!["4"], &None);
}

#[test]
fn commit_error() {
    let s = &Store::<Fr>::default();
    let expr = "(commit 123 456)";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn open_error() {
    let s = &Store::<Fr>::default();
    let expr = "(open 123 456)";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn secret_error() {
    let s = &Store::<Fr>::default();
    let expr = "(secret 123 456)";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn num_error() {
    let s = &Store::<Fr>::default();
    let expr = "(num 123 456)";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn comm_error() {
    let s = &Store::<Fr>::default();
    let expr = "(comm 123 456)";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn char_error() {
    let s = &Store::<Fr>::default();
    let expr = "(char 123 456)";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["1"], &None);
}

#[test]
fn prove_commit_secret() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (commit 123))";
    let expected = s.num_u64(0);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["4"],
        &None,
    );
}

#[test]
fn num() {
    let s = &Store::<Fr>::default();
    let expr = "(num 123)";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn num_char() {
    let s = &Store::<Fr>::default();
    let expr = r"(num #\a)";
    let expected = s.num_u64(97);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn char_num() {
    let s = &Store::<Fr>::default();
    let expr = r#"(char 97)"#;
    let expected_a = s.read_with_default_state(r"#\a").unwrap();
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected_a),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn char_coercion() {
    let s = &Store::<Fr>::default();
    let expr = r#"(char (- 0 4294967200))"#;
    let expected_a = s.read_with_default_state(r"#\a").unwrap();
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected_a),
        None,
        Some(terminal),
        None,
        &expect!["5"],
        &None,
    );
}

#[test]
fn commit_num() {
    let s = &Store::<Fr>::default();
    let expr = "(num (commit 123))";
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        None,
        None,
        Some(terminal),
        None,
        &expect!["4"],
        &None,
    );
}

#[test]
fn hide_open_comm_num() {
    let s = &Store::<Fr>::default();
    let expr = "(open (comm (num (hide 123 456))))";
    let expected = s.num_u64(456);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["9"],
        &None,
    );
}

#[test]
fn hide_secret_comm_num() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (comm (num (hide 123 456))))";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["9"],
        &None,
    );
}

#[test]
fn commit_open_comm_num() {
    let s = &Store::<Fr>::default();
    let expr = "(open (comm (num (commit 123))))";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["8"],
        &None,
    );
}

#[test]
fn commit_secret_comm_num() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (comm (num (commit 123))))";
    let expected = s.num_u64(0);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["8"],
        &None,
    );
}

#[test]
fn commit_num_open() {
    let s = &Store::<Fr>::default();
    let expr = "(open (num (commit 123)))";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["6"],
        &None,
    );
}

#[test]
fn num_invalid_tag() {
    let s = &Store::<Fr>::default();
    let expr = "(num (quote x))";
    let expr1 = "(num \"asdf\")";
    let expr2 = "(num '(1))";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["2"], &None);
    test_aux::<Coproc<Fr>>(
        s,
        expr1,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn comm_invalid_tag() {
    let s = &Store::<Fr>::default();
    let expr = "(comm (quote x))";
    let expr1 = "(comm \"asdf\")";
    let expr2 = "(comm '(1))";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["2"], &None);
    test_aux::<Coproc<Fr>>(
        s,
        expr1,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn char_invalid_tag() {
    let s = &Store::<Fr>::default();
    let expr = "(char (quote x))";
    let expr1 = "(char \"asdf\")";
    let expr2 = "(char '(1))";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["2"], &None);
    test_aux::<Coproc<Fr>>(
        s,
        expr1,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
}

#[test]
fn terminal_sym() {
    let s = &Store::<Fr>::default();
    let expr = "(quote x)";
    let x = s.intern_user_symbol("x");
    let terminal = s.cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(x),
        None,
        Some(terminal),
        None,
        &expect!["1"],
        &None,
    );
}

#[test]
#[should_panic = "No committed data for hash 000000000000000000000000000000000000000000000000000000000000007b"]
fn open_opaque_commit() {
    let s = &Store::<Fr>::default();
    let expr = "(open 123)";
    test_aux::<Coproc<Fr>>(s, expr, None, None, None, None, &expect!["2"], &None);
}

#[test]
fn open_wrong_type() {
    let s = &Store::<Fr>::default();
    let expr = "(open 'asdf)";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["2"], &None);
}

#[test]
fn secret_wrong_type() {
    let s = &Store::<Fr>::default();
    let expr = "(secret 'asdf)";
    let error = s.cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["2"], &None);
}

#[test]
#[should_panic]
fn secret_invalid_tag() {
    let s = &Store::<Fr>::default();
    let expr = "(secret 123)";
    test_aux::<Coproc<Fr>>(s, expr, None, None, None, None, &expect!["2"], &None);
}

#[test]
#[should_panic = "No committed data for hash 000000000000000000000000000000000000000000000000000000000000007b"]
fn secret_opaque_commit() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (comm 123))";
    test_aux::<Coproc<Fr>>(s, expr, None, None, None, None, &expect!["2"], &None);
}

#[allow(dead_code)]
fn relational_aux(s: &Store<Fr>, op: &str, a: &str, b: &str, res: bool) {
    let expr = &format!("({op} {a} {b})");
    let expected = if res {
        s.intern_lurk_symbol("t")
    } else {
        s.intern_nil()
    };
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_relational() {
    let s = &Store::<Fr>::default();
    let lt = "<";
    let gt = ">";
    let lte = "<=";
    let gte = ">=";
    let zero = "0";
    let one = "1";
    let two = "2";

    use crate::Num;

    let most_negative = &format!("{}", Num::<Fr>::most_negative());
    let most_positive = &format!("{}", Num::<Fr>::most_positive());

    let neg_one = &format!("{}", Num::<Fr>::Scalar(Fr::zero() - Fr::one()));

    relational_aux(s, lt, one, two, true);
    relational_aux(s, gt, one, two, false);
    relational_aux(s, lte, one, two, true);
    relational_aux(s, gte, one, two, false);

    relational_aux(s, lt, two, one, false);
    relational_aux(s, gt, two, one, true);
    relational_aux(s, lte, two, one, false);
    relational_aux(s, gte, two, one, true);

    relational_aux(s, lt, one, one, false);
    relational_aux(s, gt, one, one, false);
    relational_aux(s, lte, one, one, true);
    relational_aux(s, gte, one, one, true);

    relational_aux(s, lt, zero, two, true);
    relational_aux(s, gt, zero, two, false);
    relational_aux(s, lte, zero, two, true);
    relational_aux(s, gte, zero, two, false);

    relational_aux(s, lt, two, zero, false);
    relational_aux(s, gt, two, zero, true);
    relational_aux(s, lte, two, zero, false);
    relational_aux(s, gte, two, zero, true);

    relational_aux(s, lt, zero, zero, false);
    relational_aux(s, gt, zero, zero, false);
    relational_aux(s, lte, zero, zero, true);
    relational_aux(s, gte, zero, zero, true);

    relational_aux(s, lt, most_negative, zero, true);
    relational_aux(s, gt, most_negative, zero, false);
    relational_aux(s, lte, most_negative, zero, true);
    relational_aux(s, gte, most_negative, zero, false);

    relational_aux(s, lt, zero, most_negative, false);
    relational_aux(s, gt, zero, most_negative, true);
    relational_aux(s, lte, zero, most_negative, false);
    relational_aux(s, gte, zero, most_negative, true);

    relational_aux(s, lt, most_negative, most_positive, true);
    relational_aux(s, gt, most_negative, most_positive, false);
    relational_aux(s, lte, most_negative, most_positive, true);
    relational_aux(s, gte, most_negative, most_positive, false);

    relational_aux(s, lt, most_positive, most_negative, false);
    relational_aux(s, gt, most_positive, most_negative, true);
    relational_aux(s, lte, most_positive, most_negative, false);
    relational_aux(s, gte, most_positive, most_negative, true);

    relational_aux(s, lt, most_negative, most_negative, false);
    relational_aux(s, gt, most_negative, most_negative, false);
    relational_aux(s, lte, most_negative, most_negative, true);
    relational_aux(s, gte, most_negative, most_negative, true);

    relational_aux(s, lt, one, most_positive, true);
    relational_aux(s, gt, one, most_positive, false);
    relational_aux(s, lte, one, most_positive, true);
    relational_aux(s, gte, one, most_positive, false);

    relational_aux(s, lt, most_positive, one, false);
    relational_aux(s, gt, most_positive, one, true);
    relational_aux(s, lte, most_positive, one, false);
    relational_aux(s, gte, most_positive, one, true);

    relational_aux(s, lt, one, most_negative, false);
    relational_aux(s, gt, one, most_negative, true);
    relational_aux(s, lte, one, most_negative, false);
    relational_aux(s, gte, one, most_negative, true);

    relational_aux(s, lt, most_negative, one, true);
    relational_aux(s, gt, most_negative, one, false);
    relational_aux(s, lte, most_negative, one, true);
    relational_aux(s, gte, most_negative, one, false);

    relational_aux(s, lt, neg_one, most_positive, true);
    relational_aux(s, gt, neg_one, most_positive, false);
    relational_aux(s, lte, neg_one, most_positive, true);
    relational_aux(s, gte, neg_one, most_positive, false);

    relational_aux(s, lt, most_positive, neg_one, false);
    relational_aux(s, gt, most_positive, neg_one, true);
    relational_aux(s, lte, most_positive, neg_one, false);
    relational_aux(s, gte, most_positive, neg_one, true);

    relational_aux(s, lt, neg_one, most_negative, false);
    relational_aux(s, gt, neg_one, most_negative, true);
    relational_aux(s, lte, neg_one, most_negative, false);
    relational_aux(s, gte, neg_one, most_negative, true);

    relational_aux(s, lt, most_negative, neg_one, true);
    relational_aux(s, gt, most_negative, neg_one, false);
    relational_aux(s, lte, most_negative, neg_one, true);
    relational_aux(s, gte, most_negative, neg_one, false);
}

#[test]
fn test_relational_edge_case_identity() {
    let s = &Store::<Fr>::default();
    let t = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();

    // Normally, a value cannot be less than the result of incrementing it.
    // However, the most positive field element (when viewed as signed)
    // is the exception. Incrementing it yields the most negative element,
    // which is less than the most positive.
    {
        let expr = "(let ((most-positive (/ (- 0 1) 2))
                          (most-negative (+ 1 most-positive)))
                      (< most-negative most-positive))";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["19"],
            &None,
        );
    }

    // Regression: comparisons with negative numbers should *not* be exceptions.
    {
        let expr = "(let ((most-positive (/ (- 0 1) 2))
                              (most-negative (+ 1 most-positive))
                              (less-negative (+ 1 most-negative)))
                      (< most-negative  less-negative)) ";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["24"],
            &None,
        );
    }
}

#[test]
fn test_num_syntax_implications() {
    let s = &Store::<Fr>::default();
    let t = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();

    {
        let expr = "(let ((most-positive -1/2)
                              (most-negative 1/2))
                          (< most-negative most-positive))";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["10"],
            &None,
        );
    }

    {
        let expr = "(= (* 6 3/2) 9)";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["6"],
            &None,
        );
    }

    {
        let expr = "(= (* 2/3 3/2) 1)";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["6"],
            &None,
        );
    }

    {
        let expr = "(= (* -2/3 3/2) -1)";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["6"],
            &None,
        );
    }

    {
        let expr = "(= (+ 1/3 1/2) 5/6)";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["6"],
            &None,
        );
    }

    // Comparisons of field elements produced by fractional notation don't yield the results
    // their rational equivalents would.
    {
        // This obviously must be true, since 1/2 is the most negative Num,
        // but this violates expectations if you consider 1/2 to behave like a rational.
        let expr = "(< 1/2 1/3)";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }

    {
        // This isn't a weird edge case like the above, but it's also not the behavior
        // expected if fractional notation yielded true rational numbers.
        let expr = "(< 3/4 5/8)";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
    {
        // It's not that they *can't* compare in the naively expected way, though.
        let expr = "(< 3/5 3/4)";

        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(t),
            None,
            Some(terminal),
            None,
            &expect!["3"],
            &None,
        );
    }
}

#[test]
fn test_quoted_symbols() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((|foo bar| 9)
                          (|Foo \\| Bar| (lambda (x) (* x x))))
                      (|Foo \\| Bar| |foo bar|))";
    let res = s.num_u64(81);
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["13"],
        &None,
    );
}

#[test]
fn test_eval() {
    let s = &Store::<Fr>::default();
    let expr = "(* 3 (eval (cons '+ (cons 1 (cons 2 nil)))))";
    let expr2 = "(* 5 (eval '(+ 1 a) '((a . 3))))"; // two-arg eval, optional second arg is env.
    let res = s.num_u64(9);
    let res2 = s.num_u64(20);
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["17"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        &expect!["9"],
        &None,
    );
}

#[test]
fn test_eval_env_regression() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((a 1)) (eval 'a))";
    let expr2 = "(let ((a 1)) (eval 'a (current-env)))";
    let res = s.num_u64(1);
    let error = s.cont_error();
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["5"], &None);
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["6"],
        &None,
    );
}

#[test]
fn test_u64_mul() {
    let s = &Store::<Fr>::default();

    let expr = "(* (u64 18446744073709551615) (u64 2))";
    let expr2 = "(* 18446744073709551615u64 2u64)";
    let expr3 = "(* (- 0u64 1u64) 2u64)";
    let res = s.u64(18446744073709551614);
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["7"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr3,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["6"],
        &None,
    );
}

#[test]
fn test_u64_add() {
    let s = &Store::<Fr>::default();

    let expr = "(+ 18446744073709551615u64 2u64)";
    let expr2 = "(+ (- 0u64 1u64) 2u64)";
    let res = s.u64(1);
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["6"],
        &None,
    );
}

#[test]
fn test_u64_sub() {
    let s = &Store::<Fr>::default();

    let expr = "(- 2u64 1u64)";
    let expr2 = "(- 0u64 1u64)";
    let expr3 = "(+ 1u64 (- 0u64 1u64))";
    let res = s.u64(1);
    let res2 = s.u64(18446744073709551615);
    let res3 = s.u64(0);
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr3,
        Some(res3),
        None,
        Some(terminal),
        None,
        &expect!["6"],
        &None,
    );
}

#[test]
fn test_u64_div() {
    let s = &Store::<Fr>::default();

    let expr = "(/ 100u64 2u64)";
    let res = s.u64(50);

    let expr2 = "(/ 100u64 3u64)";
    let res2 = s.u64(33);

    let expr3 = "(/ 100u64 0u64)";

    let terminal = s.cont_terminal();
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr3,
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_u64_mod() {
    let s = &Store::<Fr>::default();

    let expr = "(% 100u64 2u64)";
    let res = s.u64(0);

    let expr2 = "(% 100u64 3u64)";
    let res2 = s.u64(1);

    let expr3 = "(% 100u64 0u64)";

    let terminal = s.cont_terminal();
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr3,
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_num_mod() {
    let s = &Store::<Fr>::default();

    let expr = "(% 100 3)";
    let expr2 = "(% 100 3u64)";
    let expr3 = "(% 100u64 3)";

    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["3"], &None);
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr3,
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_u64_comp() {
    let s = &Store::<Fr>::default();

    let expr = "(< 0u64 1u64)";
    let expr2 = "(< 1u64 0u64)";
    let expr3 = "(<= 0u64 1u64)";
    let expr4 = "(<= 1u64 0u64)";

    let expr5 = "(> 0u64 1u64)";
    let expr6 = "(> 1u64 0u64)";
    let expr7 = "(>= 0u64 1u64)";
    let expr8 = "(>= 1u64 0u64)";

    let expr9 = "(<= 0u64 0u64)";
    let expr10 = "(>= 0u64 0u64)";

    let expr11 = "(= 0u64 0u64)";
    let expr12 = "(= 0u64 1u64)";

    let t = s.intern_lurk_symbol("t");
    let nil = s.intern_nil();
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(t),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(nil),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr3,
        Some(t),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr4,
        Some(nil),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );

    test_aux::<Coproc<Fr>>(
        s,
        expr5,
        Some(nil),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr6,
        Some(t),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr7,
        Some(nil),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr8,
        Some(t),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );

    test_aux::<Coproc<Fr>>(
        s,
        expr9,
        Some(t),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr10,
        Some(t),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );

    test_aux::<Coproc<Fr>>(
        s,
        expr11,
        Some(t),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr12,
        Some(nil),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_u64_conversion() {
    let s = &Store::<Fr>::default();

    let expr = "(+ 0 1u64)";
    let expr2 = "(num 1u64)";
    let expr3 = "(+ 1 1u64)";
    let expr4 = "(u64 (+ 1 1))";
    let expr5 = "(u64 123u64)";
    let expr6 = "(u64)";
    let expr7 = "(u64 1 1)";

    let res = s.num_u64(1);
    let res2 = s.num_u64(2);
    let res3 = s.u64(2);
    let res5 = s.u64(123);
    let terminal = s.cont_terminal();
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr3,
        Some(res2),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );

    test_aux::<Coproc<Fr>>(
        s,
        expr4,
        Some(res3),
        None,
        Some(terminal),
        None,
        &expect!["5"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr5,
        Some(res5),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr6,
        None,
        None,
        Some(error),
        None,
        &expect!["1"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr7,
        None,
        None,
        Some(error),
        None,
        &expect!["1"],
        &None,
    );
}

#[test]
fn test_numeric_type_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();

    let test = |op| {
        let expr = &format!("({op} 0 'a)");
        let expr2 = &format!("({op} 0u64 'a)");

        test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["3"], &None);
        test_aux::<Coproc<Fr>>(
            s,
            expr2,
            None,
            None,
            Some(error),
            None,
            &expect!["3"],
            &None,
        );
    };

    test("+");
    test("-");
    test("*");
    test("/");
    test("%");
    test(">");
    test("<");
    test(">=");
    test("<=");
    test("=");
}

#[test]
fn test_u64_num_comparison() {
    let s = &Store::<Fr>::default();

    let expr = "(= 1 1u64)";
    let expr2 = "(= 1 2u64)";
    let t = s.intern_lurk_symbol("t");
    let nil = s.intern_nil();
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(t),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(nil),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_u64_num_cons() {
    let s = &Store::<Fr>::default();

    let expr = "(cons 1 1u64)";
    let expr2 = "(cons 1u64 1)";
    let res = s.read_with_default_state("(1 . 1u64)").unwrap();
    let res2 = s.read_with_default_state("(1u64 . 1)").unwrap();
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_hide_u64_secret() {
    let s = &Store::<Fr>::default();

    let expr = "(hide 0u64 123)";
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["3"], &None);
}

#[test]
fn test_keyword() {
    let s = &Store::<Fr>::default();

    let expr = ":asdf";
    let expr2 = "(eq :asdf :asdf)";
    let expr3 = "(eq :asdf 'asdf)";
    let res = s.key("asdf");
    let res2 = s.intern_lurk_symbol("t");
    let res3 = s.intern_nil();

    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["1"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        expr3,
        Some(res3),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_sym_hash_values() {
    use crate::package::Package;
    use crate::Symbol;

    let s = &Store::<Fr>::default();
    let state = State::init_lurk_state().rccell();

    let asdf_sym_package_name = state
        .borrow_mut()
        .intern_path(&["asdf"], false, false)
        .unwrap();
    let asdf_sym_package = Package::new(asdf_sym_package_name);
    state.borrow_mut().add_package(asdf_sym_package);

    let asdf_key_package_name = state
        .borrow_mut()
        .intern_path(&["asdf"], true, false)
        .unwrap();
    let asdf_key_package = Package::new(asdf_key_package_name);
    state.borrow_mut().add_package(asdf_key_package);

    let sym = s.read(state.clone(), ".asdf.fdsa").unwrap();
    let key = s.read(state.clone(), ":asdf.fdsa").unwrap();
    let expr = s.read(state.clone(), "(cons \"fdsa\" '.asdf)").unwrap();

    let limit = 10;
    let (output, ..) = evaluate_simple::<Fr, Coproc<Fr>>(None, expr, s, limit).unwrap();
    let new_expr = output[0];

    let toplevel_sym = s.read(state, ".asdf").unwrap();

    let root_sym = s.intern_symbol(&Symbol::root_sym());

    let asdf = s.intern_string("asdf");
    let consed_with_root = s.cons(asdf, root_sym);

    let cons_z_ptr = &s.hash_ptr(&new_expr);
    let sym_z_ptr = &s.hash_ptr(&sym);
    let key_z_ptr = &s.hash_ptr(&key);

    let consed_with_root_z_ptr = &s.hash_ptr(&consed_with_root);
    let toplevel_z_ptr = &s.hash_ptr(&toplevel_sym);

    // Symbol and keyword scalar hash values are the same as
    // those of the name string consed onto the parent symbol.
    assert_eq!(cons_z_ptr.value(), sym_z_ptr.value());
    assert_eq!(cons_z_ptr.value(), key_z_ptr.value());

    // Toplevel symbols also have this property, and their parent symbol is the root symbol.
    assert_eq!(consed_with_root_z_ptr.value(), toplevel_z_ptr.value());

    // The tags differ though.
    use crate::tag::ExprTag::{Key, Sym};
    assert_eq!(&Tag::Expr(Sym), sym_z_ptr.tag());
    assert_eq!(&Tag::Expr(Key), key_z_ptr.tag());
}

#[test]
fn test_fold_cons_regression() {
    let s = &Store::<Fr>::default();

    let expr = "(letrec ((fold (lambda (op acc l)
                                     (if l
                                         (fold op (op acc (car l)) (cdr l))
                                         acc))))
                      (fold (lambda (x y) (+ x y)) 0 '(1 2 3)))";
    let res = s.num_u64(6);
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["152"],
        &None,
    );
}

#[test]
fn test_lambda_args_regression() {
    let s = &Store::<Fr>::default();

    let expr = "(cons (lambda (x y) nil) nil)";
    let terminal = s.cont_terminal();

    test_aux::<Coproc<Fr>>(
        s,
        expr,
        None,
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_eval_bad_form() {
    let s = &Store::<Fr>::default();
    let expr = "(* 5 (eval '(+ 1 a) '((0 . 3))))"; // two-arg eval, optional second arg is env.
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["8"], &None);
}

#[test]
fn test_eval_quote_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(
        s,
        "(1)",
        None,
        None,
        Some(error),
        None,
        &expect!["1"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        "(quote . 1)",
        None,
        None,
        Some(error),
        None,
        &expect!["1"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        "(quote 1 . 1)",
        None,
        None,
        Some(error),
        None,
        &expect!["1"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        "(quote 1 1)",
        None,
        None,
        Some(error),
        None,
        &expect!["1"],
        &None,
    );
}

#[test]
fn test_eval_dotted_syntax_error() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((a (lambda (x) (+ x 1)))) (a . 1))";
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, &expect!["3"], &None);
}

#[allow(dead_code)]
fn op_syntax_error<T: Op + Copy>() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    let test = |op: T| {
        let name = op.symbol_name();

        {
            let expr = format!("({name} . 1)");
            tracing::debug!("{}", &expr);
            test_aux::<Coproc<Fr>>(
                s,
                &expr,
                None,
                None,
                Some(error),
                None,
                &expect!["1"],
                &None,
            );
        }

        if !op.supports_arity(0) {
            let expr = format!("({name})");
            tracing::debug!("{}", &expr);
            test_aux::<Coproc<Fr>>(
                s,
                &expr,
                None,
                None,
                Some(error),
                None,
                &expect!["1"],
                &None,
            );
        }
        if !op.supports_arity(1) {
            let expr = format!("({name} 123)");
            tracing::debug!("{}", &expr);
            test_aux::<Coproc<Fr>>(
                s,
                &expr,
                None,
                None,
                Some(error),
                None,
                &expect!["1"],
                &None,
            );
        }
        if !op.supports_arity(2) {
            let expr = format!("({name} 123 456)");
            tracing::debug!("{}", &expr);
            test_aux::<Coproc<Fr>>(
                s,
                &expr,
                None,
                None,
                Some(error),
                None,
                &expect!["1"],
                &None,
            );
        }

        if !op.supports_arity(3) {
            let expr = format!("({name} 123 456 789)");
            tracing::debug!("{}", &expr);
            let iterations = if op.supports_arity(2) {
                &expect!["2"]
            } else {
                &expect!["1"]
            };
            test_aux::<Coproc<Fr>>(s, &expr, None, None, Some(error), None, iterations, &None);
        }
    };

    for op in T::all() {
        test(*op);
    }
}

#[test]
fn test_eval_unop_syntax_error() {
    op_syntax_error::<crate::tag::Op1>();
}

#[test]
fn test_eval_binop_syntax_error() {
    op_syntax_error::<crate::tag::Op2>();
}

#[test]
fn test_eval_lambda_body_syntax() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();

    test_aux::<Coproc<Fr>>(
        s,
        "((lambda ()))",
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        "((lambda () 1 2))",
        None,
        None,
        Some(error),
        None,
        &expect!["2"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        "((lambda (x)) 1)",
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        "((lambda (x) 1 2) 1)",
        None,
        None,
        Some(error),
        None,
        &expect!["3"],
        &None,
    );
}

#[test]
fn test_eval_non_symbol_binding_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();

    let test = |x| {
        let expr = format!("(let (({x} 123)) {x})");
        let expr2 = format!("(letrec (({x} 123)) {x})");
        let expr3 = format!("(lambda ({x}) {x})");

        test_aux::<Coproc<Fr>>(
            s,
            &expr,
            None,
            None,
            Some(error),
            None,
            &expect!["1"],
            &None,
        );
        test_aux::<Coproc<Fr>>(
            s,
            &expr2,
            None,
            None,
            Some(error),
            None,
            &expect!["1"],
            &None,
        );
        test_aux::<Coproc<Fr>>(
            s,
            &expr3,
            None,
            None,
            Some(error),
            None,
            &expect!["1"],
            &None,
        );
    };

    test(":a");
    test("1");
    test("\"string\"");
    test("1u64");
    test("#\\x");
}

#[test]
fn test_dumb_lang() {
    use crate::{coprocessor::test::DumbCoprocessor, state::user_sym};

    let mut lang = Lang::<Fr, DumbCoprocessor<Fr>>::new();
    let dumb = DumbCoprocessor::new();
    let name = user_sym("cproc-dumb");

    let s = &Store::default();
    lang.add_coprocessor(name, dumb);

    // 9^2 + 8 = 89
    let expr = "(cproc-dumb 9 8)";

    // coprocessors cannot be shadowed
    let expr2 = "(let ((cproc-dumb (lambda (a b) (* a b))))
                   (cproc-dumb 9 8))";

    // arguments for coprocessors are evaluated
    let expr3 = "(cproc-dumb (+ 1 8) (+ 1 7))";

    // wrong number of parameters
    let expr4 = "(cproc-dumb 9 8 123)";
    let expr5 = "(cproc-dumb 9)";

    // wrong parameter type
    let expr6 = "(cproc-dumb 'x' 0)";
    let expr6_ = "(cproc-dumb 'x' 'y')";
    let expr7 = "(cproc-dumb 0 'y')";

    let res = s.num_u64(89);
    let error4 = s.list(vec![s.num_u64(123), s.num_u64(8), s.num_u64(9)]);
    let error5 = s.list(vec![s.num_u64(9)]);
    let error6 = s.char('x');
    let error7 = s.char('y');

    let error = s.cont_error();
    let terminal = s.cont_terminal();

    test_aux(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        &Some(&lang),
    );
    test_aux(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["6"],
        &Some(&lang),
    );
    test_aux(
        s,
        expr3,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["9"],
        &Some(&lang),
    );
    test_aux(
        s,
        expr4,
        Some(error4),
        None,
        Some(error),
        None,
        &expect!["4"],
        &Some(&lang),
    );
    test_aux(
        s,
        expr5,
        Some(error5),
        None,
        Some(error),
        None,
        &expect!["2"],
        &Some(&lang),
    );
    test_aux(
        s,
        expr6,
        Some(error6),
        None,
        Some(error),
        None,
        &expect!["3"],
        &Some(&lang),
    );
    test_aux(
        s,
        expr6_,
        Some(error6),
        None,
        Some(error),
        None,
        &expect!["3"],
        &Some(&lang),
    );
    test_aux(
        s,
        expr7,
        Some(error7),
        None,
        Some(error),
        None,
        &expect!["3"],
        &Some(&lang),
    );
}

#[test]
fn test_trie_lang() {
    use crate::coprocessor::trie::{install, TrieCoproc};

    let s = &Store::<Fr>::default();
    let state = State::init_lurk_state().rccell();
    let mut lang = Lang::<Fr, TrieCoproc<Fr>>::new();

    install(&state, &mut lang);

    let expr = "(let ((trie (.lurk.trie.new)))
                      trie)";
    let res = s
        .read_with_default_state(
            "0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53",
        )
        .unwrap();

    test_aux_with_state(
        s,
        state.clone(),
        expr,
        Some(res),
        None,
        None,
        None,
        &expect!["4"],
        &Some(&lang),
    );

    let expr2 =
        "(.lurk.trie.lookup 0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53 123)";
    let res2 = s.comm(Fr::zero());

    test_aux_with_state(
        s,
        state.clone(),
        expr2,
        Some(res2),
        None,
        None,
        None,
        &expect!["3"],
        &Some(&lang),
    );

    let expr3 =
        "(.lurk.trie.insert 0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53 123 456)";
    let res3 = s
        .read_with_default_state(
            "0x1b22dc5a394231c34e4529af674dc56a736fbd07508acfd1d12c0e67c8b4de27",
        )
        .unwrap();

    test_aux_with_state(
        s,
        state.clone(),
        expr3,
        Some(res3),
        None,
        None,
        None,
        &expect!["4"],
        &Some(&lang),
    );

    let expr4 =
        "(.lurk.trie.lookup 0x1b22dc5a394231c34e4529af674dc56a736fbd07508acfd1d12c0e67c8b4de27 123)";
    let res4 = s.comm(Fr::from(456));

    test_aux_with_state(
        s,
        state.clone(),
        expr4,
        Some(res4),
        None,
        None,
        None,
        &expect!["3"],
        &Some(&lang),
    );

    let s = &Store::<Fr>::default();
    let expr5 = "(let ((trie (.lurk.trie.new))
                       (found (.lurk.trie.lookup trie 123)))
                      found)";
    let res5 = s.comm(Fr::zero());

    test_aux_with_state(
        s,
        state.clone(),
        expr5,
        Some(res5),
        None,
        None,
        None,
        &expect!["9"],
        &Some(&lang),
    );

    let expr6 = "(let ((trie (.lurk.trie.insert (.lurk.trie.new) 123 456))
                       (found (.lurk.trie.lookup trie 123)))
                      found)";
    let res6 = s.comm(Fr::from(456));

    test_aux_with_state(
        s,
        state.clone(),
        expr6,
        Some(res6),
        None,
        None,
        None,
        &expect!["13"],
        &Some(&lang),
    );
}

#[test]
fn test_terminator_lang() {
    use crate::{coprocessor::test::Terminator, state::user_sym};

    let mut lang = Lang::<Fr, Terminator<Fr>>::new();
    let dumb = Terminator::new();
    let name = user_sym("terminate");

    let s = &Store::default();
    lang.add_coprocessor(name, dumb);

    let expr = "(terminate)";

    let res = s.intern_nil();
    let terminal = s.cont_terminal();

    test_aux(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["1"],
        &Some(&lang),
    );
}
