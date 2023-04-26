use super::*;
use crate::coprocessor::Coprocessor;
use crate::eval::lang::Coproc;
use crate::eval::reduction::{extend, lookup, reduce};
use crate::num::Num;
use crate::tag::{ExprTag, Op, Op1, Op2};
use crate::writer::Write;

use lurk_macros::{let_store, lurk, Coproc};
use pasta_curves::pallas::Scalar as Fr;

fn test_aux<C: Coprocessor<Fr>>(
    s: &mut Store<Fr>,
    expr: &str,
    expected_result: Option<Ptr<Fr>>,
    expected_env: Option<Ptr<Fr>>,
    expected_cont: Option<ContPtr<Fr>>,
    expected_emitted: Option<Vec<Ptr<Fr>>>,
    expected_iterations: usize,
    lang: Option<&Lang<Fr, C>>,
) {
    let ptr = s.read(expr).unwrap();

    if let Some(lang) = lang {
        test_aux2(
            s,
            &ptr,
            expected_result,
            expected_env,
            expected_cont,
            expected_emitted,
            expected_iterations,
            lang,
        )
    } else {
        let lang = Lang::<Fr, Coproc<Fr>>::new();
        test_aux2(
            s,
            &ptr,
            expected_result,
            expected_env,
            expected_cont,
            expected_emitted,
            expected_iterations,
            &lang,
        )
    }
}

fn test_aux2<C: Coprocessor<Fr>>(
    s: &mut Store<Fr>,
    expr: &Ptr<Fr>,
    expected_result: Option<Ptr<Fr>>,
    expected_env: Option<Ptr<Fr>>,
    expected_cont: Option<ContPtr<Fr>>,
    expected_emitted: Option<Vec<Ptr<Fr>>>,
    expected_iterations: usize,
    lang: &Lang<Fr, C>,
) {
    let limit = 100000;
    let env = empty_sym_env(s);
    let (
        IO {
            expr: new_expr,
            env: new_env,
            cont: new_cont,
        },
        iterations,
        emitted,
    ) = Evaluator::new(*expr, env, s, limit, &lang).eval().unwrap();

    if let Some(expected_result) = expected_result {
        dbg!(expected_result.fmt_to_string(s), &new_expr.fmt_to_string(s));
        assert!(s.ptr_eq(&expected_result, &new_expr).unwrap());
    }
    if let Some(expected_env) = expected_env {
        assert!(s.ptr_eq(&expected_env, &new_env).unwrap());
    }
    if let Some(expected_cont) = expected_cont {
        assert_eq!(expected_cont, new_cont);
    } else {
        assert_eq!(s.intern_cont_terminal(), new_cont);
    }
    if let Some(expected_emitted) = expected_emitted {
        assert_eq!(expected_emitted.len(), emitted.len());

        assert!(expected_emitted
            .iter()
            .zip(emitted)
            .all(|(a, b)| s.ptr_eq(a, &b).unwrap()));
    }
    assert_eq!(expected_iterations, iterations);
}

#[test]
fn test_lookup() {
    let mut store = Store::<Fr>::default();
    let env = empty_sym_env(&store);
    let var = store.sym("variable");
    let val = store.num(123);

    assert!(lookup(&env, &var, &store).unwrap().is_nil());

    let new_env = extend(env, var, val, &mut store);
    assert_eq!(val, lookup(&new_env, &var, &store).unwrap());
}

#[test]
fn test_reduce_simple() {
    let mut store = Store::<Fr>::default();
    let lang = Lang::<Fr, Coproc<Fr>>::new();
    {
        let num = store.num(123);

        let (result, _new_env, _cont, _witness) = reduce(
            num,
            empty_sym_env(&store),
            store.intern_cont_outermost(),
            &mut store,
            &lang,
        )
        .unwrap();
        assert_eq!(num, result);
    }

    {
        let (result, _new_env, _cont, _witness) = reduce(
            store.nil(),
            empty_sym_env(&store),
            store.intern_cont_outermost(),
            &mut store,
            &lang,
        )
        .unwrap();
        assert!(result.is_nil());
    }
}

#[test]
fn evaluate_simple() {
    let s = &mut Store::<Fr>::default();

    let expr = "999";
    let expected = s.num(999);
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, None, None, 1, None);
}

#[test]
fn evaluate_lookup() {
    let mut store = Store::<Fr>::default();

    let limit = 20;
    let val = store.num(999);
    let var = store.sym("apple");
    let val2 = store.num(888);
    let var2 = store.sym("banana");
    let env = extend(empty_sym_env(&store), var, val, &mut store);
    let lang = Lang::<Fr, Coproc<Fr>>::new();

    {
        let (
            IO {
                expr: result_expr,
                env: _env,
                cont: _cont,
            },
            iterations,
            _emitted,
        ) = Evaluator::new(var, env, &mut store, limit, &lang)
            .eval()
            .unwrap();

        assert_eq!(1, iterations);
        assert_eq!(&result_expr, &val);
    }
    {
        let env2 = extend(env, var2, val2, &mut store);
        let (
            IO {
                expr: result_expr,
                env: _env,
                cont: _cont,
            },
            iterations,
            _emitted,
        ) = Evaluator::new(var, env2, &mut store, limit, &lang)
            .eval()
            .unwrap();

        assert_eq!(2, iterations);
        assert_eq!(&result_expr, &val);
    }
}

#[test]
fn print_expr() {
    let mut s = Store::<Fr>::default();
    let nil = s.nil();
    let x = s.sym("x");
    let lambda = s.lurk_sym("lambda");
    let val = s.num(123);
    let lambda_args = s.cons(x, nil);
    let body = s.cons(x, nil);
    let rest = s.cons(lambda_args, body);
    let whole_lambda = s.cons(lambda, rest);
    let lambda_arguments = s.cons(val, nil);
    let expr = s.cons(whole_lambda, lambda_arguments);
    let output = expr.fmt_to_string(&s);

    assert_eq!("((LAMBDA (X) X) 123)".to_string(), output);
}

#[test]
fn evaluate_cons() {
    let s = &mut Store::<Fr>::default();
    let expr = "(cons 1 2)";

    let car = s.num(1);
    let cdr = s.num(2);
    let expected = s.cons(car, cdr);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
}

#[test]
fn emit_output() {
    let s = &mut Store::<Fr>::default();
    let expr = "(emit 123)";
    let expected = s.num(123);
    let emitted = vec![expected];
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        Some(emitted),
        3,
        None,
    );
}

#[test]
fn evaluate_lambda() {
    let s = &mut Store::<Fr>::default();
    let expr = "((lambda(x) x) 123)";

    let expected = s.num(123);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 4, None);
}

#[test]
fn evaluate_lambda2() {
    let s = &mut Store::<Fr>::default();
    let expr = "((lambda (y) ((lambda (x) y) 321)) 123)";

    let expected = s.num(123);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 9, None);
}

#[test]
fn evaluate_lambda3() {
    let s = &mut Store::<Fr>::default();
    let expr = "((lambda (y) ((lambda (x) ((lambda (z) z) x)) y)) 123)";

    let expected = s.num(123);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        10,
        None,
    );
}

#[test]
fn evaluate_lambda4() {
    let s = &mut Store::<Fr>::default();
    let expr =
        // NOTE: We pass two different values. This tests which is returned.
            "((lambda (y) ((lambda (x) ((lambda (z) z) x)) 888)) 999)";

    let expected = s.num(888);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        10,
        None,
    );
}

#[test]
fn evaluate_lambda5() {
    let s = &mut Store::<Fr>::default();
    let expr =
        // Bind a function to the name FN, then call it.
            "(((lambda (fn) (lambda (x) (fn x))) (lambda (y) y)) 999)";

    let expected = s.num(999);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        13,
        None,
    );
}

#[test]
fn evaluate_sum() {
    let s = &mut Store::<Fr>::default();
    let expr = "(+ 2 (+ 3 4))";

    let expected = s.num(9);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 6, None);
}

#[test]
fn evaluate_diff() {
    let s = &mut Store::<Fr>::default();
    let expr = "(- 9 5)";

    let expected = s.num(4);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
}

#[test]
fn evaluate_product() {
    let s = &mut Store::<Fr>::default();
    let expr = "(* 9 5)";

    let expected = s.num(45);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
}

#[test]
fn evaluate_quotient() {
    let s = &mut Store::<Fr>::default();
    let expr = "(/ 21 7)";

    let expected = s.num(3);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
}

#[test]
fn evaluate_quotient_divide_by_zero() {
    let s = &mut Store::<Fr>::default();
    let expr = "(/ 21 0)";

    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 3, None);
}

#[test]
fn evaluate_num_equal() {
    let s = &mut Store::<Fr>::default();

    {
        let expr = "(= 5 5)";

        // TODO: Consider special-casing T, like NIL, and force it to the
        // immediate value 1 (with Symbol type-tag). That way boolean logic
        // will work out. It might be more consistent to have an explicit
        // boolean type (like Scheme), though. Otherwise we will have to
        // think about handling of symbol names (if made explicit), since
        // neither T/NIL as 1/0 will *not* be hashes of their symbol names.
        let expected = s.t();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
    {
        let expr = "(= 5 6)";

        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
}

#[test]
fn evaluate_adder1() {
    let s = &mut Store::<Fr>::default();
    let expr = "(((lambda (x) (lambda (y) (+ x y))) 2) 3)";

    let expected = s.num(5);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        13,
        None,
    );
}

// Enable this when we have LET.
#[test]
fn evaluate_adder2() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((make-adder (lambda (x) (lambda (y) (+ x y)))))
                   ((make-adder 2) 3))";

    let expected = s.num(5);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        15,
        None,
    );
}

#[test]
fn evaluate_let_simple() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((a 1)) a)";

    let expected = s.num(1);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
}

#[test]
fn evaluate_empty_let_bug() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let () (+ 1 2))";

    let expected = s.num(3);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 4, None);
}

#[test]
fn evaluate_let() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((a 1)
                        (b 2))
                   (+ a b))";

    let expected = s.num(3);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        10,
        None,
    );
}

#[test]
fn evaluate_let_empty_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let)";

    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn evaluate_let_empty_body_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((a 1)))";

    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn evaluate_letrec_empty_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(letrec)";

    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn evaluate_letrec_empty_body_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(letrec ((a 1)))";

    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn evaluate_letrec_body_nil() {
    let s = &mut Store::<Fr>::default();
    let expr = "(eq nil (let () nil))";

    let expected = s.t();
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 4, None);
}

#[test]
fn evaluate_let_parallel_binding() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((a 1) (b a)) b)";

    let expected = s.num(1);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 5, None);
}

#[test]
fn evaluate_arithmetic_let() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((a 5)
                        (b 1)
                        (c 2))
                   (/ (+ a b) c))";

    let expected = s.num(3);
    let new_env = s.nil();
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        Some(new_env),
        Some(terminal),
        None,
        18,
        None,
    );
}

#[test]
// Not because it's efficient, but to prove we can.
fn evaluate_fundamental_conditional() {
    {
        let s = &mut Store::<Fr>::default();
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

        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            35,
            None,
        );
    }
    {
        let s = &mut Store::<Fr>::default();
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

        let expected = s.num(6);
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            32,
            None,
        );
    }
}

#[test]
fn evaluate_if() {
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(if t 5 6)";

        let expected = s.num(5);
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(if nil 5 6)";

        let expected = s.num(6);
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
}

#[test]
fn evaluate_fully_evaluates() {
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(if t (+ 5 5) 6)";

        let expected = s.num(10);
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 5, None);
    }
}

#[test]
fn evaluate_recursion1() {
    let s = &mut Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base)
                                  (lambda (exponent)
                                    (if (= 0 exponent)
                                        1
                                        (* base ((exp base) (- exponent 1))))))))
                   ((exp 5) 3))";

    let expected = s.num(125);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        91,
        None,
    );
}

#[test]
fn evaluate_recursion2() {
    let s = &mut Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base)
                                  (lambda (exponent)
                                     (lambda (acc)
                                       (if (= 0 exponent)
                                          acc
                                          (((exp base) (- exponent 1)) (* acc base))))))))
                   (((exp 5) 5) 1))";

    let expected = s.num(3125);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        201,
        None,
    );
}

#[test]
fn evaluate_recursion_multiarg() {
    let s = &mut Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp base (- exponent 1)))))))
                          (exp 5 3))";

    let expected = s.num(125);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        95,
        None,
    );
}

#[test]
fn evaluate_recursion_optimized() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((exp (lambda (base)
                               (letrec ((base-inner
                                          (lambda (exponent)
                                            (if (= 0 exponent)
                                                1
                                                (* base (base-inner (- exponent 1)))))))
                                        base-inner))))
                    ((exp 5) 3))";

    let expected = s.num(125);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        75,
        None,
    );
}

#[test]
fn evaluate_tail_recursion() {
    let s = &mut Store::<Fr>::default();
    let expr = "(letrec ((exp (lambda (base)
                                  (lambda (exponent-remaining)
                                    (lambda (acc)
                                      (if (= 0 exponent-remaining)
                                          acc
                                          (((exp base) (- exponent-remaining 1)) (* acc base))))))))
                          (((exp 5) 3) 1))";

    let expected = s.num(125);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        129,
        None,
    );
}

#[test]
fn evaluate_tail_recursion_somewhat_optimized() {
    let s = &mut Store::<Fr>::default();
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

    let expected = s.num(125);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        110,
        None,
    );
}

#[test]
fn evaluate_multiple_letrec_bindings() {
    let s = &mut Store::<Fr>::default();
    let expr = "(letrec ((double (lambda (x) (* 2 x)))
                           (square (lambda (x) (* x x))))
                   (+ (square 3) (double 2)))";

    let expected = s.num(13);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        22,
        None,
    );
}

#[test]
fn evaluate_multiple_letrec_bindings_referencing() {
    let s = &mut Store::<Fr>::default();
    let expr = "(letrec ((double (lambda (x) (* 2 x)))
                           (double-inc (lambda (x) (+ 1 (double x)))))
                   (+ (double 3) (double-inc 2)))";

    let expected = s.num(11);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        31,
        None,
    );
}

#[test]
fn evaluate_multiple_letrec_bindings_recursive() {
    let s = &mut Store::<Fr>::default();
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

    let expected = s.num(33);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        242,
        None,
    );
}

#[test]
fn nested_let_closure_regression() {
    let s = &mut Store::<Fr>::default();
    let terminal = s.get_cont_terminal();
    let expected = s.num(6);

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
            13,
            None,
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
            14,
            None,
        );
    }
}

#[test]
fn evaluate_eq() {
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(eq 'a 'a)";

        let expected = s.t();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(eq 1 1)";

        let expected = s.t();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(eq 'a 1)";

        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }

    {
        let s = &mut Store::<Fr>::default();
        let expr = "(eq 1 'a)";

        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
}
#[test]
fn evaluate_zero_arg_lambda() {
    let s = &mut Store::<Fr>::default();
    let terminal = s.get_cont_terminal();
    {
        let expr = "((lambda () 123))";

        let expected = s.num(123);
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
    {
        let expected = {
            let arg = s.sym("x");
            let num = s.num(123);
            let body = s.list(&[num]);
            let env = s.nil();
            s.intern_fun(arg, body, env)
        };

        // One arg expected but zero supplied.
        let expr = "((lambda (x) 123))";
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
    }
    {
        let expr = "(letrec ((x 9) (f (lambda () (+ x 1)))) (f))";

        let expected = s.num(10);
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            12,
            None,
        );
    }
}

#[test]
fn evaluate_zero_arg_lambda_variants() {
    {
        let_store!();

        let limit = 20;
        let expr = lurk!(((lambda (x) 123))).unwrap();
        let lang = Lang::<Fr, Coproc<Fr>>::new();

        let (
            IO {
                expr: result_expr,
                env: _new_env,
                cont: _continuation,
            },
            iterations,
            _emitted,
        ) = Evaluator::new(expr, empty_sym_env(s_), s_, limit, &lang)
            .eval()
            .unwrap();

        assert_eq!(crate::tag::ExprTag::Fun, result_expr.tag);
        assert_eq!(3, iterations);
    }
    {
        let s = &mut Store::<Fr>::default();
        let expr = "((lambda () 123) 1)";

        let error = s.get_cont_error();
        test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 3, None);
    }
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(123)";

        let error = s.get_cont_error();
        test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
    }
}

#[test]
fn evaluate_make_tree() {
    {
        let s = &mut Store::<Fr>::default();
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
            .read("(((h . g) . (f . e)) . ((d . c) . (b . a)))")
            .unwrap();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            493,
            None,
        );
    }
}

#[test]
fn evaluate_make_tree_minimal_regression() {
    {
        let mut s = Store::<Fr>::default();
        let limit = 100;
        let expr = s
            .read(
                "(letrec ((fn-1 (lambda (x)
                                    (let ((y x))
                                       y)))
                               (fn-2 (lambda (list)
                                       (let ((z (fn-1 list)))
                                         (fn-2 z)))))
                                 (fn-2 '(a b c d e f g h)))",
            )
            .unwrap();

        let lang = Lang::<Fr, Coproc<Fr>>::new();
        let (
            IO {
                expr: _result_expr,
                env: _new_env,
                cont: _continuation,
            },
            iterations,
            _emitted,
        ) = Evaluator::new(expr, empty_sym_env(&s), &mut s, limit, &lang)
            .eval()
            .unwrap();

        assert_eq!(100, iterations);
    }
}
#[test]
fn evaluate_map_tree_bug() {
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(letrec ((map-tree (lambda (f tree)
                      (if (atom tree)
                          (f tree)
                          (cons (map-tree f (car tree))
                                (map-tree f (cdr tree)))))))
         (map-tree (lambda (x) (+ 1 x)) '((1 . 2) . (3 . 4))))";

        let expected = s.read("((2 . 3) . (4 . 5))").unwrap();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            170,
            None,
        );
    }
}

#[test]
fn evaluate_map_tree_numequal_bug() {
    {
        // Reuse map-tree failure case to test Relop behavior.
        // This failed initially and tests regression.
        let s = &mut Store::<Fr>::default();
        let expr = "(letrec ((map-tree (lambda (f tree)
                                           (if (atom tree)
                                             (f tree)
                                               (= (map-tree f (car tree))
                                                  (map-tree f (cdr tree)))))))
                       (map-tree (lambda (x) (+ 1 x)) '((1 . 2) . (3 . 4))))";
        let expected = s.nil();
        let error = s.get_cont_error();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(error), None, 169, None);
    }
}

#[test]
fn env_lost_bug() {
    {
        // previously, an unbound variable `u` error
        let s = &mut Store::<Fr>::default();
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
        let expected = s.nil();
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            25,
            None,
        );
    }
}

#[test]
fn dont_discard_rest_env() {
    {
        // previously: Unbound variable: Sym("Z")
        let s = &mut Store::<Fr>::default();
        let expr = "(let ((z 9))
                       (letrec ((a 1)
                                 (b 2)
                                 (l (lambda (x) (+ z x))))
                         (l 9)))";
        let expected = s.num(18);
        let terminal = s.get_cont_terminal();
        test_aux::<Coproc<Fr>>(
            s,
            expr,
            Some(expected),
            None,
            Some(terminal),
            None,
            22,
            None,
        );
    }
}

#[test]
fn test_str_car_cdr_cons() {
    let s = &mut Store::<Fr>::default();
    let a = s.read(r#"#\a"#).unwrap();
    let apple = s.read(r#" "apple" "#).unwrap();
    let a_pple = s.read(r#" (#\a . "pple") "#).unwrap();
    let pple = s.read(r#" "pple" "#).unwrap();
    let empty = s.intern_str("");
    let nil = s.nil();
    let terminal = s.get_cont_terminal();
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(
        s,
        r#"(car "apple")"#,
        Some(a),
        None,
        Some(terminal),
        None,
        2,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr "apple")"#,
        Some(pple),
        None,
        Some(terminal),
        None,
        2,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(car "")"#,
        Some(nil),
        None,
        Some(terminal),
        None,
        2,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr "")"#,
        Some(empty),
        None,
        Some(terminal),
        None,
        2,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cons #\a "pple")"#,
        Some(a_pple),
        None,
        Some(terminal),
        None,
        3,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(strcons #\a "pple")"#,
        Some(apple),
        None,
        Some(terminal),
        None,
        3,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(strcons #\a #\b)"#,
        None,
        None,
        Some(error),
        None,
        3,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(strcons "a" "b")"#,
        None,
        None,
        Some(error),
        None,
        3,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(strcons 1 2)"#,
        None,
        None,
        Some(error),
        None,
        3,
        None,
    );
    test_aux::<Coproc<Fr>>(s, r#"(strcons)"#, None, None, Some(error), None, 1, None);
}

#[test]
fn test_one_arg_cons_error() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, r#"(cons "")"#, None, None, Some(error), None, 1, None);
}

#[test]
fn test_car_nil() {
    let s = &mut Store::<Fr>::default();
    let expected = s.nil();
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(car NIL)"#,
        Some(expected),
        None,
        Some(terminal),
        None,
        2,
        None,
    );
}

#[test]
fn test_cdr_nil() {
    let s = &mut Store::<Fr>::default();
    let expected = s.nil();
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr NIL)"#,
        Some(expected),
        None,
        Some(terminal),
        None,
        2,
        None,
    );
}

#[test]
fn test_car_cdr_invalid_tag_error_sym() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, r#"(car 'car)"#, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, r#"(cdr 'car)"#, None, None, Some(error), None, 2, None);
}

#[test]
fn test_car_cdr_invalid_tag_error_char() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, r#"(car #\a)"#, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, r#"(cdr #\a)"#, None, None, Some(error), None, 2, None);
}

#[test]
fn test_car_cdr_invalid_tag_error_num() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, r#"(car 42)"#, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, r#"(cdr 42)"#, None, None, Some(error), None, 2, None);
}

#[test]
fn test_car_cdr_invalid_tag_error_lambda() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(
        s,
        r#"(car (lambda (x) x))"#,
        None,
        None,
        Some(error),
        None,
        2,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        r#"(cdr (lambda (x) x))"#,
        None,
        None,
        Some(error),
        None,
        2,
        None,
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

    let s = &mut Store::<Fr>::default();
    let n = s.num(0x1044);
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
        1114,
        None,
    );
}

#[test]
fn begin_current_env() {
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(begin (current-env))";
        let expected = s.nil();
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, None, None, 2, None);
    }
}

#[test]
fn begin() {
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(car (begin 1 2 '(3 . 4)))";
        let expected = s.num(3);
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, None, None, 6, None);
    }
}

#[test]
fn begin_current_env1() {
    {
        let s = &mut Store::<Fr>::default();
        let expr = "(let ((a 1))
                       (begin 123 (current-env)))";
        let a = s.sym("a");
        let one = s.num(1);
        let binding = s.cons(a, one);
        let expected = s.list(&[binding]);
        test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, None, None, 5, None);
    }
}

#[test]
fn hide_open() {
    let s = &mut Store::<Fr>::default();
    let expr = "(open (hide 123 'x))";
    let x = s.sym("x");
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, None, None, 5, None);
}

#[test]
fn hide_opaque_open_available() {
    use crate::Num;

    let s = &mut Store::<Fr>::default();
    let commitment = eval_to_ptr::<Fr, Coproc<Fr>>(s, "(hide 123 'x)").unwrap();

    let c_scalar = s.hash_expr(&commitment).unwrap();
    let c = c_scalar.value();
    let comm = s.intern_maybe_opaque_comm(*c);

    assert!(!comm.is_opaque());

    let open = s.sym("open");
    let x = s.sym("x");
    let lang = Lang::new();

    {
        let expr = s.list(&[open, comm]);
        test_aux2::<Coproc<Fr>>(s, &expr, Some(x), None, None, None, 2, &lang);
    }

    {
        let secret = s.sym("secret");
        let expr = s.list(&[secret, comm]);
        let sec = s.num(123);
        test_aux2::<Coproc<Fr>>(s, &expr, Some(sec), None, None, None, 2, &lang);
    }

    {
        // We can open a commitment identified by its corresponding `Num`.
        let comm_num = s.num(Num::from_scalar(*c));
        let expr2 = s.list(&[open, comm_num]);
        test_aux2::<Coproc<Fr>>(s, &expr2, Some(x), None, None, None, 2, &lang);
    }
}

#[test]
#[should_panic]
fn hide_opaque_open_unavailable() {
    let s = &mut Store::<Fr>::default();
    let commitment = eval_to_ptr::<Fr, Coproc<Fr>>(s, "(hide 123 'x)").unwrap();

    let c_scalar = s.hash_expr(&commitment).unwrap();
    let c = c_scalar.value();

    let s2 = &mut Store::<Fr>::default();
    let comm = s2.intern_maybe_opaque_comm(*c);
    let open = s2.lurk_sym("open");
    let x = s2.sym("x");

    let expr = s2.list(&[open, comm]);
    let lang = Lang::new();

    test_aux2::<Coproc<Fr>>(s2, &expr, Some(x), None, None, None, 2, &lang);
}

#[test]
fn commit_open_sym() {
    let s = &mut Store::<Fr>::default();
    let expr = "(open (commit 'x))";
    let x = s.sym("x");
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, None, None, 4, None);
}

#[test]
fn commitment_value() {
    let s = &mut Store::<Fr>::default();
    let expr = "(num (commit 123))";
    let x = s
        .read("0x2937881eff06c2bcc2c8c1fa0818ae3733c759376f76fc10b7439269e9aaa9bc")
        .unwrap();
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, None, None, 4, None);
}

#[test]
fn commit_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(commit 123 456)";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn open_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(open 123 456)";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn secret_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(secret 123 456)";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn num_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(num 123 456)";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn comm_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(comm 123 456)";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn char_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(char 123 456)";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 1, None);
}

#[test]
fn prove_commit_secret() {
    let s = &mut Store::<Fr>::default();
    let expr = "(secret (commit 123))";
    let expected = s.num(0);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 4, None);
}

#[test]
fn num() {
    let s = &mut Store::<Fr>::default();
    let expr = "(num 123)";
    let expected = s.num(123);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 2, None);
}

#[test]
fn num_char() {
    let s = &mut Store::<Fr>::default();
    let expr = r#"(num #\a)"#;
    let expected = s.num(97);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 2, None);
}

#[test]
fn char_num() {
    let s = &mut Store::<Fr>::default();
    let expr = r#"(char 97)"#;
    let expected_a = s.read(r#"#\a"#).unwrap();
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected_a),
        None,
        Some(terminal),
        None,
        2,
        None,
    );
}

#[test]
fn char_coercion() {
    let s = &mut Store::<Fr>::default();
    let expr = r#"(char (- 0 4294967200))"#;
    let expected_a = s.read(r#"#\a"#).unwrap();
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(
        s,
        expr,
        Some(expected_a),
        None,
        Some(terminal),
        None,
        5,
        None,
    );
}

#[test]
fn commit_num() {
    let s = &mut Store::<Fr>::default();
    let expr = "(num (commit 123))";
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(terminal), None, 4, None);
}

#[test]
fn hide_open_comm_num() {
    let s = &mut Store::<Fr>::default();
    let expr = "(open (comm (num (hide 123 456))))";
    let expected = s.num(456);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 9, None);
}

#[test]
fn hide_secret_comm_num() {
    let s = &mut Store::<Fr>::default();
    let expr = "(secret (comm (num (hide 123 456))))";
    let expected = s.num(123);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 9, None);
}

#[test]
fn commit_open_comm_num() {
    let s = &mut Store::<Fr>::default();
    let expr = "(open (comm (num (commit 123))))";
    let expected = s.num(123);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 8, None);
}

#[test]
fn commit_secret_comm_num() {
    let s = &mut Store::<Fr>::default();
    let expr = "(secret (comm (num (commit 123))))";
    let expected = s.num(0);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 8, None);
}

#[test]
fn commit_num_open() {
    let s = &mut Store::<Fr>::default();
    let expr = "(open (num (commit 123)))";
    let expected = s.num(123);
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 6, None);
}

#[test]
fn num_invalid_tag() {
    let s = &mut Store::<Fr>::default();
    let expr = "(num (quote x))";
    let expr1 = "(num \"asdf\")";
    let expr2 = "(num '(1))";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, expr1, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, expr2, None, None, Some(error), None, 2, None);
}

#[test]
fn comm_invalid_tag() {
    let s = &mut Store::<Fr>::default();
    let expr = "(comm (quote x))";
    let expr1 = "(comm \"asdf\")";
    let expr2 = "(comm '(1))";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, expr1, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, expr2, None, None, Some(error), None, 2, None);
}

#[test]
fn char_invalid_tag() {
    let s = &mut Store::<Fr>::default();
    let expr = "(char (quote x))";
    let expr1 = "(char \"asdf\")";
    let expr2 = "(char '(1))";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, expr1, None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(s, expr2, None, None, Some(error), None, 2, None);
}

#[test]
fn terminal_sym() {
    let s = &mut Store::<Fr>::default();
    let expr = "(quote x)";
    let x = s.sym("x");
    let terminal = s.get_cont_terminal();
    test_aux::<Coproc<Fr>>(s, expr, Some(x), None, Some(terminal), None, 1, None);
}

#[test]
#[should_panic = "hidden value could not be opened"]
fn open_opaque_commit() {
    let s = &mut Store::<Fr>::default();
    let expr = "(open 123)";
    test_aux::<Coproc<Fr>>(s, expr, None, None, None, None, 2, None);
}

#[test]
fn open_wrong_type() {
    let s = &mut Store::<Fr>::default();
    let expr = "(open 'asdf)";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 2, None);
}

#[test]
fn secret_wrong_type() {
    let s = &mut Store::<Fr>::default();
    let expr = "(secret 'asdf)";
    let error = s.get_cont_error();
    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 2, None);
}

#[test]
#[should_panic]
fn secret_invalid_tag() {
    let s = &mut Store::<Fr>::default();
    let expr = "(secret 123)";
    test_aux::<Coproc<Fr>>(s, expr, None, None, None, None, 2, None);
}

#[test]
#[should_panic = "secret could not be extracted"]
fn secret_opaque_commit() {
    let s = &mut Store::<Fr>::default();
    let expr = "(secret (comm 123))";
    test_aux::<Coproc<Fr>>(s, expr, None, None, None, None, 2, None);
}

fn relational_aux(s: &mut Store<Fr>, op: &str, a: &str, b: &str, res: bool) {
    let expr = &format!("({op} {a} {b})");
    let expected = if res { s.t() } else { s.nil() };
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(expected), None, Some(terminal), None, 3, None);
}

#[test]
fn test_relational() {
    let s = &mut Store::<Fr>::default();
    let lt = "<";
    let gt = ">";
    let lte = "<=";
    let gte = ">=";
    let zero = "0";
    let one = "1";
    let two = "2";

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
    let s = &mut Store::<Fr>::default();
    let t = s.t();
    let terminal = s.get_cont_terminal();

    // Normally, a value cannot be less than the result of incrementing it.
    // However, the most positive field element (when viewed as signed)
    // is the exception. Incrementing it yields the most negative element,
    // which is less than the most positive.
    {
        let expr = "(let ((most-positive (/ (- 0 1) 2))
                          (most-negative (+ 1 most-positive)))
                      (< most-negative most-positive))";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 19, None);
    }

    // Regression: comparisons with negative numbers should *not* be exceptions.
    {
        let expr = "(let ((most-positive (/ (- 0 1) 2))
                              (most-negative (+ 1 most-positive))
                              (less-negative (+ 1 most-negative)))
                      (< most-negative  less-negative)) ";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 24, None);
    }
}

#[test]
fn test_num_syntax_implications() {
    let s = &mut Store::<Fr>::default();
    let t = s.t();
    let terminal = s.get_cont_terminal();

    {
        let expr = "(let ((most-positive -1/2)
                              (most-negative 1/2))
                          (< most-negative most-positive))";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 10, None);
    }

    {
        let expr = "(= (* 6 3/2) 9)";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 6, None);
    }

    {
        let expr = "(= (* 2/3 3/2) 1)";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 6, None);
    }

    {
        let expr = "(= (* -2/3 3/2) -1)";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 6, None);
    }

    {
        let expr = "(= (+ 1/3 1/2) 5/6)";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 6, None);
    }

    // Comparisons of field elements produced by fractional notation don't yield the results
    // their rational equivalents would.
    {
        // This obviously must be true, since 1/2 is the most negative Num,
        // but this violates expectations if you consider 1/2 to behave like a rational.
        let expr = "(< 1/2 1/3)";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 3, None);
    }

    {
        // This isn't a weird edge case like the above, but it's also not the behavior
        // expected if fractional notation yielded true rational numbers.
        let expr = "(< 3/4 5/8)";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 3, None);
    }
    {
        // It's not that they *can't* compare in the naively expected way, though.
        let expr = "(< 3/5 3/4)";

        test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 3, None);
    }
}

#[test]
fn test_quoted_symbols() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((|foo bar| 9)
                          (|Foo \\| Bar| (lambda (|X|) (* x x))))
                      (|Foo \\| Bar| |foo bar|))";
    let res = s.num(81);
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 13, None);
}

#[test]
fn test_eval() {
    let s = &mut Store::<Fr>::default();
    let expr = "(* 3 (eval (cons '+ (cons 1 (cons 2 nil)))))";
    let expr2 = "(* 5 (eval '(+ 1 a) '((a . 3))))"; // two-arg eval, optional second arg is env.
    let res = s.num(9);
    let res2 = s.num(20);
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 17, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res2), None, Some(terminal), None, 9, None);
}

#[test]
fn test_eval_env_regression() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((a 1)) (eval 'a))";
    let expr2 = "(let ((a 1)) (eval 'a (current-env)))";
    let res = s.num(1);
    let error = s.get_cont_error();
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 5, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res), None, Some(terminal), None, 6, None);
}

#[test]
fn test_u64_self_evaluating() {
    let s = &mut Store::<Fr>::default();

    let expr = "123u64";
    let res = s.uint64(123);
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 1, None);
}

#[test]
fn test_u64_mul() {
    let s = &mut Store::<Fr>::default();

    let expr = "(* (u64 18446744073709551615) (u64 2))";
    let expr2 = "(* 18446744073709551615u64 2u64)";
    let expr3 = "(* (- 0u64 1u64) 2u64)";
    let res = s.uint64(18446744073709551614);
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 7, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr3, Some(res), None, Some(terminal), None, 6, None);
}

#[test]
fn test_u64_add() {
    let s = &mut Store::<Fr>::default();

    let expr = "(+ 18446744073709551615u64 2u64)";
    let expr2 = "(+ (- 0u64 1u64) 2u64)";
    let res = s.uint64(1);
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res), None, Some(terminal), None, 6, None);
}

#[test]
fn test_u64_sub() {
    let s = &mut Store::<Fr>::default();

    let expr = "(- 2u64 1u64)";
    let expr2 = "(- 0u64 1u64)";
    let expr3 = "(+ 1u64 (- 0u64 1u64))";
    let res = s.uint64(1);
    let res2 = s.uint64(18446744073709551615);
    let res3 = s.uint64(0);
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr3, Some(res3), None, Some(terminal), None, 6, None);
}

#[test]
fn test_u64_div() {
    let s = &mut Store::<Fr>::default();

    let expr = "(/ 100u64 2u64)";
    let res = s.uint64(50);

    let expr2 = "(/ 100u64 3u64)";
    let res2 = s.uint64(33);

    let expr3 = "(/ 100u64 0u64)";

    let terminal = s.get_cont_terminal();
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr3, None, None, Some(error), None, 3, None);
}

#[test]
fn test_u64_mod() {
    let s = &mut Store::<Fr>::default();

    let expr = "(% 100u64 2u64)";
    let res = s.uint64(0);

    let expr2 = "(% 100u64 3u64)";
    let res2 = s.uint64(1);

    let expr3 = "(% 100u64 0u64)";

    let terminal = s.get_cont_terminal();
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr3, None, None, Some(error), None, 3, None);
}

#[test]
fn test_num_mod() {
    let s = &mut Store::<Fr>::default();

    let expr = "(% 100 3)";
    let expr2 = "(% 100 3u64)";
    let expr3 = "(% 100u64 3)";

    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, None, None, Some(error), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr3, None, None, Some(error), None, 3, None);
}

#[test]
fn test_u64_comp() {
    let s = &mut Store::<Fr>::default();

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

    let t = s.t();
    let nil = s.nil();
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(nil), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr3, Some(t), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr4, Some(nil), None, Some(terminal), None, 3, None);

    test_aux::<Coproc<Fr>>(s, expr5, Some(nil), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr6, Some(t), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr7, Some(nil), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr8, Some(t), None, Some(terminal), None, 3, None);

    test_aux::<Coproc<Fr>>(s, expr9, Some(t), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr10, Some(t), None, Some(terminal), None, 3, None);

    test_aux::<Coproc<Fr>>(s, expr11, Some(t), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr12, Some(nil), None, Some(terminal), None, 3, None);
}

#[test]
fn test_u64_conversion() {
    let s = &mut Store::<Fr>::default();

    let expr = "(+ 0 1u64)";
    let expr2 = "(num 1u64)";
    let expr3 = "(+ 1 1u64)";
    let expr4 = "(u64 (+ 1 1))";
    let expr5 = "(u64 123u64)";
    let expr6 = "(u64)";
    let expr7 = "(u64 1 1)";

    let res = s.intern_num(1);
    let res2 = s.intern_num(2);
    let res3 = s.get_u64(2);
    let res5 = s.get_u64(123);
    let terminal = s.get_cont_terminal();
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res), None, Some(terminal), None, 2, None);
    test_aux::<Coproc<Fr>>(s, expr3, Some(res2), None, Some(terminal), None, 3, None);

    test_aux::<Coproc<Fr>>(s, expr4, Some(res3), None, Some(terminal), None, 5, None);
    test_aux::<Coproc<Fr>>(s, expr5, Some(res5), None, Some(terminal), None, 2, None);
    test_aux::<Coproc<Fr>>(s, expr6, None, None, Some(error), None, 1, None);
    test_aux::<Coproc<Fr>>(s, expr7, None, None, Some(error), None, 1, None);
}

#[test]
fn test_numeric_type_error() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();

    let mut test = |op| {
        let expr = &format!("({op} 0 'a)");
        let expr2 = &format!("({op} 0u64 'a)");

        test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 3, None);
        test_aux::<Coproc<Fr>>(s, expr2, None, None, Some(error), None, 3, None);
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
    let s = &mut Store::<Fr>::default();

    let expr = "(= 1 1u64)";
    let expr2 = "(= 1 2u64)";
    let t = s.t();
    let nil = s.nil();
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(t), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(nil), None, Some(terminal), None, 3, None);
}

#[test]
fn test_u64_num_cons() {
    let s = &mut Store::<Fr>::default();

    let expr = "(cons 1 1u64)";
    let expr2 = "(cons 1u64 1)";
    let res = s.read("(1 . 1u64)").unwrap();
    let res2 = s.read("(1u64 . 1)").unwrap();
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
}

#[test]
fn test_hide_u64_secret() {
    let s = &mut Store::<Fr>::default();

    let expr = "(hide 0u64 123)";
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 3, None);
}

#[test]
fn test_keyword() {
    let s = &mut Store::<Fr>::default();

    let expr = ":asdf";
    let expr2 = "(eq :asdf :asdf)";
    let expr3 = "(eq :asdf 'asdf)";
    let res = s.key("ASDF");
    let res2 = s.get_t();
    let res3 = s.get_nil();

    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 1, None);
    test_aux::<Coproc<Fr>>(s, expr2, Some(res2), None, Some(terminal), None, 3, None);
    test_aux::<Coproc<Fr>>(s, expr3, Some(res3), None, Some(terminal), None, 3, None);
}

#[test]
fn test_root_sym() {
    use crate::sym::Sym;

    let s = &mut Store::<Fr>::default();

    let sym = Sym::root();
    let x = s.intern_sym(&sym);

    let scalar_ptr = &s.get_expr_hash(&x).unwrap();

    assert_eq!(&Fr::zero(), scalar_ptr.value());
    assert_eq!(ExprTag::Sym, scalar_ptr.tag());
}

#[test]
fn test_sym_hash_values() {
    use crate::sym::Sym;

    let s = &mut Store::<Fr>::default();

    let sym = s.sym(".ASDF.FDSA");
    let key = s.sym(":ASDF.FDSA");
    let expr = s.read("(cons \"FDSA\" '.ASDF)").unwrap();

    let limit = 10;
    let env = empty_sym_env(s);
    let lang = Lang::<Fr, Coproc<Fr>>::new();
    let (
        IO {
            expr: new_expr,
            env: _,
            cont: _,
        },
        _iterations,
        _emitted,
    ) = Evaluator::new(expr, env, s, limit, &lang).eval().unwrap();

    let toplevel_sym = s.sym(".ASDF");

    let root = Sym::root();
    let root_sym = s.intern_sym(&root);

    let asdf = s.str("ASDF");
    let consed_with_root = s.cons(asdf, root_sym);

    let cons_scalar_ptr = &s.get_expr_hash(&new_expr).unwrap();
    let sym_scalar_ptr = &s.get_expr_hash(&sym).unwrap();
    let key_scalar_ptr = &s.get_expr_hash(&key).unwrap();

    let consed_with_root_scalar_ptr = &s.get_expr_hash(&consed_with_root).unwrap();
    let toplevel_scalar_ptr = &s.get_expr_hash(&toplevel_sym).unwrap();

    // Symbol and keyword scalar hash values are the same as
    // those of the name string consed onto the parent symbol.
    assert_eq!(cons_scalar_ptr.value(), sym_scalar_ptr.value());
    assert_eq!(cons_scalar_ptr.value(), key_scalar_ptr.value());

    // Toplevel symbols also have this property, and their parent symbol is the root symbol.
    assert_eq!(
        consed_with_root_scalar_ptr.value(),
        toplevel_scalar_ptr.value()
    );

    // The tags differ though.
    assert_eq!(ExprTag::Sym, sym_scalar_ptr.tag());
    assert_eq!(ExprTag::Key, key_scalar_ptr.tag());
}

#[test]
fn test_fold_cons_regression() {
    let s = &mut Store::<Fr>::default();

    let expr = "(letrec ((fold (lambda (op acc l)
                                     (if l
                                         (fold op (op acc (car l)) (cdr l))
                                         acc))))
                      (fold (lambda (x y) (+ x y)) 0 '(1 2 3)))";
    let res = s.num(6);
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, Some(res), None, Some(terminal), None, 152, None);
}

#[test]
fn test_lambda_args_regression() {
    let s = &mut Store::<Fr>::default();

    let expr = "(cons (lambda (x y) nil) nil)";
    let terminal = s.get_cont_terminal();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(terminal), None, 3, None);
}

#[test]
fn test_eval_bad_form() {
    let s = &mut Store::<Fr>::default();
    let expr = "(* 5 (eval '(+ 1 a) '((0 . 3))))"; // two-arg eval, optional second arg is env.
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 8, None);
}

#[test]
fn test_eval_quote_error() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, "(1)", None, None, Some(error), None, 1, None);
    test_aux::<Coproc<Fr>>(s, "(quote . 1)", None, None, Some(error), None, 1, None);
    test_aux::<Coproc<Fr>>(s, "(quote 1 . 1)", None, None, Some(error), None, 1, None);
    test_aux::<Coproc<Fr>>(s, "(quote 1 1)", None, None, Some(error), None, 1, None);
}

#[test]
fn test_eval_dotted_syntax_error() {
    let s = &mut Store::<Fr>::default();
    let expr = "(let ((a (lambda (x) (+ x 1)))) (a . 1))";
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, expr, None, None, Some(error), None, 3, None);
}

fn op_syntax_error<T: Op + Copy>() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();
    let mut test = |op: T| {
        let name = op.symbol_name();

        {
            let expr = format!("({name} . 1)");
            dbg!(&expr);
            test_aux::<Coproc<Fr>>(s, &expr, None, None, Some(error), None, 1, None);
        }

        if !op.supports_arity(0) {
            let expr = format!("({name})");
            dbg!(&expr);
            test_aux::<Coproc<Fr>>(s, &expr, None, None, Some(error), None, 1, None);
        }
        if !op.supports_arity(1) {
            let expr = format!("({name} 123)");
            dbg!(&expr);
            test_aux::<Coproc<Fr>>(s, &expr, None, None, Some(error), None, 1, None);
        }
        if !op.supports_arity(2) {
            let expr = format!("({name} 123 456)");
            dbg!(&expr);
            test_aux::<Coproc<Fr>>(s, &expr, None, None, Some(error), None, 1, None);
        }

        if !op.supports_arity(3) {
            let expr = format!("({name} 123 456 789)");
            dbg!(&expr);
            let iterations = if op.supports_arity(2) { 2 } else { 1 };
            test_aux::<Coproc<Fr>>(s, &expr, None, None, Some(error), None, iterations, None);
        }
    };

    for op in T::all() {
        test(*op);
    }
}

#[test]
fn test_eval_unop_syntax_error() {
    op_syntax_error::<Op1>();
}

#[test]
fn test_eval_binop_syntax_error() {
    op_syntax_error::<Op2>();
}

#[test]
fn test_eval_lambda_body_syntax() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();

    test_aux::<Coproc<Fr>>(s, "((lambda ()))", None, None, Some(error), None, 2, None);
    test_aux::<Coproc<Fr>>(
        s,
        "((lambda () 1 2))",
        None,
        None,
        Some(error),
        None,
        2,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        "((lambda (x)) 1)",
        None,
        None,
        Some(error),
        None,
        3,
        None,
    );
    test_aux::<Coproc<Fr>>(
        s,
        "((lambda (x) 1 2) 1)",
        None,
        None,
        Some(error),
        None,
        3,
        None,
    );
}

#[test]
fn test_eval_non_symbol_binding_error() {
    let s = &mut Store::<Fr>::default();
    let error = s.get_cont_error();

    let mut test = |x| {
        let expr = format!("(let (({x} 123)) {x})");
        let expr2 = format!("(letrec (({x} 123)) {x})");
        let expr3 = format!("(lambda ({x}) {x})");

        test_aux::<Coproc<Fr>>(s, &expr, None, None, Some(error), None, 1, None);
        test_aux::<Coproc<Fr>>(s, &expr2, None, None, Some(error), None, 1, None);
        test_aux::<Coproc<Fr>>(s, &expr3, None, None, Some(error), None, 1, None);
    };

    test(":a");
    test("1");
    test("\"string\"");
    test("1u64");
    test("#\\x");
}

#[cfg(test)]
pub(crate) mod coproc {
    use super::super::lang::Lang;
    use super::super::*;
    use super::*;
    use crate::circuit::gadgets::constraints::{add, mul};
    use crate::circuit::gadgets::data::GlobalAllocations;
    use crate::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
    use crate::coprocessor::{test::DumbCoprocessor, CoCircuit};
    use crate::store::Store;
    use crate::sym::Sym;

    #[derive(Clone, Debug, Coproc)]
    pub(crate) enum DumbCoproc<F: LurkField> {
        DC(DumbCoprocessor<F>),
    }

    use bellperson::SynthesisError;

    impl<F: LurkField> Coprocessor<F> for DumbCoproc<F> {
        fn eval_arity(&self) -> usize {
            match self {
                Self::DC(c) => c.eval_arity(),
            }
        }

        fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
            match self {
                Self::DC(c) => c.simple_evaluate(s, args),
            }
        }
    }
        
    impl<F: LurkField> CoCircuit<F> for DumbCoproc<F> {
        fn arity(&self) -> usize {
            2
        }

        fn synthesize<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocations<F>,
            _store: &Store<F>,
            input_exprs: &[AllocatedPtr<F>],
            input_env: &AllocatedPtr<F>,
            input_cont: &AllocatedContPtr<F>,
        ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError>
        {
            let a = input_exprs[0].clone();
            let b = &input_exprs[1];

            // FIXME: Check tags.

            // a^2 + b = c
            let a2 = mul(&mut cs.namespace(|| "square"), a.hash(), a.hash())?;
            let c = add(&mut cs.namespace(|| "add"), &a2, b.hash())?;
            let c_ptr = AllocatedPtr::alloc_tag(cs, ExprTag::Num.to_field(), c)?;

            Ok((c_ptr, input_env.clone(), input_cont.clone()))
        }
    }

    #[test]
    fn test_dumb_lang() {
        let s = &mut Store::<Fr>::new();

        let mut lang = Lang::<Fr, DumbCoproc<Fr>>::new();
        let name = Sym::new(".cproc.dumb".to_string());
        let dumb = DumbCoprocessor::new();
        let coproc = DumbCoproc::DC(dumb);

        lang.add_coprocessor(name, coproc, s);

        // 9^2 + 8 = 89
        let expr = "(.cproc.dumb 9 8)";

        // The dumb coprocessor cannot be shadowed.
        let expr2 = "(let ((.cproc.dumb (lambda (a b) (* a b))))
                   (.cproc.dumb 9 8))";

        // The dumb coprocessor cannot be shadowed.
        let expr3 = "(.cproc.dumb 9 8 123))";

        let res = s.num(89);
        let error = s.get_cont_error();

        test_aux(s, &expr, Some(res), None, None, None, 1, Some(&lang));
        test_aux(s, &expr2, Some(res), None, None, None, 3, Some(&lang));
        test_aux(s, &expr3, None, None, Some(error), None, 1, Some(&lang));
    }
}
