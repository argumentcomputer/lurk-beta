use expect_test::expect;
use pasta_curves::pallas::Scalar as Fr;
use std::{cell::RefCell, rc::Rc, sync::Arc};

use crate::{
    eval::lang::{Coproc, Lang},
    lem::{store::Store, Tag},
    num::Num,
    proof::nova::C1LEM,
    state::user_sym,
    state::State,
    tag::{ExprTag, Op, Op1, Op2},
};

use super::{nova_test_full_aux, nova_test_full_aux2, test_aux, DEFAULT_REDUCTION_COUNT};

type M1<'a, Fr> = C1LEM<'a, Fr, Coproc<Fr>>;

#[test]
fn test_prove_self_evaluating() {
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
        test_aux::<_, _, M1<'_, _>>(s, expr, Some(expt), None, None, None, expect!["1"], &None);
    });

    let fun = s.intern_fun(s.intern_user_symbol("x"), s.list(vec![expt_nil]), expt_nil);
    nova_test_full_aux2::<_, _, M1<'_, _>>(
        s,
        fun,
        Some(fun),
        None,
        None,
        None,
        &expect!["1"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        Lang::new().into(),
    );
}

#[test]
fn test_prove_binop() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(+ 1 2)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
#[should_panic]
// This tests the testing mechanism. Since the supplied expected value is wrong,
// the test should panic on an assertion failure.
fn test_prove_binop_fail() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(2);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(+ 1 2)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_arithmetic_let() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((a 5)
                  (b 1)
                  (c 2))
             (/ (+ a b) c))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["18"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_eq() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();
    nova_test_full_aux::<_, _, M1<'_, _>>(
        s,
        "(eq 5 5)",
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        DEFAULT_REDUCTION_COUNT,
        true,
        None,
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_num_equal() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(= 5 5)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );

    let expected = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(= 5 6)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_invalid_num_equal() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(= 5 nil)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );

    let expected = s.num_u64(5);
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(= nil 5)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_equal() {
    let s = &Store::<Fr>::default();
    let nil = s.intern_nil();
    let t = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        "(eq 5 nil)",
        Some(nil),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(eq nil 5)",
        Some(nil),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(eq nil nil)",
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(eq 5 5)",
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_quote_end_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(quote (1) (2))",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_if() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(5);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(if t 5 6)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );

    let expected = s.num_u64(6);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(if nil 5 6)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    )
}

#[test]
fn test_prove_if_end_is_nil_error() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(5);
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(if nil 5 6 7)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    )
}

#[test]
#[ignore]
fn test_prove_if_fully_evaluates() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(10);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(if t (+ 5 5) 6)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
#[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
fn test_prove_recursion1() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(25);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((exp (lambda (base)
                           (lambda (exponent)
                             (if (= 0 exponent)
                                 1
                                 (* base ((exp base) (- exponent 1))))))))
             ((exp 5) 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["66"],
        &None,
    );
}

#[test]
#[ignore] // Skip expensive tests in CI for now. Do run these locally, please.
fn test_prove_recursion2() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(25);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((exp (lambda (base)
                              (lambda (exponent)
                                 (lambda (acc)
                                   (if (= 0 exponent)
                                      acc
                                      (((exp base) (- exponent 1)) (* acc base))))))))
            (((exp 5) 2) 1))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["93"],
        &None,
    );
}

fn test_prove_unop_regression_aux(chunk_count: usize) {
    let s = &Store::<Fr>::default();
    let expected = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();
    nova_test_full_aux::<_, _, M1<'_, _>>(
        s,
        "(atom 123)",
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        chunk_count, // This needs to be 1 to exercise the bug.
        false,
        None,
        &None,
    );

    let expected = s.num_u64(1);
    nova_test_full_aux::<_, _, M1<'_, _>>(
        s,
        "(car '(1 . 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        chunk_count, // This needs to be 1 to exercise the bug.
        false,
        None,
        &None,
    );

    let expected = s.num_u64(2);
    nova_test_full_aux::<_, _, M1<'_, _>>(
        s,
        "(cdr '(1 . 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["2"],
        chunk_count, // This needs to be 1 to exercise the bug.
        false,
        None,
        &None,
    );

    let expected = s.num_u64(123);
    nova_test_full_aux::<_, _, M1<'_, _>>(
        s,
        "(emit 123)",
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        chunk_count,
        false,
        None,
        &None,
    )
}

#[test]
#[ignore]
fn test_prove_unop_regression() {
    // We need to at least use chunk size 1 to exercise the regression.
    // Also use a non-1 value to check the MultiFrame case.
    for i in 1..2 {
        test_prove_unop_regression_aux(i);
    }
}

#[test]
#[ignore]
fn test_prove_emit_output() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(emit 123)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_evaluate() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(99);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (x) x) 99)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_evaluate2() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(99);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (y)
                ((lambda (x) y) 888))
              99)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["9"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_evaluate3() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(999);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (y)
                 ((lambda (x)
                    ((lambda (z) z)
                     x))
                  y))
               999)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["10"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_evaluate4() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(888);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (y)
                 ((lambda (x)
                    ((lambda (z) z)
                     x))
                  ;; NOTE: We pass a different value here.
                  888))
              999)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["10"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_evaluate5() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(999);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(((lambda (fn)
                  (lambda (x) (fn x)))
                (lambda (y) y))
               999)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["13"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_evaluate_sum() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(9);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(+ 2 (+ 3 4))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["6"],
        &None,
    );
}

#[test]
fn test_prove_binop_rest_is_nil() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(9);
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(- 9 8 7)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(= 9 8 7)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
}

fn op_syntax_error<T: Op + Copy>() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    let test = |op: T| {
        let name = op.symbol_name();

        if !op.supports_arity(0) {
            let expr = format!("({name})");
            tracing::debug!("{:?}", &expr);
            test_aux::<_, _, M1<'_, _>>(
                s,
                &expr,
                None,
                None,
                Some(error),
                None,
                expect!["1"],
                &None,
            );
        }
        if !op.supports_arity(1) {
            let expr = format!("({name} 123)");
            tracing::debug!("{:?}", &expr);
            test_aux::<_, _, M1<'_, _>>(
                s,
                &expr,
                None,
                None,
                Some(error),
                None,
                expect!["1"],
                &None,
            );
        }
        if !op.supports_arity(2) {
            let expr = format!("({name} 123 456)");
            tracing::debug!("{:?}", &expr);
            test_aux::<_, _, M1<'_, _>>(
                s,
                &expr,
                None,
                None,
                Some(error),
                None,
                expect!["1"],
                &None,
            );
        }

        if !op.supports_arity(3) {
            let expr = format!("({name} 123 456 789)");
            tracing::debug!("{:?}", &expr);
            let iterations = if op.supports_arity(2) {
                expect!["2"]
            } else {
                expect!["1"]
            };
            test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, iterations, &None);
        }
    };

    for op in T::all() {
        test(*op);
    }
}

#[test]
#[ignore]
fn test_prove_unop_syntax_error() {
    op_syntax_error::<Op1>();
}

#[test]
#[ignore]
fn test_prove_binop_syntax_error() {
    op_syntax_error::<Op2>();
}

#[test]
fn test_prove_diff() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(4);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(- 9 5)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_product() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(45);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(* 9 5)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_quotient() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(7);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(/ 21 3)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_error_div_by_zero() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(0);
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(/ 21 0)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_error_invalid_type_and_not_cons() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(/ 21 nil)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_adder() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(5);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(((lambda (x)
                (lambda (y)
                  (+ x y)))
              2)
             3)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["13"],
        &None,
    );
}

#[test]
fn test_prove_current_env_simple() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(current-env)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_current_env_rest_is_nil_error() {
    let s = &Store::<Fr>::default();
    let expected = s.read_with_default_state("(current-env a)").unwrap();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(current-env a)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_let_simple() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(1);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((a 1))
              a)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_let_end_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((a 1 2)) a)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_letrec_end_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((a 1 2)) a)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_lambda_empty_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (x)) 0)",
        None,
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_let_empty_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_let_empty_body_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((a 1)))",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_letrec_empty_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_letrec_empty_body_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((a 1)))",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_let_body_nil() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(eq nil (let () nil))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

#[test]
fn test_prove_let_rest_body_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((a 1)) a 1)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_letrec_rest_body_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((a 1)) a 1)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_let_null_bindings() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let () (+ 1 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}
#[test]
#[ignore]
fn test_prove_letrec_null_bindings() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec () (+ 1 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_let() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(6);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((a 1)
                   (b 2)
                   (c 3))
              (+ a (+ b c)))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["18"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_arithmetic() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(20);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((((lambda (x)
                  (lambda (y)
                    (lambda (z)
                      (* z
                         (+ x y)))))
                2)
              3)
             4)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["23"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_comparison() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((x 2)
                   (y 3)
                   (z 4))
              (= 20 (* z
                       (+ x y))))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["21"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_conditional() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(5);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((true (lambda (a)
                           (lambda (b)
                             a)))
                   (false (lambda (a)
                            (lambda (b)
                              b)))
                  ;; NOTE: We cannot shadow IF because it is built-in.
                  (if- (lambda (a)
                         (lambda (c)
                           (lambda (cond)
                             ((cond a) c))))))
             (((if- 5) 6) true))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["35"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_conditional2() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(6);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((true (lambda (a)
                           (lambda (b)
                             a)))
                   (false (lambda (a)
                            (lambda (b)
                              b)))
                  ;; NOTE: We cannot shadow IF because it is built-in.
                  (if- (lambda (a)
                         (lambda (c)
                           (lambda (cond)
                             ((cond a) c))))))
             (((if- 5) 6) false))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["32"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_fundamental_conditional_bug() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(5);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((true (lambda (a)
                           (lambda (b)
                             a)))
                   ;; NOTE: We cannot shadow IF because it is built-in.
                   (if- (lambda (a)
                          (lambda (c)
                           (lambda (cond)
                             ((cond a) c))))))
             (((if- 5) 6) true))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["32"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_fully_evaluates() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(10);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(if t (+ 5 5) 6)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_recursion() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(25);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((exp (lambda (base)
                               (lambda (exponent)
                                 (if (= 0 exponent)
                                     1
                                     (* base ((exp base) (- exponent 1))))))))
                       ((exp 5) 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["66"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_recursion_multiarg() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(25);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((exp (lambda (base exponent)
                               (if (= 0 exponent)
                                   1
                                   (* base (exp base (- exponent 1)))))))
                       (exp 5 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["69"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_recursion_optimized() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(25);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((exp (lambda (base)
                            (letrec ((base-inner
                                       (lambda (exponent)
                                         (if (= 0 exponent)
                                             1
                                             (* base (base-inner (- exponent 1)))))))
                                    base-inner))))
               ((exp 5) 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["56"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_tail_recursion() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(25);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((exp (lambda (base)
                               (lambda (exponent-remaining)
                                 (lambda (acc)
                                   (if (= 0 exponent-remaining)
                                       acc
                                       (((exp base) (- exponent-remaining 1)) (* acc base))))))))
                      (((exp 5) 2) 1))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["93"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_tail_recursion_somewhat_optimized() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(25);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((exp (lambda (base)
                               (letrec ((base-inner
                                          (lambda (exponent-remaining)
                                            (lambda (acc)
                                              (if (= 0 exponent-remaining)
                                                  acc
                                                 ((base-inner (- exponent-remaining 1)) (* acc base)))))))
                                       base-inner))))
                      (((exp 5) 2) 1))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["81"], &None
    );
}

#[test]
#[ignore]
fn test_prove_no_mutual_recursion() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((even (lambda (n)
                              (if (= 0 n)
                                  t
                                  (odd (- n 1)))))
                      (odd (lambda (n)
                             (even (- n 1)))))
                    ;; NOTE: This is not true mutual-recursion.
                    ;; However, it exercises the behavior of LETREC.
                    (odd 1))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["22"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_no_mutual_recursion_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((even (lambda (n)
                              (if (= 0 n)
                                  t
                                  (odd (- n 1)))))
                      (odd (lambda (n)
                             (even (- n 1)))))
                    ;; NOTE: This is not true mutual-recursion.
                    ;; However, it exercises the behavior of LETREC.
                    (odd 2))",
        None,
        None,
        Some(error),
        None,
        expect!["25"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_cons1() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(1);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(car (cons 1 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_car_end_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(car (1 2) 3)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_cdr_end_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(cdr (1 2) 3)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_atom_end_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(atom 123 4)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_emit_end_is_nil_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(emit 123 4)",
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_cons2() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(2);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(cdr (cons 1 2))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_zero_arg_lambda1() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda () 123))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_zero_arg_lambda2() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(10);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((x 9) (f (lambda () (+ x 1)))) (f))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["10"],
        &None,
    );
}

#[test]
fn test_prove_zero_arg_lambda3() {
    let s = &Store::<Fr>::default();
    let expected = {
        let arg = s.intern_user_symbol("x");
        let num = s.num_u64(123);
        let body = s.list(vec![num]);
        let env = s.intern_nil();
        s.intern_fun(arg, body, env)
    };
    let terminal = s.cont_terminal();
    nova_test_full_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (x) 123))",
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        &None,
    );
}

#[test]
fn test_prove_zero_arg_lambda4() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda () 123) 1)",
        None,
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_zero_arg_lambda5() {
    let s = &Store::<Fr>::default();
    let expected = s.read_with_default_state("(123)").unwrap();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(123)",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_zero_arg_lambda6() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(123);
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((emit 123))",
        Some(expected),
        None,
        Some(error),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_nested_let_closure_regression() {
    let s = &Store::<Fr>::default();
    let terminal = s.cont_terminal();
    let expected = s.num_u64(6);
    let expr = "(let ((data-function (lambda () 123))
                      (x 6)
                      (data (data-function)))
                  x)";
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["14"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_minimal_tail_call() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec
               ((f (lambda (x)
                     (if (= x 3)
                         123
                         (f (+ x 1))))))
               (f 0))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["50"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_cons_in_function1() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(2);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(((lambda (a)
                (lambda (b)
                  (car (cons a b))))
              2)
             3)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["15"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_cons_in_function2() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(((lambda (a)
                (lambda (b)
                  (cdr (cons a b))))
              2)
             3)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["15"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_multiarg_eval_bug() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(2);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(car (cdr '(1 2 3 4)))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_multiple_letrec_bindings() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec
               ((x 888)
                (f (lambda (x)
                     (if (= x 5)
                         123
                         (f (+ x 1))))))
              (f 0))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["78"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_tail_call2() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec
               ((f (lambda (x)
                     (if (= x 5)
                         123
                         (f (+ x 1)))))
                (g (lambda (x) (f x))))
              (g 0))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["84"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_multiple_letrecstar_bindings() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(13);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((double (lambda (x) (* 2 x)))
                       (square (lambda (x) (* x x))))
                      (+ (square 3) (double 2)))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["22"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_multiple_letrecstar_bindings_referencing() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(11);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((double (lambda (x) (* 2 x)))
                       (double-inc (lambda (x) (+ 1 (double x)))))
                      (+ (double 3) (double-inc 2)))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["31"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_multiple_letrecstar_bindings_recursive() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(33);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((exp (lambda (base exponent)
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
                        (exp3 4 2)))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["242"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_dont_discard_rest_env() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(18);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((z 9))
               (letrec ((a 1)
                         (b 2)
                         (l (lambda (x) (+ z x))))
                        (l 9)))",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["22"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_fibonacci() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(1);
    let terminal = s.cont_terminal();
    nova_test_full_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((next (lambda (a b n target)
                 (if (eq n target)
                     a
                     (next b
                         (+ a b)
                         (+ 1 n)
                        target))))
                (fib (next 0 1 0)))
            (fib 1))",
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["89"],
        5,
        false,
        None,
        &None,
    );
}

/// This test is a follow up to https://github.com/lurk-lab/lurk-rs/pull/931,
/// which reverts a PR that made the "parallel steps" flow break
#[test]
#[ignore]
fn test_one_folding() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(4);
    let terminal = s.cont_terminal();
    nova_test_full_aux::<_, _, M1<'_, _>>(
        s,
        "(+ 1 (+ 1 (+ 1 1)))",
        Some(expected),
        None,
        Some(terminal),
        None,
        &expect!["9"],
        5,    // 9 iterations and rc=5 causes one folding to happen and uses the cached witness
        true, // generate Nova proof and verify it
        None,
        &None,
    );
}

#[test]
fn test_prove_terminal_continuation_regression() {
    let s = &Store::<Fr>::default();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((a (lambda (x) (cons 2 2))))
           (a 1))",
        None,
        None,
        Some(terminal),
        None,
        expect!["9"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_chained_functional_commitment() {
    let s = &Store::<Fr>::default();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((secret 12345)
                  (a (lambda (acc x)
                       (let ((acc (+ acc x)))
                         (cons acc (cons secret (a acc)))))))
            (a 0 5))",
        None,
        None,
        Some(terminal),
        None,
        expect!["39"],
        &None,
    );
}

#[test]
fn test_prove_begin_empty() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(begin)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_begin_emit() {
    let s = &Store::<Fr>::default();
    let expr = "(begin (emit 1) (emit 2) (emit 3))";
    let expected_expr = s.num_u64(3);
    let expected_emitted = vec![s.num_u64(1), s.num_u64(2), s.num_u64(3)];
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected_expr),
        None,
        None,
        Some(&expected_emitted),
        expect!["13"],
        &None,
    );
}

#[test]
fn test_prove_str_car() {
    let s = &Store::<Fr>::default();
    let expected_a = s.read_with_default_state(r"#\a").unwrap();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car "apple")"#,
        Some(expected_a),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_str_cdr() {
    let s = &Store::<Fr>::default();
    let expected_pple = s.read_with_default_state(r#" "pple" "#).unwrap();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr "apple")"#,
        Some(expected_pple),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_str_car_empty() {
    let s = &Store::<Fr>::default();
    let expected_nil = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car "")"#,
        Some(expected_nil),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_str_cdr_empty() {
    let s = &Store::<Fr>::default();
    let expected_empty_str = s.intern_string("");
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr "")"#,
        Some(expected_empty_str),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_strcons() {
    let s = &Store::<Fr>::default();
    let expected_apple = s.read_with_default_state(r#" "apple" "#).unwrap();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(strcons #\a "pple")"#,
        Some(expected_apple),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_str_cons_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r"(strcons #\a 123)",
        None,
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_one_arg_cons_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cons "")"#,
        None,
        None,
        Some(error),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_car_nil() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car nil)"#,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_cdr_nil() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr nil)"#,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_car_cdr_invalid_tag_error_sym() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car car)"#,
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr car)"#,
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_car_cdr_invalid_tag_error_char() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r"(car #\a)",
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r"(cdr #\a)",
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_car_cdr_invalid_tag_error_num() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car 42)"#,
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr 42)"#,
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_car_cdr_of_cons() {
    let s = &Store::<Fr>::default();
    let res1 = s.num_u64(1);
    let res2 = s.num_u64(2);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car (cons 1 2))"#,
        Some(res1),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr (cons 1 2))"#,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_car_cdr_invalid_tag_error_lambda() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car (lambda (x) x))"#,
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr (lambda (x) x))"#,
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_hide_open() {
    let s = &Store::<Fr>::default();
    let expr = "(open (hide 123 456))";
    let expected = s.num_u64(456);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_hide_wrong_secret_type() {
    let s = &Store::<Fr>::default();
    let expr = "(hide 'x 456)";
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["3"], &None);
}

#[test]
fn test_prove_hide_secret() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (hide 123 456))";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_hide_open_sym() {
    let s = &Store::<Fr>::default();
    let expr = "(open (hide 123 'x))";
    let x = s.intern_user_symbol("x");
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(x),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_commit_open_sym() {
    let s = &Store::<Fr>::default();
    let expr = "(open (commit 'x))";
    let x = s.intern_user_symbol("x");
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(x),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

#[test]
fn test_prove_commit_open() {
    let s = &Store::<Fr>::default();
    let expr = "(open (commit 123))";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

#[test]
fn test_prove_commit_error() {
    let s = &Store::<Fr>::default();
    let expr = "(commit 123 456)";
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["1"], &None);
}

#[test]
fn test_prove_open_error() {
    let s = &Store::<Fr>::default();
    let expr = "(open 123 456)";
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["1"], &None);
}

#[test]
fn test_prove_open_wrong_type() {
    let s = &Store::<Fr>::default();
    let expr = "(open 'asdf)";
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["2"], &None);
}

#[test]
fn test_prove_secret_wrong_type() {
    let s = &Store::<Fr>::default();
    let expr = "(secret 'asdf)";
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["2"], &None);
}

#[test]
fn test_prove_commit_secret() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (commit 123))";
    let expected = s.num_u64(0);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

#[test]
fn test_prove_num() {
    let s = &Store::<Fr>::default();
    let expr = "(num 123)";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_num_char() {
    let s = &Store::<Fr>::default();
    let expr = r"(num #\a)";
    let expected = s.num_u64(97);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_char_num() {
    let s = &Store::<Fr>::default();
    let expr = r#"(char 97)"#;
    let expected_a = s.read_with_default_state(r"#\a").unwrap();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected_a),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_char_coercion() {
    let s = &Store::<Fr>::default();
    let expr = r#"(char (- 0 4294967200))"#;
    let expr2 = r#"(char (- 0 4294967199))"#;
    let expected_a = s.read_with_default_state(r"#\a").unwrap();
    let expected_b = s.read_with_default_state(r"#\b").unwrap();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected_a),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(expected_b),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_commit_num() {
    let s = &Store::<Fr>::default();
    let expr = "(num (commit 123))";
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        None,
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

#[test]
fn test_prove_hide_open_comm_num() {
    let s = &Store::<Fr>::default();
    let expr = "(open (comm (num (hide 123 456))))";
    let expected = s.num_u64(456);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["9"],
        &None,
    );
}

#[test]
fn test_prove_hide_secret_comm_num() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (comm (num (hide 123 456))))";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["9"],
        &None,
    );
}

#[test]
fn test_prove_commit_open_comm_num() {
    let s = &Store::<Fr>::default();
    let expr = "(open (comm (num (commit 123))))";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["8"],
        &None,
    );
}

#[test]
fn test_prove_commit_secret_comm_num() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (comm (num (commit 123))))";
    let expected = s.num_u64(0);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["8"],
        &None,
    );
}

#[test]
fn test_prove_commit_num_open() {
    let s = &Store::<Fr>::default();
    let expr = "(open (num (commit 123)))";
    let expected = s.num_u64(123);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["6"],
        &None,
    );
}

#[test]
fn test_prove_num_invalid_tag() {
    let s = &Store::<Fr>::default();
    let expr = "(num (quote x))";
    let expr1 = "(num \"asdf\")";
    let expr2 = "(num '(1))";
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["2"], &None);
    test_aux::<_, _, M1<'_, _>>(s, expr1, None, None, Some(error), None, expect!["2"], &None);
    test_aux::<_, _, M1<'_, _>>(s, expr2, None, None, Some(error), None, expect!["2"], &None);
}

#[test]
fn test_prove_comm_invalid_tag() {
    let s = &Store::<Fr>::default();
    let expr = "(comm (quote x))";
    let expr1 = "(comm \"asdf\")";
    let expr2 = "(comm '(1))";
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["2"], &None);
    test_aux::<_, _, M1<'_, _>>(s, expr1, None, None, Some(error), None, expect!["2"], &None);
    test_aux::<_, _, M1<'_, _>>(s, expr2, None, None, Some(error), None, expect!["2"], &None);
}

#[test]
fn test_prove_char_invalid_tag() {
    let s = &Store::<Fr>::default();
    let expr = "(char (quote x))";
    let expr1 = "(char \"asdf\")";
    let expr2 = "(char '(1))";
    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["2"], &None);
    test_aux::<_, _, M1<'_, _>>(s, expr1, None, None, Some(error), None, expect!["2"], &None);
    test_aux::<_, _, M1<'_, _>>(s, expr2, None, None, Some(error), None, expect!["2"], &None);
}

#[test]
fn test_prove_terminal_sym() {
    let s = &Store::<Fr>::default();
    let expr = "(quote x)";
    let x = s.intern_user_symbol("x");
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(x),
        None,
        Some(terminal),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
#[should_panic]
fn test_prove_open_opaque_commit() {
    let s = &Store::<Fr>::default();
    let expr = "(open 123)";
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, None, None, expect!["2"], &None);
}

#[test]
#[should_panic]
fn test_prove_secret_invalid_tag() {
    let s = &Store::<Fr>::default();
    let expr = "(secret 123)";
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, None, None, expect!["2"], &None);
}

#[test]
#[should_panic]
fn test_prove_secret_opaque_commit() {
    let s = &Store::<Fr>::default();
    let expr = "(secret (comm 123))";
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, None, None, expect!["2"], &None);
}

#[test]
fn test_str_car_cdr_cons() {
    let s = &Store::<Fr>::default();
    let a = s.read_with_default_state(r"#\a").unwrap();
    let apple = s.read_with_default_state(r#" "apple" "#).unwrap();
    let a_pple = s.read_with_default_state(r#" (#\a . "pple") "#).unwrap();
    let pple = s.read_with_default_state(r#" "pple" "#).unwrap();
    let empty = s.intern_string("");
    let nil = s.intern_nil();
    let terminal = s.cont_terminal();
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car "apple")"#,
        Some(a),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr "apple")"#,
        Some(pple),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(car "")"#,
        Some(nil),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cdr "")"#,
        Some(empty),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(cons #\a "pple")"#,
        Some(a_pple),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );

    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(strcons #\a "pple")"#,
        Some(apple),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );

    test_aux::<_, _, M1<'_, _>>(
        s,
        r"(strcons #\a #\b)",
        None,
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );

    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(strcons "a" "b")"#,
        None,
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );

    test_aux::<_, _, M1<'_, _>>(
        s,
        r#"(strcons 1 2)"#,
        None,
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
}

fn relational_aux(s: &Store<Fr>, op: &str, a: &str, b: &str, res: bool) {
    let expr = &format!("({op} {a} {b})");
    let expected = if res {
        s.intern_lurk_symbol("t")
    } else {
        s.intern_nil()
    };
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[ignore]
#[test]
fn test_prove_test_relational() {
    let s = &Store::<Fr>::default();
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
    let s = &Store::<Fr>::default();
    // Normally, a value cannot be less than the result of incrementing it.
    // However, the most positive field element (when viewed as signed)
    // is the exception. Incrementing it yields the most negative element,
    // which is less than the most positive.
    let expr = "(let ((most-positive (/ (- 0 1) 2))
                      (most-negative (+ 1 most-positive)))
                  (< most-negative most-positive))";
    let t = s.intern_lurk_symbol("t");
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["19"],
        &None,
    );
}

#[test]
fn test_prove_test_eval() {
    let s = &Store::<Fr>::default();
    let expr = "(* 3 (eval  (cons '+ (cons 1 (cons 2 nil)))))";
    let expr2 = "(* 5 (eval '(+ 1 a) '((a . 3))))"; // two-arg eval, optional second arg is env.
    let res = s.num_u64(9);
    let res2 = s.num_u64(20);
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["17"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["9"],
        &None,
    );
}

#[test]
fn test_prove_test_keyword() {
    let s = &Store::<Fr>::default();

    let expr = ":asdf";
    let expr2 = "(eq :asdf :asdf)";
    let expr3 = "(eq :asdf 'asdf)";
    let res = s.key("asdf");
    let res2 = s.intern_lurk_symbol("t");
    let res3 = s.intern_nil();

    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["1"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr3,
        Some(res3),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

// The following functional commitment tests were discovered to fail. They are commented out (as tests) for now so
// they can be addressed independently in future work.

#[test]
fn test_prove_functional_commitment() {
    let s = &Store::<Fr>::default();

    let expr = "(let ((f (commit (let ((num 9)) (lambda (f) (f num)))))
                      (inc (lambda (x) (+ x 1))))
                  ((open f) inc))";
    let res = s.num_u64(10);
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["25"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_complicated_functional_commitment() {
    let s = &Store::<Fr>::default();

    let expr = "(let ((f (commit (let ((nums '(1 2 3))) (lambda (f) (f nums)))))
                      (in (letrec ((sum-aux (lambda (acc nums)
                                          (if nums
                                            (sum-aux (+ acc (car nums)) (cdr nums))
                                            acc)))
                               (sum (sum-aux 0)))
                         (lambda (nums)
                           (sum nums)))))

                  ((open f) in))";
    let res = s.num_u64(6);
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["108"],
        &None,
    );
}

#[test]
fn test_prove_test_fold_cons_regression() {
    let s = &Store::<Fr>::default();
    let expr = "(letrec ((fold (lambda (op acc l)
                                 (if l
                                     (fold op (op acc (car l)) (cdr l))
                                     acc))))
                  (fold (lambda (x y) (+ x y)) 0 '(1 2 3)))";
    let res = s.num_u64(6);
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["152"],
        &None,
    );
}

#[test]
fn test_prove_test_lambda_args_regression() {
    let s = &Store::<Fr>::default();

    let expr = "(cons (lambda (x y) nil) nil)";
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        None,
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_reduce_sym_contradiction_regression() {
    let s = &Store::<Fr>::default();

    let expr = "(eval 'a '(nil))";
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["4"], &None);
}

#[test]
fn test_prove_test_self_eval_env_not_nil() {
    let s = &Store::<Fr>::default();

    // NOTE: cond1 shouldn't depend on env-is-not-nil
    // therefore this unit test is not very useful
    // the conclusion is that by removing condition env-is-not-nil from cond1,
    // we solve this soundness problem
    // this solution makes the circuit a bit smaller
    let expr = "(let ((a 1)) t)";

    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        None,
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_test_self_eval_nil() {
    let s = &Store::<Fr>::default();

    // nil doesn't have SYM tag
    let expr = "nil";

    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        None,
        None,
        Some(terminal),
        None,
        expect!["1"],
        &None,
    );
}

#[test]
fn test_prove_test_env_not_nil_and_binding_nil() {
    let s = &Store::<Fr>::default();

    let expr = "(let ((a 1) (b 2)) c)";

    let error = s.cont_error();
    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["7"], &None);
}

#[test]
fn test_prove_test_eval_bad_form() {
    let s = &Store::<Fr>::default();
    let expr = "(* 5 (eval '(+ 1 a) '((0 . 3))))"; // two-arg eval, optional second arg is env. This tests for error on malformed env.
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["8"], &None);
}

#[test]
fn test_prove_test_u64_mul() {
    let s = &Store::<Fr>::default();

    let expr = "(* (u64 18446744073709551615) (u64 2))";
    let expr2 = "(* 18446744073709551615u64 2u64)";
    let expr3 = "(* (- 0u64 1u64) 2u64)";
    let expr4 = "(u64 18446744073709551617)";
    let res = s.u64(18446744073709551614);
    let res2 = s.u64(1);
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["7"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr3,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["6"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr4,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
}

#[test]
fn test_prove_test_u64_add() {
    let s = &Store::<Fr>::default();

    let expr = "(+ 18446744073709551615u64 2u64)";
    let expr2 = "(+ (- 0u64 1u64) 2u64)";
    let res = s.u64(1);
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["6"],
        &None,
    );
}

#[test]
fn test_prove_test_u64_sub() {
    let s = &Store::<Fr>::default();

    let expr = "(- 2u64 1u64)";
    let expr2 = "(- 0u64 1u64)";
    let expr3 = "(+ 1u64 (- 0u64 1u64))";
    let res = s.u64(1);
    let res2 = s.u64(18446744073709551615);
    let res3 = s.u64(0);
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr3,
        Some(res3),
        None,
        Some(terminal),
        None,
        expect!["6"],
        &None,
    );
}

#[test]
fn test_prove_test_u64_div() {
    let s = &Store::<Fr>::default();

    let expr = "(/ 100u64 2u64)";
    let res = s.u64(50);

    let expr2 = "(/ 100u64 3u64)";
    let res2 = s.u64(33);

    let expr3 = "(/ 100u64 0u64)";

    let terminal = s.cont_terminal();
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(s, expr3, None, None, Some(error), None, expect!["3"], &None);
}

#[test]
fn test_prove_test_u64_mod() {
    let s = &Store::<Fr>::default();

    let expr = "(% 100u64 2u64)";
    let res = s.u64(0);

    let expr2 = "(% 100u64 3u64)";
    let res2 = s.u64(1);

    let expr3 = "(% 100u64 0u64)";

    let terminal = s.cont_terminal();
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(s, expr3, None, None, Some(error), None, expect!["3"], &None);
}

#[test]
fn test_prove_test_num_mod() {
    let s = &Store::<Fr>::default();

    let expr = "(% 100 3)";
    let expr2 = "(% 100 3u64)";
    let expr3 = "(% 100u64 3)";

    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["3"], &None);
    test_aux::<_, _, M1<'_, _>>(s, expr2, None, None, Some(error), None, expect!["3"], &None);
    test_aux::<_, _, M1<'_, _>>(s, expr3, None, None, Some(error), None, expect!["3"], &None);
}

#[test]
fn test_prove_test_u64_comp() {
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

    let t = s.intern_lurk_symbol("t");
    let nil = s.intern_nil();
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(nil),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr3,
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr4,
        Some(nil),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr5,
        Some(nil),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr6,
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr7,
        Some(nil),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr8,
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr9,
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr10,
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_test_u64_conversion() {
    let s = &Store::<Fr>::default();

    let expr = "(+ 0 1u64)";
    let expr2 = "(num 1u64)";
    let expr3 = "(+ 1 1u64)";
    let expr4 = "(u64 (+ 1 1))";
    let res = s.num_u64(1);
    let res2 = s.num_u64(2);
    let res3 = s.u64(2);
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr3,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr4,
        Some(res3),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}

#[test]
fn test_prove_test_u64_num_comparison() {
    let s = &Store::<Fr>::default();

    let expr = "(= 1 1u64)";
    let expr2 = "(= 1 2u64)";
    let t = s.intern_lurk_symbol("t");
    let nil = s.intern_nil();
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(t),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(nil),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_test_u64_num_cons() {
    let s = &Store::<Fr>::default();

    let expr = "(cons 1 1u64)";
    let expr2 = "(cons 1u64 1)";
    let res = s.read_with_default_state("(1 . 1u64)").unwrap();
    let res2 = s.read_with_default_state("(1u64 . 1)").unwrap();
    let terminal = s.cont_terminal();

    test_aux::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
fn test_prove_test_hide_u64_secret() {
    let s = &Store::<Fr>::default();

    let expr = "(hide 0u64 123)";
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["3"], &None);
}

#[test]
fn test_prove_test_mod_by_zero_error() {
    let s = &Store::<Fr>::default();

    let expr = "(% 0 0)";
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["3"], &None);
}

#[test]
fn test_prove_dotted_syntax_error() {
    let s = &Store::<Fr>::default();
    let expr = "(let ((a (lambda (x) (+ x 1)))) (a . 1))";
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(s, expr, None, None, Some(error), None, expect!["3"], &None);
}

#[test]
fn test_prove_call_literal_fun() {
    let s = &Store::<Fr>::default();
    let empty_env = s.intern_nil();
    let arg = s.intern_user_symbol("x");
    let body = s.read_with_default_state("((+ x 1))").unwrap();
    let fun = s.intern_3_ptrs(Tag::Expr(ExprTag::Fun), arg, body, empty_env);
    let input = s.num_u64(9);
    let expr = s.list(vec![fun, input]);
    let res = s.num_u64(10);
    let terminal = s.cont_terminal();
    let lang: Arc<Lang<Fr, Coproc<Fr>>> = Arc::new(Lang::new());

    nova_test_full_aux2::<_, _, M1<'_, _>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["7"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        lang,
    );
}

#[test]
fn test_prove_lambda_body_syntax() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();

    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda ()))",
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda () 1 2))",
        None,
        None,
        Some(error),
        None,
        expect!["2"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (x)) 1)",
        None,
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (x) 1 2) 1)",
        None,
        None,
        Some(error),
        None,
        expect!["3"],
        &None,
    );
}

#[test]
#[ignore]
fn test_prove_non_symbol_binding_error() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();

    let test = |x| {
        let expr = format!("(let (({x} 123)) {x})");
        let expr2 = format!("(letrec (({x} 123)) {x})");
        let expr3 = format!("(lambda ({x}) {x})");

        test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, expect!["1"], &None);
        test_aux::<_, _, M1<'_, _>>(
            s,
            &expr2,
            None,
            None,
            Some(error),
            None,
            expect!["1"],
            &None,
        );
        test_aux::<_, _, M1<'_, _>>(
            s,
            &expr3,
            None,
            None,
            Some(error),
            None,
            expect!["1"],
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
fn test_prove_head_with_sym_mimicking_value() {
    let s = &Store::<Fr>::default();
    let error = s.cont_error();

    let hash_num = |s: &Store<Fr>, state: Rc<RefCell<State>>, name| {
        let sym = s.read(state, name).unwrap();
        let z_ptr = s.hash_ptr(&sym);
        let hash = *z_ptr.value();
        Num::Scalar(hash)
    };

    let state = State::init_lurk_state().rccell();
    {
        // binop
        let expr = format!("({} 1 1)", hash_num(s, state.clone(), "+"));
        test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, expect!["1"], &None);
    }
    {
        // unop
        let expr = format!("({} '(1 . 2))", hash_num(s, state.clone(), "car"));
        test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, expect!["1"], &None);
    }
    {
        // let_or_letrec
        let expr = format!("({} ((a 1)) a)", hash_num(s, state.clone(), "let"));
        test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, expect!["1"], &None);
    }
    {
        // current-env
        let expr = format!("({})", hash_num(s, state.clone(), "current-env"));
        test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, expect!["1"], &None);
    }
    {
        // lambda
        let expr = format!("({} (x) 123)", hash_num(s, state.clone(), "lambda"));
        test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, expect!["1"], &None);
    }
    {
        // quote
        let expr = format!("({} asdf)", hash_num(s, state.clone(), "quote"));
        test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, expect!["1"], &None);
    }
    {
        // if
        let expr = format!("({} t 123 456)", hash_num(s, state, "if"));
        test_aux::<_, _, M1<'_, _>>(s, &expr, None, None, Some(error), None, expect!["1"], &None);
    }
}

#[test]
fn test_dumb_lang() {
    use crate::coprocessor::test::DumbCoprocessor;

    let s = &Store::<Fr>::default();

    let mut lang = Lang::<Fr, DumbCoprocessor<Fr>>::new();
    let name = user_sym("cproc-dumb");
    let dumb = DumbCoprocessor::new();

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
    let lang = Arc::new(lang);

    test_aux::<_, _, C1LEM<'_, _, DumbCoprocessor<_>>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["3"],
        &Some(lang.clone()),
    );
    test_aux::<_, _, C1LEM<'_, _, DumbCoprocessor<_>>>(
        s,
        expr2,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["6"],
        &Some(lang.clone()),
    );
    test_aux::<_, _, C1LEM<'_, _, DumbCoprocessor<_>>>(
        s,
        expr3,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["9"],
        &Some(lang.clone()),
    );
    test_aux::<_, _, C1LEM<'_, _, DumbCoprocessor<_>>>(
        s,
        expr4,
        Some(error4),
        None,
        Some(error),
        None,
        expect!["4"],
        &Some(lang.clone()),
    );
    test_aux::<_, _, C1LEM<'_, _, DumbCoprocessor<_>>>(
        s,
        expr5,
        Some(error5),
        None,
        Some(error),
        None,
        expect!["2"],
        &Some(lang.clone()),
    );
    test_aux::<_, _, C1LEM<'_, _, DumbCoprocessor<_>>>(
        s,
        expr6,
        Some(error6),
        None,
        Some(error),
        None,
        expect!["3"],
        &Some(lang.clone()),
    );
    test_aux::<_, _, C1LEM<'_, _, DumbCoprocessor<_>>>(
        s,
        expr6_,
        Some(error6),
        None,
        Some(error),
        None,
        expect!["3"],
        &Some(lang.clone()),
    );
    test_aux::<_, _, C1LEM<'_, _, DumbCoprocessor<_>>>(
        s,
        expr7,
        Some(error7),
        None,
        Some(error),
        None,
        expect!["3"],
        &Some(lang),
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

    test_aux::<_, _, C1LEM<'_, _, Terminator<_>>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        expect!["1"],
        &Some(lang.into()),
    );
}

#[test]
fn test_trie_lang() {
    use crate::coprocessor::trie::{install, TrieCoproc};

    let s = &Store::<Fr>::default();
    let state = State::init_lurk_state().rccell();
    let mut lang = Lang::<Fr, TrieCoproc<Fr>>::new();

    install(&state, &mut lang);

    let lang = Arc::new(lang);

    let terminal = s.cont_terminal();

    let expr = "(let ((trie (.lurk.trie.new)))
                      trie)";
    let expr = s.read(state.clone(), expr).unwrap();
    let res = s
        .read_with_default_state(
            "0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53",
        )
        .unwrap();
    nova_test_full_aux2::<_, _, C1LEM<'_, _, TrieCoproc<_>>>(
        s,
        expr,
        Some(res),
        None,
        Some(terminal),
        None,
        &expect!["4"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        lang.clone(),
    );

    let expr2 =
        "(.lurk.trie.lookup 0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53 123)";
    let expr2 = s.read(state.clone(), expr2).unwrap();
    let res2 = s.comm(Fr::zero());
    nova_test_full_aux2::<_, _, C1LEM<'_, _, TrieCoproc<_>>>(
        s,
        expr2,
        Some(res2),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        lang.clone(),
    );

    let expr3 =
        "(.lurk.trie.insert 0x1cc5b90039db85fd519af975afa1de9d2b92960a585a546637b653b115bc3b53 123 456)";
    let expr3 = s.read(state.clone(), expr3).unwrap();
    let res3 = s
        .read_with_default_state(
            "0x1b22dc5a394231c34e4529af674dc56a736fbd07508acfd1d12c0e67c8b4de27",
        )
        .unwrap();
    nova_test_full_aux2::<_, _, C1LEM<'_, _, TrieCoproc<_>>>(
        s,
        expr3,
        Some(res3),
        None,
        Some(terminal),
        None,
        &expect!["4"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        lang.clone(),
    );

    let expr4 =
        "(.lurk.trie.lookup 0x1b22dc5a394231c34e4529af674dc56a736fbd07508acfd1d12c0e67c8b4de27 123)";
    let expr4 = s.read(state.clone(), expr4).unwrap();
    let res4 = s.comm(Fr::from(456));
    nova_test_full_aux2::<_, _, C1LEM<'_, _, TrieCoproc<_>>>(
        s,
        expr4,
        Some(res4),
        None,
        Some(terminal),
        None,
        &expect!["3"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        lang.clone(),
    );

    let s = &Store::<Fr>::default();
    let terminal = s.cont_terminal();
    let expr5 = "(let ((trie (.lurk.trie.new))
                       (found (.lurk.trie.lookup trie 123)))
                      found)";
    let expr5 = s.read(state.clone(), expr5).unwrap();
    let res5 = s.comm(Fr::zero());
    nova_test_full_aux2::<_, _, C1LEM<'_, _, TrieCoproc<_>>>(
        s,
        expr5,
        Some(res5),
        None,
        Some(terminal),
        None,
        &expect!["9"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        lang.clone(),
    );

    let expr6 = "(let ((trie (.lurk.trie.insert (.lurk.trie.new) 123 456))
                       (found (.lurk.trie.lookup trie 123)))
                      found)";
    let expr6 = s.read(state.clone(), expr6).unwrap();
    let res6 = s.comm(Fr::from(456));
    nova_test_full_aux2::<_, _, C1LEM<'_, _, TrieCoproc<_>>>(
        s,
        expr6,
        Some(res6),
        None,
        Some(terminal),
        None,
        &expect!["13"],
        DEFAULT_REDUCTION_COUNT,
        false,
        None,
        lang.clone(),
    );
}

// This is related to issue #426
#[test]
fn test_prove_lambda_body_nil() {
    let s = &Store::<Fr>::default();
    let expected = s.intern_nil();
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "((lambda (x) nil) 0)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["4"],
        &None,
    );
}

// The following 3 tests are related to issue #424
#[test]
fn test_letrec_let_nesting() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(2);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((x (let ((z 0)) 1))) 2)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["6"],
        &None,
    );
}
#[test]
fn test_let_sequencing() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(1);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(let ((x 0) (y x)) 1)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["5"],
        &None,
    );
}
#[test]
fn test_letrec_sequencing() {
    let s = &Store::<Fr>::default();
    let expected = s.num_u64(3);
    let terminal = s.cont_terminal();
    test_aux::<_, _, M1<'_, _>>(
        s,
        "(letrec ((x 0) (y (letrec ((inner 1)) 2))) 3)",
        Some(expected),
        None,
        Some(terminal),
        None,
        expect!["8"],
        &None,
    );
}
