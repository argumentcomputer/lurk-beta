#[cfg(test)]
mod test {
    use blstrs::Scalar as Fr;
    use lurk::{eval::IO, store::Store};
    use lurk_macro::{let_store, lurk};

    #[test]
    fn test_let_store() {
        let_store!();
    }

    #[test]
    fn test_lurk() {
        let_store!();
        let res = lurk!((cons 1 2)).unwrap();

        let res2 = s_.read("(cons 1 2)").unwrap();

        assert_eq!(res2, res);
    }
    #[test]
    fn test_letstar() {
        let_store!();
        let res = lurk!((let ((a 1)) a)).unwrap();

        let res2 = s_.read("(let ((a 1)) a)").unwrap();

        assert_eq!(res2, res);
    }

    #[test]
    fn test_letrecstar() {
        let_store!();
        let res = lurk!((letrec ((a 1)) a)).unwrap();

        lurk!((let ((a 1)
                    (b 2)
                    (c (lambda (x) (* x x))))
               (+ a (c b))))
        .unwrap();

        let res2 = s_.read("(letrec ((a 1)) a)").unwrap();

        assert_eq!(res2, res);
    }

    use lurk::eval::{empty_sym_env, Evaluator};

    #[test]
    fn outer_evaluate_recursion1() {
        // This test is an example of simple usage. Compare to the commented-out original source for this test.

        // let mut s = Store::<Fr>::default();
        let_store!();
        let limit = 200;

        let expr = lurk!((letrec ((exp (lambda (base)
                                         (lambda (exponent)
                                          (if (= 0 exponent)
                                           1
                                           (* base ((exp base) (- exponent 1))))))))
                          ((exp 5) 3)))
        .unwrap();

        let (
            IO {
                expr: result_expr,
                env: _new_env,
                cont: _continuation,
            },
            iterations,
            _emitted,
        ) = Evaluator::new(expr, empty_sym_env(&s_), &mut s_, limit)
            .eval()
            .unwrap();

        assert_eq!(91, iterations);
        assert_eq!(s_.num(125), result_expr);
    }

    #[test]
    fn outer_evaluate_lambda() {
        let_store!();

        let limit = 20;
        let val = s_.num(123);
        let expr = lurk!(((lambda (x) x) 123)).unwrap();

        let (
            IO {
                expr: result_expr,
                env: _new_env,
                cont: _continuation,
            },
            iterations,
            _emitted,
        ) = Evaluator::new(expr, empty_sym_env(&s_), &mut s_, limit)
            .eval()
            .unwrap();

        assert_eq!(4, iterations);
        assert_eq!(val, result_expr);
    }
}
