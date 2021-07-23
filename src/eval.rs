use crate::data::{Expression, Store, Tag, Tagged};
use ff::Field;

// TODO: Unify this with Expression::Cont. For simplicity, keep separate for now.
#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum Continuation {
    Outermost,
    Simple(Box<Continuation>),
    Call(Expression, Box<Continuation>), // The unevaluated argument
    Call2(Expression, Box<Continuation>), // The function
    Error,
    Lookup(Expression, Box<Continuation>),      // The saved env
    Binop(Op2, Expression, Box<Continuation>),  // Unevaluated arguments
    Binop2(Op2, Expression, Box<Continuation>), // The first argument
    Relop(Rel2, Expression, Box<Continuation>), // Unevaluated arguments
    Relop2(Rel2, Expression, Box<Continuation>), //The first argument
    If(Expression, Box<Continuation>),          //Unevaluated arguments
}

#[allow(dead_code)]
struct Function {
    arg: Expression,
    body: Expression,
    closed_env: Expression,
}

#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum Op2 {
    Sum,
    Diff,
    Product,
    Quotient,
}

#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum Rel2 {
    Equal,
}

fn eval_expr(
    expr: &Expression,
    env: &Expression,
    cont: &Continuation,
    store: &mut Store,
) -> (Expression, Expression, Continuation) {
    match expr {
        Expression::Nil => invoke_continuation(cont, expr, env, store),
        Expression::Num(_) => invoke_continuation(cont, expr, env, store),
        Expression::Fun(_, _) => invoke_continuation(cont, expr, env, store),
        Expression::Sym(_) if expr == &store.intern("T") => {
            invoke_continuation(cont, expr, env, store)
        }
        Expression::Sym(_) => {
            let (binding, smaller_env) = store.car_cdr(&env);
            let (v, val) = store.car_cdr(&binding);
            if v == *expr {
                invoke_continuation(cont, &val, env, store)
            } else {
                (
                    expr.clone(),
                    smaller_env,
                    Continuation::Lookup(env.clone(), Box::new(cont.clone())),
                )
            }
        }
        Expression::Cons(head_t, rest_t) => {
            let head = store.fetch(*head_t).unwrap();
            let rest = store.fetch(*rest_t).unwrap();

            if rest == Expression::Nil {
                //todo!("maybe implement zero-arg functions");
                (expr.clone(), env.clone(), cont.clone())
            } else if head == Expression::Sym("LAMBDA".to_string()) {
                let (args, body) = store.car_cdr(&rest);
                let (arg, rest) = store.car_cdr(&args);
                assert_eq!(Expression::Nil, rest);
                let function = store.fun(&arg, &body);

                invoke_continuation(cont, &function, env, store)
            } else if head == Expression::Sym("LET".to_string()) {
                let (bindings, body) = store.car_cdr(&rest);
                let (body1, rest_body) = store.car_cdr(&body);
                // Only a single body form allowed for now.
                assert_eq!(Expression::Nil, rest_body);
                if bindings == Expression::Nil {
                    (body, env.clone(), cont.clone())
                } else {
                    let (binding1, rest_bindings) = store.car_cdr(&bindings);
                    let (var, more_vals) = store.car_cdr(&binding1);
                    let (val, end) = store.car_cdr(&more_vals);
                    assert_eq!(Expression::Nil, end);
                    let expanded = if rest_bindings == Expression::Nil {
                        let lambda = store.intern("LAMBDA");
                        let var = store.list(vec![var]);
                        let lambda_form = store.list(vec![lambda, var, body1]);

                        let whole = store.list(vec![lambda_form, val]);
                        whole
                    } else {
                        let lambda = store.intern("LAMBDA");
                        let var = store.list(vec![var]);
                        let letsym = store.intern("LET");
                        let body = store.list(vec![letsym, rest_bindings, body1]);
                        let lambda_form = store.list(vec![lambda, var, body]);

                        let whole = store.list(vec![lambda_form, val]);
                        whole
                    };
                    (
                        expanded,
                        env.clone(),
                        Continuation::Simple(Box::new(cont.clone())),
                    )
                }
            } else if head == Expression::Sym("+".to_string()) {
                let (arg1, more) = store.car_cdr(&rest);
                (
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Sum, more, Box::new(cont.clone())),
                )
            } else if head == Expression::Sym("-".to_string()) {
                let (arg1, more) = store.car_cdr(&rest);
                (
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Diff, more, Box::new(cont.clone())),
                )
            } else if head == Expression::Sym("*".to_string()) {
                let (arg1, more) = store.car_cdr(&rest);
                (
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Product, more, Box::new(cont.clone())),
                )
            } else if head == Expression::Sym("/".to_string()) {
                let (arg1, more) = store.car_cdr(&rest);
                (
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Quotient, more, Box::new(cont.clone())),
                )
            } else if head == Expression::Sym("=".to_string()) {
                let (arg1, more) = store.car_cdr(&rest);
                (
                    arg1,
                    env.clone(),
                    Continuation::Relop(Rel2::Equal, more, Box::new(cont.clone())),
                )
            } else if head == Expression::Sym("IF".to_string()) {
                let (condition, more) = store.car_cdr(&rest);

                (
                    condition,
                    env.clone(),
                    Continuation::If(more, Box::new(cont.clone())),
                )
            } else {
                let fun_form = head;
                let args = rest;
                let (arg, more_args) = store.car_cdr(&args);
                match &more_args {
                    Expression::Nil => (
                        fun_form,
                        env.clone(),
                        Continuation::Call(arg, Box::new(cont.clone())),
                    ),
                    _ => {
                        panic!(
                            "Only one arg supported, but got more args: {}",
                            store.print_expr(&more_args)
                        );
                    }
                }
            }

            // todo!("bottom of cons eval");
        }
        Expression::Cont() => panic!("Cannot evaluate a continuation."),
    }
}

fn maybe_wrap_continuation(cont: Continuation) -> Continuation {
    match cont {
        Continuation::Outermost => Continuation::Simple(Box::new(cont)),
        _ => cont,
    }
}

fn invoke_continuation(
    cont: &Continuation,
    expr: &Expression,
    env: &Expression,
    store: &mut Store,
) -> (Expression, Expression, Continuation) {
    match &cont {
        Continuation::Outermost => (expr.clone(), env.clone(), cont.clone()),
        Continuation::Simple(continuation) => (expr.clone(), env.clone(), *continuation.clone()),
        Continuation::Lookup(saved_env, continuation) => {
            (expr.clone(), saved_env.clone(), (*continuation.clone()))
        }
        Continuation::Call(arg, continuation) => match expr.tag() {
            Tag::Fun => {
                let function = expr;
                let next_expr = arg;
                let newer_cont = Continuation::Call2(
                    function.clone(),
                    Box::new(maybe_wrap_continuation(*continuation.clone())),
                );
                (next_expr.clone(), env.clone(), newer_cont)
            }
            _ => {
                panic!("call expects a function: {}", store.print_expr(&expr));
            }
        },
        Continuation::Call2(function, continuation) => match function {
            Expression::Fun(arg_t, body) => {
                let body_t = store.fetch(*body).unwrap();
                let next_expr = store.car(&body_t);
                let arg = store.fetch(*arg_t).unwrap();
                let newer_env = extend(env, &arg, expr, store);
                (next_expr, newer_env, *continuation.clone())
            }
            _ => {
                panic!("Call2 continuation contains a non-function: {:?}", function);
            }
        },
        Continuation::Binop(op2, more_args, continuation) => {
            let (arg2, rest) = store.car_cdr(&more_args);
            assert_eq!(Expression::Nil, rest);
            (
                arg2,
                env.clone(),
                Continuation::Binop2(op2.clone(), expr.clone(), continuation.clone()),
            )
        }
        Continuation::Binop2(op2, arg1, continuation) => {
            let arg2 = expr;
            match (arg1, arg2) {
                (Expression::Num(a), Expression::Num(b)) => match op2 {
                    Op2::Sum => {
                        let mut tmp = a.clone();
                        tmp.add_assign(b);
                        (Expression::Num(tmp), env.clone(), (*continuation.clone()))
                    }
                    Op2::Diff => {
                        let mut tmp = a.clone();
                        tmp.sub_assign(b);
                        (Expression::Num(tmp), env.clone(), (*continuation.clone()))
                    }
                    Op2::Product => {
                        let mut tmp = a.clone();
                        tmp.mul_assign(b);
                        (Expression::Num(tmp), env.clone(), (*continuation.clone()))
                    }
                    Op2::Quotient => {
                        let mut tmp = a.clone();
                        // TODO: Return error continuation.
                        assert!(!b.is_zero(), "Division by zero error.");
                        tmp.mul_assign(&b.inverse().unwrap());
                        (Expression::Num(tmp), env.clone(), (*continuation.clone()))
                    }
                },
                _ => unimplemented!("Binop2"),
            }
        }
        Continuation::Relop(rel2, more_args, continuation) => {
            let (arg2, rest) = store.car_cdr(&more_args);
            assert_eq!(Expression::Nil, rest);
            (
                arg2,
                env.clone(),
                Continuation::Relop2(rel2.clone(), expr.clone(), continuation.clone()),
            )
        }
        Continuation::Relop2(rel2, arg1, continuation) => {
            let arg2 = expr;
            match (arg1, arg2) {
                (Expression::Num(a), Expression::Num(b)) => match rel2 {
                    Rel2::Equal => {
                        let result = if a == b {
                            Expression::Sym("T".to_string()) // TODO: maybe explicit boolean.
                        } else {
                            Expression::Nil
                        };
                        (result, env.clone(), (*continuation.clone()))
                    }
                },
                _ => unimplemented!("Relop2"),
            }
        }
        Continuation::If(more_args, continuation) => {
            let condition = expr;
            let (arg1, more) = store.car_cdr(more_args);
            // NOTE: as formulated here, IF operates on any condition. Every
            // value but NIL is considered true.
            //
            // We can implement this in constraints:
            // X * (1-X) = 0
            // C * X = 0
            // (X + C) * Q = 1
            //
            // where X is a constrained boolean which is true (1) iff C == 0. Q
            // is a value non-deterministically supplied by the prover to
            // demonstrate that both X and C are not 0. If both were 0, the
            // constraint C * X = 0 would hold. But in that case, X should be 1
            // since C = 0.
            //
            // Now X can be used as the known-boolean conditional in a
            // conditional selection: (B - A) * X = B - C
            //
            // where C is the result, A is the 'true' result, and B is the
            // false/else result. i.e. if X then A else B.
            //
            // All of the above is just 'how to implement an exact equality
            // check' in the case that the value checked against is zero. We
            // will need this throughout, when branching on symbols (effectively
            // a CASE expression). Since symbols are field elements with
            // equality, this is relatively efficient. When doing this, the
            // value being checked against is not zero, so that value should
            // first be subtracted from the value being checked.

            if *condition == Expression::Nil {
                let (arg2, end) = store.car_cdr(&more);
                assert_eq!(end, Expression::Nil);
                (arg2, env.clone(), (*continuation.clone()))
            } else {
                (arg1, env.clone(), (*continuation.clone()))
            }
        }
        _ => {
            todo!("Unhandled Continuation variant.")
        }
    }
}

pub fn outer_evaluate(
    expr: Expression,
    env: Expression,
    mut store: &mut Store,
    limit: usize,
) -> (Expression, Expression, usize, Continuation) {
    let mut next_cont = Continuation::Outermost;
    let mut next_expr = expr;
    let mut next_env = env;

    for i in 1..=limit {
        let (new_expr, new_env, new_cont) =
            eval_expr(&next_expr, &next_env, &next_cont, &mut store);

        match &new_cont {
            Continuation::Outermost => return (new_expr, new_env, i, new_cont),
            Continuation::Error => panic!("Error when evaluating."), // FIXME: handle better.
            _ => (),
        }

        next_expr = new_expr;
        next_cont = new_cont;
        next_env = new_env;
    }

    (next_expr.clone(), next_env, limit, next_cont)
}

pub fn empty_sym_env(_store: &Store) -> Expression {
    Expression::Nil
}

fn extend(env: &Expression, var: &Expression, val: &Expression, store: &mut Store) -> Expression {
    let cons = store.cons(var, val);
    store.cons(&cons, env)
}

#[allow(dead_code)]
fn lookup(env: &Expression, var: &Expression, store: &Store) -> Expression {
    assert_eq!(Tag::Sym, var.tag());
    match &*env {
        Expression::Nil => Expression::Nil,
        Expression::Cons(_, _) => {
            let (binding, smaller_env) = store.car_cdr(&env);
            let (v, val) = store.car_cdr(&binding);
            if v == *var {
                val
            } else {
                lookup(&smaller_env, var, store)
            }
        }
        _ => panic!("Env must be a list."),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lookup() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let var = store.intern("variable");
        let val = Expression::num(123);

        assert_eq!(Expression::Nil, lookup(&env, &var, &store));

        let new_env = extend(&env, &var, &val, &mut store);
        assert_eq!(val, lookup(&new_env, &var, &store));
    }

    #[test]
    fn test_eval_expr_simple() {
        let mut store = Store::default();

        {
            let num = Expression::num(123);
            let (result, _new_env, _cont) = eval_expr(
                &num,
                &empty_sym_env(&store),
                &Continuation::Outermost,
                &mut store,
            );
            assert_eq!(num, result);
        }

        {
            let (result, _new_env, _cont) = eval_expr(
                &Expression::Nil,
                &empty_sym_env(&store),
                &Continuation::Outermost,
                &mut store,
            );
            assert_eq!(Expression::Nil, result);
        }
    }

    #[test]
    fn outer_evaluate_simple() {
        let mut store = Store::default();

        let limit = 20;
        let val = Expression::num(999);
        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(val.clone(), empty_sym_env(&store), &mut store, limit);

        assert_eq!(1, iterations);
        assert_eq!(&result_expr, &val);
    }

    #[test]
    fn outer_evaluate_lookup() {
        let mut store = Store::default();

        let limit = 20;
        let val = Expression::num(999);
        let var = store.intern("apple");
        let val2 = Expression::num(888);
        let var2 = store.intern("banana");
        let env = extend(&empty_sym_env(&store), &var, &val, &mut store);

        {
            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(var.clone(), env.clone(), &mut store, limit);

            assert_eq!(1, iterations);
            assert_eq!(&result_expr, &val);
        }
        {
            let env2 = extend(&env, &var2, &val2, &mut store);
            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(var, env2, &mut store, limit);

            assert_eq!(2, iterations);
            assert_eq!(&result_expr, &val);
        }
    }

    #[test]
    fn print_expr() {
        let mut s = Store::default();
        let nil = Expression::Nil;
        let x = s.intern("x");
        let lambda = s.intern("lambda");
        let val = Expression::num(123);
        let lambda_args = s.cons(&x, &nil);
        let body = s.cons(&x, &nil);
        let rest = s.cons(&lambda_args, &body);
        let whole_lambda = s.cons(&lambda, &rest);
        let lambda_arguments = s.cons(&val, &nil);
        let expr = s.cons(&whole_lambda, &lambda_arguments);

        assert_eq!("((LAMBDA . ((X) . (X))) . (Fr(0x000000000000000000000000000000000000000000000000000000000000007b)))".to_string(), s.print_expr(&expr));
    }

    #[test]
    fn outer_evaluate_lambda() {
        let mut s = Store::default();
        let limit = 20;
        let val = Expression::num(123);
        let expr = s.read("((lambda (x) x) 123)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(4, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_lambda2() {
        let mut s = Store::default();
        let limit = 20;
        let val = Expression::num(123);
        let expr = s.read("((lambda (y) ((lambda (x) y) 321)) 123)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(9, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_lambda3() {
        let mut s = Store::default();
        let limit = 20;
        let val = Expression::num(123);
        let expr = s
            .read("((lambda (y) ((lambda (x) ((lambda (z) z) x)) y)) 123)")
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(10, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_lambda4() {
        let mut s = Store::default();
        let limit = 20;
        let _val = Expression::num(999);
        let val2 = Expression::num(888);
        let expr = s
            // NOTE: We pass two different values. This tests which is returned.
            .read("((lambda (y) ((lambda (x) ((lambda (z) z) x)) 888)) 999)")
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(10, iterations);
        assert_eq!(val2, result_expr);
    }

    #[test]
    fn outer_evaluate_lambda5() {
        let mut s = Store::default();
        let limit = 20;
        let val = Expression::num(999);
        let expr = s
            // Bind a function to the name FN, then call it.
            .read("(((lambda (fn) (lambda (x) (fn x))) (lambda (y) y)) 999)")
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(12, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_sum() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(+ 2 (+ 3 4))").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(6, iterations);
        assert_eq!(Expression::num(9), result_expr);
    }

    #[test]
    fn outer_evaluate_diff() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(- 9 5)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(3, iterations);
        assert_eq!(Expression::num(4), result_expr);
    }

    #[test]
    fn outer_evaluate_product() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(* 9 5)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(3, iterations);
        assert_eq!(Expression::num(45), result_expr);
    }

    #[test]
    fn outer_evaluate_quotient() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(/ 21 7)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(3, iterations);
        assert_eq!(Expression::num(3), result_expr);
    }

    #[test]
    #[should_panic]
    // This shouldn't actually panic, it should return an error continuation.
    // But for now document the handling.
    fn outer_evaluate_quotient_divide_by_zero() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(/ 21 0)").unwrap();

        let (_result_expr, _new_env, _iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
    }

    #[test]
    fn outer_evaluate_num_equal() {
        let mut s = Store::default();
        let limit = 20;

        {
            let expr = s.read("(= 5 5)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(3, iterations);
            // TODO: Consider special-casing T, like NIL, and force it to the
            // immediate value 1 (with Symbol type-tag). That way boolean logic
            // will work out. It might be more consistent to have an explicit
            // boolean type (like Scheme), though. Otherwise we will have to
            // think about handling of symbol names (if made explicit), since
            // neither T/NIL as 1/0 will *not* be hashes of their symbol names.
            assert_eq!(Expression::Sym("T".to_string()), result_expr);
        }
        {
            let expr = s.read("(= 5 6)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(3, iterations);
            assert_eq!(Expression::Nil, result_expr);
        }
    }

    #[test]
    fn outer_evaluate_adder() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(((lambda (x) (lambda (y) (+ x y))) 2) 3)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(12, iterations);
        assert_eq!(Expression::num(5), result_expr);
    }

    // Enable this when we have LET.
    #[test]
    fn outer_evaluate_adder2() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s
            .read(
                "(let ((make-adder (lambda (x) (lambda (y) (+ x y)))))
                              ((make-adder 2) 3))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(16, iterations);
        assert_eq!(Expression::num(5), result_expr);
    }

    #[test]
    fn outer_evaluate_let_simple() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(let ((a 1)) a)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(5, iterations);
        assert_eq!(Expression::num(1), result_expr);
    }

    #[test]
    fn outer_evaluate_let() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s
            .read(
                "(let ((a 1)
                       (b 2))
                   (+ a b))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(15, iterations);
        assert_eq!(Expression::num(3), result_expr);
    }

    #[test]
    fn outer_evaluate_arithmetic_let() {
        let mut s = Store::default();
        let limit = 30;
        let expr = s
            .read(
                "(let ((a 1)
                       (b 2)
                       (c 3))
                   (+ a (+ b c)))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(27, iterations);
        assert_eq!(Expression::num(6), result_expr);
    }

    #[test]
    // Not because it's efficient, but to prove we can.
    fn outer_evaluate_fundamental_conditional() {
        let mut s = Store::default();
        let limit = 100;
        let expr = s
            .read(
                "(let ((true (lambda (a)
                               (lambda (b)
                                 a)))
                        (false (lambda (a)
                                 (lambda (b)
                                   b)))
                        (iff (lambda (a)
                               (lambda (b)
                                 (lambda (cond)
                                   ((cond a) b))))))
                   (((iff 5) 6) true))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(48, iterations);
        assert_eq!(Expression::num(5), result_expr);
    }

    #[test]
    fn outer_evaluate_if() {
        let mut s = Store::default();
        let limit = 100;
        let expr = s.read("(if t 5 6)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(2, iterations);
        assert_eq!(Expression::num(5), result_expr);
    }

    #[test]
    fn outer_evaluate_recursion() {
        let mut s = Store::default();
        let limit = 300;
        let expr = s
            .read(
                "(let ((exp (lambda (base)
                              (lambda (exponent)
                                (if (= 0 exponent)
                                    1
                                    (* base ((exp base) (- exponent 1))))))))
                   ((exp 5) 3))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(109, iterations);
        assert_eq!(Expression::num(125), result_expr);
    }
}
