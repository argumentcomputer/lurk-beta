use crate::data::{Expression, Store, Tag, Tagged};

// TODO: Unify this with Expression::Cont. For simplicity, keep separate for now.
#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
enum Continuation {
    Outermost,
    Simple(Box<Continuation>),
    Call(Expression),  // The unevaluated argument
    Call2(Expression), // The function
    Error,
    Lookup(Expression, Box<Continuation>), // The saved env
    Binop(Expression),                     // Unevaluated arguments
    Binop2(Expression),                    // The first argument
    Relop(Expression),                     // Unevaluated arguments
    Relop2(Expression),                    //The first argument
    If(Expression),                        //Unevaluated arguments
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
        Expression::Fun() => invoke_continuation(cont, expr, env, store),
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
        Expression::Cons(car, cdr) => {
            todo!();
        }
        Expression::Cont() => panic!("Cannot evaluate a continuation: {}"),
    }
}

fn invoke_continuation(
    cont: &Continuation,
    expr: &Expression,
    env: &Expression,
    store: &Store,
) -> (Expression, Expression, Continuation) {
    match &cont {
        Continuation::Outermost => (expr.clone(), env.clone(), cont.clone()),
        Continuation::Lookup(saved_env, continuation) => {
            (expr.clone(), saved_env.clone(), (*continuation.clone()))
        }
        _ => todo!(),
    }
}

fn outer_evaluate(
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

fn empty_sym_env(store: &Store) -> Expression {
    Expression::Nil
}

fn extend(env: &Expression, var: &Expression, val: &Expression, store: &mut Store) -> Expression {
    let cons = store.cons(var, val);
    dbg!(&cons, &cons.tagged_hash(), &store.fetch(cons.tagged_hash()));
    store.cons(&cons, env)
}

fn lookup(env: &Expression, var: &Expression, store: &Store) -> Expression {
    assert_eq!(Tag::Sym, var.tag());
    dbg!("lookup", &var, &env);
    match &*env {
        Expression::Nil => Expression::Nil,
        Expression::Cons(_, _) => {
            let (binding, smaller_env) = store.car_cdr(&env);
            let (v, val) = store.car_cdr(&binding);
            dbg!(&binding, &v, &var);
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

        dbg!(&store, &env, &var, &val);
        assert_eq!(Expression::Nil, lookup(&env, &var, &store));

        let new_env = extend(&env, &var, &val, &mut store);
        dbg!(&store, &new_env);
        assert_eq!(val, lookup(&new_env, &var, &store));
    }

    #[test]
    fn test_eval_expr_simple() {
        let mut store = Store::default();

        {
            let num = Expression::num(123);
            let (result, new_env, cont) = eval_expr(
                &num,
                &empty_sym_env(&store),
                &Continuation::Outermost,
                &mut store,
            );
            assert_eq!(num, result);
        }

        {
            let (result, new_env, cont) = eval_expr(
                &Expression::Nil,
                &empty_sym_env(&store),
                &Continuation::Outermost,
                &mut store,
            );
            assert_eq!(Expression::Nil, result);
        }
    }

    #[test]
    fn test_outer_evaluate_simple() {
        let mut store = Store::default();

        let limit = 20;
        let val = Expression::num(999);
        let (result_expr, new_env, iterations, continuation) =
            outer_evaluate(val.clone(), empty_sym_env(&store), &mut store, limit);

        assert_eq!(1, iterations);
        assert_eq!(&result_expr, &val);
    }

    #[test]
    fn test_outer_evaluate_lookup() {
        let mut store = Store::default();

        let limit = 20;
        let val = Expression::num(999);
        let var = store.intern("apple");
        let val2 = Expression::num(888);
        let var2 = store.intern("banana");
        let env = extend(&empty_sym_env(&store), &var, &val, &mut store);

        {
            let (result_expr, new_env, iterations, continuation) =
                outer_evaluate(var.clone(), env.clone(), &mut store, limit);

            assert_eq!(1, iterations);
            assert_eq!(&result_expr, &val);
        }
        {
            let env2 = extend(&env, &var2, &val2, &mut store);
            let (result_expr, new_env, iterations, continuation) =
                outer_evaluate(var, env2, &mut store, limit);

            assert_eq!(2, iterations);
            assert_eq!(&result_expr, &val);
        }
    }
}
