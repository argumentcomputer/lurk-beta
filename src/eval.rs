use crate::data::{Expression, Store};

// TODO: Unify this with Expression::Cont. For simplicity, keep separate for now.
#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
enum Continuation {
    Outermost,
    Simple(Box<Continuation>),
    Call(Expression),  // The unevaluated argument
    Call2(Expression), // The function
    Error,
    Lookup(Expression), // The saved env
    Binop(Expression),  // Unevaluated arguments
    Binop2(Expression), // The first argument
    Relop(Expression),  // Unevaluated arguments
    Relop2(Expression), //The first argument
    If(Expression),     //Unevaluated arguments
}

fn eval_expr(
    expr: Expression,
    env: Expression,
    cont: Continuation,
    store: &mut Store,
) -> (Expression, Expression, Continuation, Store) {
    match &expr {
        Expression::Nil => invoke_continuation(cont, store.intern("T"), env),
        Expression::Sym(_) if expr == store.intern("T") => invoke_continuation(cont, expr, env),
        Expression::Num(_) => invoke_continuation(cont, expr, env),
        Expression::Fun() => invoke_continuation(cont, expr, env),
        _ => unimplemented!(),
    }
}

fn invoke_continuation(
    cont: Continuation,
    expr: Expression,
    env: Expression,
) -> (Expression, Expression, Continuation, Store) {
    unimplemented!();
}

fn outer_evaluate(
    expr: Expression,
    env: Expression,
    store: Store,
    limit: usize,
) -> (Expression, Expression, Store, usize, Continuation) {
    let mut next_cont = Continuation::Outermost;
    let mut next_expr = expr;
    let mut next_env = env;
    let mut next_store = store;

    for i in 0..limit {
        let (new_expr, new_env, new_cont, new_store) =
            eval_expr(next_expr, next_env, next_cont, &mut next_store);

        match &new_cont {
            Outermost => return (new_expr, new_env, new_store, i, new_cont),
            Error => panic!("Error when evaluating."), // FIXME: handle better.
        }

        next_expr = new_expr;
        next_cont = new_cont;
        next_env = new_env;
        next_store = new_store;
    }

    (next_expr, next_env, next_store, limit, next_cont)
}

#[cfg(test)]
mod test {
    #[test]
    fn test_eval_expr() {}
}
