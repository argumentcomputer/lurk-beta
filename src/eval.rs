use crate::data::{Continuation, Expression, Op1, Op2, Rel2, Store, Tag, Tagged, Thunk};
use ff::Field;
use std::cmp::PartialEq;
use std::iter::Iterator;
use std::ops::{AddAssign, MulAssign, SubAssign};

#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub struct IO {
    pub expr: Expression,
    pub env: Expression,
    pub cont: Continuation, // This could be an Expression too, if we want Continuations to be first class.
}

#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub struct Frame<T, W> {
    pub input: Option<T>,
    pub output: Option<T>,
    pub initial: Option<T>,
    pub i: Option<usize>,
    pub witness: Option<W>,
}

pub trait Evaluable<W> {
    fn eval(&self, store: &mut Store) -> (Self, W)
    where
        Self: Sized;

    fn is_terminal(&self) -> bool;
}

impl Evaluable<Witness> for IO {
    fn eval(&self, store: &mut Store) -> (Self, Witness) {
        let (new_expr, new_env, new_cont, witness) =
            eval_expr(&self.expr, &self.env, &self.cont, store);

        (
            Self {
                expr: new_expr,
                env: new_env,
                cont: new_cont,
            },
            witness,
        )
    }

    fn is_terminal(&self) -> bool {
        matches!(self.cont, Continuation::Error | Continuation::Terminal)
    }
}

impl<T: Evaluable<Witness> + Clone + PartialEq> Frame<T, Witness> {
    fn next(&self, store: &mut Store) -> Self {
        let mut input = self.output.clone();

        if let Some((output, witness)) = input.clone().map(|i| i.eval(store)) {
            let i = self.i.map(|i| i + 1);
            Self {
                input,
                output: Some(output),
                initial: self.initial.clone(),
                i,
                witness: Some(witness),
            }
        } else {
            panic!("Frame has no output, so cannot produce next().");
        }
    }
}

impl<T: Evaluable<Witness> + Clone + PartialEq> Frame<T, Witness> {
    fn from_initial_input(input: T, store: &mut Store) -> Self {
        let (output, witness) = input.eval(store);

        Self {
            input: Some(input.clone()),
            output: Some(output),
            initial: Some(input.clone()),
            i: Some(0),
            witness: Some(witness),
        }
    }
}

struct FrameIt<'a, T, W> {
    initial_input: T,
    frame: Option<Frame<T, W>>,
    store: &'a mut Store,
}

impl<'a, T, W> FrameIt<'a, T, W> {
    fn new(initial_input: T, store: &'a mut Store) -> Self {
        Self {
            initial_input,
            frame: None,
            store,
        }
    }
}

impl<'a, T: Evaluable<Witness> + Clone + PartialEq> Iterator for FrameIt<'a, T, Witness> {
    type Item = Frame<T, Witness>;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if let Some(next_frame) = if let Some(frame) = &self.frame {
            if frame.output.as_ref().unwrap().is_terminal() {
                None
            } else {
                Some(frame.next(self.store))
            }
        } else {
            Some(Frame::from_initial_input(
                self.initial_input.clone(),
                self.store,
            ))
        } {
            self.frame = Some(next_frame);
            self.frame.clone()
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Witness {
    // TODO: Many of these fields ended up not being used.
    // once circuit is done, remove the excess.
    pub store: Option<Store>,
    pub prethunk_output_expr: Option<Expression>,
    pub prethunk_output_env: Option<Expression>,
    pub prethunk_output_cont: Option<Continuation>,
    pub destructured_thunk: Option<Thunk>,
    pub extended_closure: Option<Expression>,
    pub make_thunk_cont: Option<Continuation>,
    pub make_thunk_tail_continuation_cont: Option<Continuation>,
    pub invoke_continuation_cont: Option<Continuation>,

    pub invoke_continuation_output_result: Option<Expression>,
}

impl Witness {
    fn witness_destructured_thunk(&mut self, thunk: &Thunk) {
        assert!(
            !self.destructured_thunk.is_some(),
            "Only one thunk should be destructured per evaluation step."
        );
        self.destructured_thunk = Some(thunk.clone());
    }
}

fn eval_expr(
    expr: &Expression,
    env: &Expression,
    cont: &Continuation,
    store: &mut Store,
) -> (Expression, Expression, Continuation, Witness) {
    let mut witness = Witness::default();

    let (new_expr, new_env, new_cont) =
        eval_expr_with_witness(expr, env, cont, store, &mut witness).results();

    (new_expr, new_env, new_cont, witness)
}

pub enum Control<Expr, Cont> {
    Return(Expr, Expr, Cont),
    MakeThunk(Expr, Expr, Cont),
    InvokeContinuation(Expr, Expr, Cont),
}

impl<E: Clone, C: Clone> Control<E, C> {
    pub fn results(&self) -> (E, E, C) {
        match self {
            Self::Return(expr, env, cont) => (expr.clone(), env.clone(), cont.clone()),
            Self::MakeThunk(expr, env, cont) => (expr.clone(), env.clone(), cont.clone()),
            Self::InvokeContinuation(expr, env, cont) => (expr.clone(), env.clone(), cont.clone()),
        }
    }

    pub fn is_return(&self) -> bool {
        matches!(self, Self::Return(_, _, _))
    }
    pub fn is_make_thunk(&self) -> bool {
        matches!(self, Self::MakeThunk(_, _, _))
    }
    pub fn is_invoke_continuation(&self) -> bool {
        matches!(self, Self::InvokeContinuation(_, _, _))
    }
}

fn eval_expr_with_witness(
    expr: &Expression,
    env: &Expression,
    cont: &Continuation,
    store: &mut Store,
    witness: &mut Witness,
) -> Control<Expression, Continuation> {
    witness.store = Some(store.clone());
    let control = match expr {
        Expression::Thunk(thunk) => Control::InvokeContinuation(
            *thunk.value.clone(),
            env.clone(),
            *thunk.continuation.clone(),
        ),
        Expression::Nil => Control::MakeThunk(expr.clone(), env.clone(), cont.clone()),
        Expression::Sym(_) => {
            if expr == &store.intern("NIL") || (expr == &store.intern("T")) {
                // CIRCUIT: sym_is_self_evaluating
                Control::MakeThunk(expr.clone(), env.clone(), cont.clone())
            } else {
                // CIRCUIT: sym_otherwise
                assert!(Expression::Nil != *env, "Unbound variable: {:?}", expr);
                let (binding, smaller_env) = store.car_cdr(env);
                if binding == Expression::Nil {
                    // CIRCUIT: binding_is_nil
                    //          otherwise_and_binding_is_nil
                    Control::Return(expr.clone(), env.clone(), Continuation::Error)
                } else {
                    // CIRCUIT: binding_not_nil
                    let (var_or_rec_binding, val_or_more_rec_env) = store.car_cdr(&binding);
                    match &var_or_rec_binding {
                        // In a simple_env.
                        Expression::Sym(_) => {
                            // CIRCUIT: var_or_rec_binding_is_sym
                            let v = var_or_rec_binding;
                            let val = val_or_more_rec_env;

                            if v == *expr {
                                // CIRCUIT: v_is_expr1
                                //          v_is_expr1_real
                                Control::MakeThunk(val, env.clone(), cont.clone())
                            } else {
                                // CIRCUIT: otherwise_and_v_not_expr

                                match cont {
                                    Continuation::Lookup(_, _) => {
                                        // CIRCUIT: cont_is_lookup
                                        //          cont_is_lookup_real
                                        //          cont_is_lookup_sym
                                        Control::Return(expr.clone(), smaller_env, cont.clone())
                                    }
                                    _ =>
                                    // CIRCUIT: cont_not_lookup_real
                                    {
                                        Control::Return(
                                            expr.clone(),
                                            smaller_env,
                                            Continuation::Lookup(
                                                env.clone(),
                                                Box::new(cont.clone()),
                                            ),
                                        )
                                    }
                                }
                            }
                        }
                        // Start of a recursive_env.
                        Expression::Cons(_, _) => {
                            // CIRCUIT: var_or_rec_binding_is_cons
                            let rec_env = binding;
                            let smaller_rec_env = val_or_more_rec_env;

                            let (v2, val2) = store.car_cdr(&var_or_rec_binding);
                            if v2 == *expr {
                                // CIRCUIT: v2_is_expr
                                //          v2_is_expr_real
                                let val_to_use = {
                                    // CIRCUIT: val_to_use
                                    //          val_to_use_real
                                    match val2 {
                                        Expression::Fun(_, _, _) => {
                                            witness.extended_closure = Some(val2.clone());
                                            // CIRCUIT: val2_is_fun

                                            // We just found a closure in a recursive env.
                                            // We need to extend its environment to include that recursive env.

                                            extend_closure(&val2, &rec_env, store)
                                        }
                                        _ => {
                                            witness.extended_closure = None;
                                            val2
                                        }
                                    }
                                };
                                Control::MakeThunk(val_to_use, env.clone(), cont.clone())
                            } else {
                                // CIRCUIT: otherwise_and_v2_not_expr
                                // CIRCUIT: env_to_use
                                let env_to_use = if smaller_rec_env == Expression::Nil {
                                    smaller_env
                                } else {
                                    // CIRCUIT: with_smaller_rec_env
                                    store.cons(&smaller_rec_env, &smaller_env)
                                };
                                match cont {
                                    Continuation::Lookup(_, _) => {
                                        // CIRCUIT: continuation_is_lookup (indicates this branch)
                                        Control::Return(expr.clone(), env_to_use, cont.clone())
                                    }
                                    _ => Control::Return(
                                        expr.clone(),
                                        env_to_use,
                                        Continuation::Lookup(env.clone(), Box::new(cont.clone())),
                                    ),
                                }
                            }
                        }
                        _ => panic!("Bad form."),
                    }
                }
            }
        }
        Expression::Str(_) => unimplemented!(),
        Expression::Num(_) => Control::MakeThunk(expr.clone(), env.clone(), cont.clone()),
        Expression::Fun(_, _, _) => Control::MakeThunk(expr.clone(), env.clone(), cont.clone()),
        Expression::Cons(head_t, rest_t) => {
            let head = store.fetch(head_t).unwrap();
            let rest = store.fetch(rest_t).unwrap();
            let lambda = store.intern("LAMBDA");
            let quote = store.intern("QUOTE");
            let dummy_arg = store.intern("_");

            if head == lambda {
                let (args, body) = store.car_cdr(&rest);
                let (arg, _rest) = if args == Expression::Nil {
                    // (LAMBDA () STUFF)
                    // becomes (LAMBDA (DUMMY) STUFF)
                    (dummy_arg, Expression::Nil)
                } else {
                    store.car_cdr(&args)
                };
                let cdr_args = store.cdr(&args);
                let inner_body = if cdr_args == Expression::Nil {
                    body
                } else {
                    // (LAMBDA (A B) STUFF)
                    // becomes (LAMBDA (A) (LAMBDA (B) STUFF))
                    let inner = store.cons(&cdr_args, &body);
                    let l = store.cons(&lambda, &inner);
                    store.list(vec![l])
                };
                let function = store.fun(&arg, &inner_body, env);

                Control::MakeThunk(function, env.clone(), cont.clone())
            } else if head == quote {
                let (quoted, end) = store.car_cdr(&rest);
                assert_eq!(Expression::Nil, end);
                Control::MakeThunk(quoted, env.clone(), cont.clone())
            } else if head == Expression::Sym("LET*".to_string()) {
                let (bindings, body) = store.car_cdr(&rest);
                let (body1, rest_body) = store.car_cdr(&body);
                // Only a single body form allowed for now.
                assert_eq!(Expression::Nil, rest_body);
                if bindings == Expression::Nil {
                    Control::Return(body1, env.clone(), cont.clone())
                } else {
                    let (binding1, rest_bindings) = store.car_cdr(&bindings);
                    let (var, more_vals) = store.car_cdr(&binding1);
                    let (val, end) = store.car_cdr(&more_vals);
                    assert_eq!(Expression::Nil, end);

                    let expanded = if rest_bindings == Expression::Nil {
                        body1
                    } else {
                        let lt = store.intern("LET*");
                        store.list(vec![lt, rest_bindings, body1])
                    };
                    Control::Return(
                        val,
                        env.clone(),
                        Continuation::LetStar(var, expanded, env.clone(), Box::new(cont.clone())),
                    )
                }
            } else if head == store.intern("LETREC*") {
                let (bindings, body) = store.car_cdr(&rest);
                let (body1, rest_body) = store.car_cdr(&body);
                // Only a single body form allowed for now.
                assert_eq!(Expression::Nil, rest_body);
                if bindings == Expression::Nil {
                    Control::Return(body1, env.clone(), cont.clone())
                } else {
                    let (binding1, rest_bindings) = store.car_cdr(&bindings);
                    let (var, more_vals) = store.car_cdr(&binding1);
                    let (val, end) = store.car_cdr(&more_vals);
                    assert_eq!(Expression::Nil, end);

                    let expanded = if rest_bindings == Expression::Nil {
                        body1
                    } else {
                        let lt = store.intern("LETREC*");
                        store.list(vec![lt, rest_bindings, body1])
                    };
                    Control::Return(
                        val,
                        env.clone(),
                        Continuation::LetRecStar(
                            var,
                            expanded,
                            env.clone(),
                            Box::new(cont.clone()),
                        ),
                    )
                }
            } else if head == store.intern("cons") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Cons, env.clone(), more, Box::new(cont.clone())),
                )
            } else if head == store.intern("car") {
                let (arg1, end) = store.car_cdr(&rest);
                assert_eq!(Expression::Nil, end);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Unop(Op1::Car, Box::new(cont.clone())),
                )
            } else if head == store.intern("cdr") {
                let (arg1, end) = store.car_cdr(&rest);
                assert_eq!(Expression::Nil, end);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Unop(Op1::Cdr, Box::new(cont.clone())),
                )
            } else if head == store.intern("atom") {
                let (arg1, end) = store.car_cdr(&rest);
                assert_eq!(Expression::Nil, end);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Unop(Op1::Atom, Box::new(cont.clone())),
                )
            } else if head == store.intern("+") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Sum, env.clone(), more, Box::new(cont.clone())),
                )
            } else if head == store.intern("-") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Diff, env.clone(), more, Box::new(cont.clone())),
                )
            } else if head == store.intern("*") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Product, env.clone(), more, Box::new(cont.clone())),
                )
            } else if head == store.intern("/") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Binop(Op2::Quotient, env.clone(), more, Box::new(cont.clone())),
                )
            } else if head == store.intern("=") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Relop(Rel2::NumEqual, env.clone(), more, Box::new(cont.clone())),
                )
            } else if head == store.intern("eq") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env.clone(),
                    Continuation::Relop(Rel2::Equal, env.clone(), more, Box::new(cont.clone())),
                )
            } else if head == store.intern("if") {
                let (condition, more) = store.car_cdr(&rest);
                Control::Return(
                    condition,
                    env.clone(),
                    Continuation::If(more, Box::new(cont.clone())),
                )
            } else if head == store.intern("current-env") {
                assert_eq!(Expression::Nil, rest);
                Control::MakeThunk(env.clone(), env.clone(), cont.clone())
            } else {
                // (fn . args)
                let fun_form = head;
                let args = rest;
                let (arg, more_args) = if args == Expression::Nil {
                    (Expression::Nil, Expression::Nil)
                } else {
                    store.car_cdr(&args)
                };
                match &more_args {
                    // (fn arg)
                    // Interpreting as call.
                    Expression::Nil => Control::Return(
                        fun_form,
                        env.clone(),
                        Continuation::Call(arg, env.clone(), Box::new(cont.clone())),
                    ),
                    _ => {
                        // Interpreting as multi-arg call.
                        // (fn arg . more_args) => ((fn arg) . more_args)
                        let expanded_inner = store.list(vec![fun_form, arg]);
                        let expanded = store.cons(&expanded_inner, &more_args);
                        Control::Return(expanded, env.clone(), cont.clone())
                    }
                }
            }
        }
    };

    {
        let (new_expr, new_env, new_cont) = control.results();

        witness.prethunk_output_expr = Some(new_expr);
        witness.prethunk_output_env = Some(new_env);
        witness.prethunk_output_cont = Some(new_cont);
    }
    let control = invoke_continuation(control, store, witness);
    make_thunk(control, store, witness)
}

fn invoke_continuation(
    control: Control<Expression, Continuation>,
    store: &mut Store,
    witness: &mut Witness,
) -> Control<Expression, Continuation> {
    if !control.is_invoke_continuation() {
        return control;
    }
    let (result, env, cont) = control.results();

    witness.invoke_continuation_cont = Some(cont.clone());

    let control = match &cont {
        Continuation::Terminal => unreachable!("Terminal Continuation should never be invoked."),
        Continuation::Dummy => unreachable!("Dummy Continuation should never be invoked."),
        Continuation::Outermost => match result {
            Expression::Thunk(thunk) => {
                witness.witness_destructured_thunk(&thunk);
                Control::Return(*thunk.value.clone(), env.clone(), Continuation::Terminal)
            }
            _ => Control::Return(result.clone(), env.clone(), Continuation::Terminal),
        },
        Continuation::Call(arg, saved_env, continuation) => match result.tag() {
            Tag::Fun => {
                let function = result;
                let next_expr = arg;
                let newer_cont = Continuation::Call2(
                    function,
                    saved_env.clone(),
                    Box::new(*continuation.clone()),
                );
                Control::Return(next_expr.clone(), env.clone(), newer_cont)
            }
            _ => {
                Control::Return(result.clone(), env.clone(), Continuation::Error)
                // Bad function
            }
        },
        Continuation::Call2(function, saved_env, continuation) => match function {
            Expression::Fun(arg_t, body_t, closed_env_t) => {
                let body = store.fetch(body_t).unwrap();
                let body_form = store.car(&body);
                let closed_env = store.fetch(closed_env_t).unwrap();
                let arg = store.fetch(arg_t).unwrap();
                let newer_env = extend(&closed_env, &arg, &result, store);
                let cont = make_tail_continuation(saved_env, continuation);
                Control::Return(body_form, newer_env, cont)
            }
            _ => {
                Control::Return(result.clone(), env.clone(), Continuation::Error)
                // panic!("Call2 continuation contains a non-function: {:?}", function);
            }
        },
        Continuation::LetStar(var, body, saved_env, continuation) => {
            let extended_env = extend(&env, var, &result, store);
            let c = make_tail_continuation(saved_env, continuation);

            Control::Return(body.clone(), extended_env, c)
        }
        Continuation::LetRecStar(var, body, saved_env, continuation) => {
            let extended_env = extend_rec(&env, var, &result, store);
            let c = make_tail_continuation(saved_env, continuation);

            Control::Return(body.clone(), extended_env, c)
        }
        Continuation::Unop(op1, continuation) => {
            let val = match op1 {
                Op1::Car => store.car(&result),
                Op1::Cdr => store.cdr(&result),
                Op1::Atom => match result.tag() {
                    Tag::Cons => Expression::Nil,
                    _ => store.intern("T"),
                },
            };
            Control::MakeThunk(val, env.clone(), *continuation.clone())
        }
        Continuation::Binop(op2, saved_env, unevaled_args, continuation) => {
            let (arg2, rest) = store.car_cdr(unevaled_args);
            assert_eq!(Expression::Nil, rest);
            Control::Return(
                arg2,
                saved_env.clone(),
                Continuation::Binop2(op2.clone(), result.clone(), continuation.clone()),
            )
        }
        Continuation::Binop2(op2, arg1, continuation) => {
            let arg2 = result;
            let result = match (arg1, &arg2) {
                (Expression::Num(a), Expression::Num(b)) => match op2 {
                    Op2::Sum => {
                        let mut tmp = *a;
                        tmp.add_assign(b);
                        Expression::Num(tmp)
                    }
                    Op2::Diff => {
                        let mut tmp = *a;
                        tmp.sub_assign(b);
                        Expression::Num(tmp)
                    }
                    Op2::Product => {
                        let mut tmp = *a;
                        tmp.mul_assign(b);
                        Expression::Num(tmp)
                    }
                    Op2::Quotient => {
                        let mut tmp = *a;
                        // TODO: Return error continuation.
                        let b_is_zero: bool = b.is_zero().into();
                        assert!(!b_is_zero, "Division by zero error.");
                        tmp.mul_assign(&b.invert().unwrap());
                        Expression::Num(tmp)
                    }
                    Op2::Cons => store.cons(arg1, &arg2),
                },
                _ => match op2 {
                    Op2::Cons => store.cons(arg1, &arg2),
                    _ => unimplemented!("Binop2"),
                },
            };
            Control::MakeThunk(result, env.clone(), *continuation.clone())
        }
        Continuation::Relop(rel2, saved_env, more_args, continuation) => {
            let (arg2, rest) = store.car_cdr(more_args);
            assert_eq!(Expression::Nil, rest);
            Control::Return(
                arg2,
                saved_env.clone(),
                Continuation::Relop2(rel2.clone(), result.clone(), continuation.clone()),
            )
        }
        Continuation::Relop2(rel2, arg1, continuation) => {
            let arg2 = result;
            let result = match (arg1, arg2) {
                (Expression::Num(a), Expression::Num(b)) => match rel2 {
                    Rel2::NumEqual | Rel2::Equal => {
                        if *a == b {
                            store.intern("T") // TODO: maybe explicit boolean.
                        } else {
                            Expression::Nil
                        }
                    }
                },
                (a_expr, b_expr) => match rel2 {
                    Rel2::NumEqual => Expression::Nil, // FIXME: This should be a type error.
                    Rel2::Equal => {
                        if *a_expr == b_expr {
                            store.intern("T")
                        } else {
                            Expression::Nil
                        }
                    }
                },
            };
            Control::MakeThunk(result, env.clone(), *continuation.clone())
        }
        Continuation::If(more_args, continuation) => {
            let condition = result;
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

            if condition == Expression::Nil {
                let (arg2, end) = store.car_cdr(&more);
                assert_eq!(end, Expression::Nil);
                Control::Return(arg2, env.clone(), (*continuation.clone()))
            } else {
                Control::Return(arg1, env.clone(), (*continuation.clone()))
            }
        }
        Continuation::Lookup(saved_env, continuation) => {
            Control::MakeThunk(result.clone(), saved_env.clone(), *continuation.clone())
        }
        Continuation::Simple(continuation) => {
            Control::MakeThunk(result.clone(), env.clone(), *continuation.clone())
        }
        Continuation::Tail(saved_env, continuation) => {
            Control::MakeThunk(result.clone(), saved_env.clone(), *continuation.clone())
        }
        _ => {
            unreachable!();
        }
    };

    let (output_result, output_env, output_cont) = control.results();

    witness.invoke_continuation_output_result = Some(output_result);

    if let Control::InvokeContinuation(_, _, _) = control {
        unreachable!();
    }

    control
}

// Returns (Expression::Thunk, Expression::Env, Continuation)
fn make_thunk(
    control: Control<Expression, Continuation>,
    store: &mut Store,
    witness: &mut Witness,
) -> Control<Expression, Continuation> {
    if !control.is_make_thunk() {
        return control;
    }
    let (result, env, cont) = control.results();

    if let Expression::Thunk(_) = result {
        unreachable!("make_thunk should never be called with a thunk");
    };

    let effective_env = match &cont {
        // These are the restore-env continuations.
        Continuation::Lookup(saved_env, _) => saved_env.clone(),
        Continuation::Tail(saved_env, _) => saved_env.clone(),
        _ => env.clone(),
    };

    // This structure is in case we have other tail continuations in the future.
    // I think we should not have, though -- since by definition we should be able
    // to use Tail for any such need.
    let control = match cont {
        // These are the tail-continuations.
        Continuation::Tail(_, continuation) => {
            witness.make_thunk_tail_continuation_cont = Some(*continuation.clone());
            if let Continuation::Tail(saved_env, previous_cont) = &*continuation {
                let thunk = Thunk {
                    value: Box::new(result),
                    continuation: previous_cont.clone(),
                };
                // witness.make_thunk_tail_continuation_thunk = Some(thunk.clone());
                witness.witness_destructured_thunk(&thunk);
                Control::Return(
                    Expression::Thunk(thunk),
                    saved_env.clone(),
                    Continuation::Dummy,
                )
            } else {
                // There is no risk of a recursive loop here, so the self-call below
                // is just convenience. It can be unrolled in the circuit. That
                // said, it' a pain to deal with in circuit and would probably be
                // easier if it were done here instead, then copied.

                //return make_thunk(continuation, result, effective_env, store, witness);

                // Yes, we are unrolling it. Original code and comment left above to
                // clarify what we are doing below and why.

                // We know:
                // - effective_env = saved_env.
                // - continuation is not a tail continuation.

                // So, expanding the recursive call, we get:

                let effective_env2 = match &*continuation {
                    Continuation::Lookup(saved_env2, _) => saved_env2,
                    Continuation::Tail(_, _) => unreachable!(),
                    _ => &effective_env,
                };

                match &*continuation {
                    Continuation::Outermost => {
                        Control::Return(result, effective_env.clone(), Continuation::Terminal)
                    }
                    _ => {
                        let thunk = Thunk {
                            value: Box::new(result),
                            continuation: continuation.clone(),
                        };
                        witness.witness_destructured_thunk(&thunk);
                        Control::Return(
                            Expression::Thunk(thunk),
                            effective_env2.clone(),
                            Continuation::Dummy,
                        )
                    }
                }
            }
        }
        // If continuation is outermost, we don't actually make a thunk. Instead, we signal
        // that this is the terminal result by returning a Terminal continuation.
        Continuation::Outermost => Control::Return(result, env, Continuation::Terminal),
        _ => {
            let thunk = Thunk {
                value: Box::new(result),
                continuation: Box::new(cont.clone()),
            };
            witness.witness_destructured_thunk(&thunk);
            Control::Return(Expression::Thunk(thunk), effective_env, Continuation::Dummy)
        }
    };

    {
        let (output_result, output_env, output_cont) = control.results();
    }
    control
}

fn make_tail_continuation(env: &Expression, continuation: &Continuation) -> Continuation {
    // Result must be either a Tail or Outermost continuation.
    match &*continuation {
        // If continuation is already one of these, just return it.
        Continuation::Outermost | Continuation::Tail(_, _) => continuation.clone(),
        // Otherwise, package it along with supplied env as a new Tail continuation.
        _ => Continuation::Tail(env.clone(), Box::new(continuation.clone())),
    }
    // Since this is the only place Tail continuation are created, this ensures Tail continuations never
    // point to one another: they can only be nested one deep.
}

pub fn outer_evaluate(
    expr: Expression,
    env: Expression,
    store: &mut Store,
    limit: usize,
) -> (Expression, Expression, usize, Continuation) {
    let initial_input = IO {
        expr,
        env,
        cont: Continuation::Outermost,
    };

    let frame_iterator: std::iter::Take<FrameIt<'_, IO, Witness>> =
        FrameIt::new(initial_input, store).take(limit);

    // FIXME: Handle limit.
    if let Some(last_frame) = frame_iterator.last() {
        let output = last_frame.output.unwrap();
        (
            output.expr,
            output.env,
            last_frame.i.map(|i| i + 1).unwrap(),
            output.cont,
        )
    } else {
        panic!("xxx")
    }
}

pub fn empty_sym_env(_store: &Store) -> Expression {
    Expression::Nil
}

fn extend(env: &Expression, var: &Expression, val: &Expression, store: &mut Store) -> Expression {
    let cons = store.cons(var, val);
    store.cons(&cons, env)
}

fn extend_rec(
    env: &Expression,
    var: &Expression,
    val: &Expression,
    store: &mut Store,
) -> Expression {
    let (binding_or_env, rest) = store.car_cdr(env);
    let (var_or_binding, _val_or_more_bindings) = store.car_cdr(&binding_or_env);
    match var_or_binding {
        // It's a var, so we are extending a simple env with a recursive env.
        Expression::Sym(_) | Expression::Nil => {
            let cons = store.cons(var, val);
            let list = store.list(vec![cons]);
            store.cons(&list, env)
        }
        // It's a binding, so we are extending a recursive env.
        Expression::Cons(_, _) => {
            let cons = store.cons(var, val);
            let cons2 = store.cons(&cons, &binding_or_env);
            store.cons(&cons2, &rest)
        }
        _ => {
            panic!("Bad input form.")
        }
    }
}

fn extend_closure(fun: &Expression, rec_env: &Expression, store: &mut Store) -> Expression {
    match fun {
        Expression::Fun(arg, body, closed_env) => {
            let closed_env = store.fetch(closed_env).unwrap();
            let extended = store.cons(rec_env, &closed_env);
            store.fun(
                &store.fetch(arg).unwrap(),
                &store.fetch(body).unwrap(),
                &extended,
            )
        }
        _ => panic!("extend_closure received non-Fun: {:?}", fun),
    }
}

#[allow(dead_code)]
fn lookup(env: &Expression, var: &Expression, store: &Store) -> Expression {
    assert_eq!(Tag::Sym, var.tag());
    match &*env {
        Expression::Nil => Expression::Nil,
        Expression::Cons(_, _) => {
            let (binding, smaller_env) = store.car_cdr(env);
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
            let (result, _new_env, _cont, _witness) = eval_expr(
                &num,
                &empty_sym_env(&store),
                &Continuation::Outermost,
                &mut store,
            );
            assert_eq!(num, result);
        }

        {
            let (result, _new_env, _cont, _witness) = eval_expr(
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

            assert_eq!(3, iterations);
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
        let output = s.write_expr_str(&expr);

        assert_eq!("((LAMBDA (X) X) Fr(0x7b))".to_string(), output);
    }

    #[test]
    fn outer_evaluate_lambda() {
        let mut s = Store::default();
        let limit = 20;
        let val = Expression::num(123);
        let expr = s.read("((lambda (x) x) 123)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(6, iterations);
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

        assert_eq!(13, iterations);
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

        assert_eq!(16, iterations);
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

        assert_eq!(16, iterations);
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

        assert_eq!(18, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_sum() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(+ 2 (+ 3 4))").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(9, iterations);
        assert_eq!(Expression::num(9), result_expr);
    }

    #[test]
    fn outer_evaluate_diff() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(- 9 5)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(5, iterations);
        assert_eq!(Expression::num(4), result_expr);
    }

    #[test]
    fn outer_evaluate_product() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(* 9 5)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(5, iterations);
        assert_eq!(Expression::num(45), result_expr);
    }

    #[test]
    fn outer_evaluate_quotient() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(/ 21 7)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(5, iterations);
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

            assert_eq!(5, iterations);
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

            assert_eq!(5, iterations);
            assert_eq!(Expression::Nil, result_expr);
        }
    }

    #[test]
    fn outer_evaluate_adder1() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(((lambda (x) (lambda (y) (+ x y))) 2) 3)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(17, iterations);
        assert_eq!(Expression::num(5), result_expr);
    }

    // Enable this when we have LET.
    #[test]
    fn outer_evaluate_adder2() {
        let mut s = Store::default();
        let limit = 25;
        let expr = s
            .read(
                "(let* ((make-adder (lambda (x) (lambda (y) (+ x y)))))
                   ((make-adder 2) 3))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(20, iterations);
        assert_eq!(Expression::num(5), result_expr);
    }

    #[test]
    fn outer_evaluate_let_simple() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(let* ((a 1)) a)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(4, iterations);
        assert_eq!(Expression::num(1), result_expr);
    }

    #[test]
    fn outer_evaluate_empty_let_bug() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(let* () (+ 1 2))").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(6, iterations);
        assert_eq!(Expression::num(3), result_expr);
    }

    #[test]
    fn outer_evaluate_let() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s
            .read(
                "(let* ((a 1)
                        (b 2))
                   (+ a b))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(13, iterations);
        assert_eq!(Expression::num(3), result_expr);
    }

    //#[test]
    // TODO: Remember to backport this to Lisp implementation when fixed.
    // Actually, this is almost not a bug. It's just that LET as implemented is LET*.
    fn outer_evaluate_let_bug() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(let* ((a 1) (b a)) b)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(10, iterations); // Expected 7
        assert_eq!(s.intern("A"), result_expr);
    }

    #[test]
    fn outer_evaluate_arithmetic_let() {
        let mut s = Store::default();
        let limit = 100;
        let expr = s
            .read(
                "(let* ((a 1)
                        (b 2)
                        (c 3))
                   (+ a (+ b c)))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

        assert_eq!(23, iterations);
        assert_eq!(Expression::num(6), result_expr);
    }

    #[test]
    // Not because it's efficient, but to prove we can.
    fn outer_evaluate_fundamental_conditional() {
        let limit = 100;
        {
            let mut s = Store::default();
            let expr = s
                .read(
                    "(let* ((true (lambda (a)
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

            assert_eq!(45, iterations);
            assert_eq!(Expression::num(5), result_expr);
        }
        {
            let mut s = Store::default();
            let expr = s
                .read(
                    "(let* ((true (lambda (a)
                                    (lambda (b)
                                   a)))
                            (false (lambda (a)
                                  (lambda (b)
                                   b)))
                            (iff (lambda (a)
                                   (lambda (b)
                                     (lambda (cond)
                                       ((cond a) b))))))
                       (((iff 5) 6) false))",
                )
                .unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(42, iterations);
            assert_eq!(Expression::num(6), result_expr);
        }
    }

    #[test]
    fn outer_evaluate_if() {
        let limit = 100;
        {
            let mut s = Store::default();
            let expr = s.read("(if t 5 6)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(4, iterations);
            assert_eq!(Expression::num(5), result_expr);
        }
        {
            let mut s = Store::default();
            let expr = s.read("(if nil 5 6)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(4, iterations);
            assert_eq!(Expression::num(6), result_expr);
        }
    }

    #[test]
    fn outer_evaluate_fully_evaluates() {
        let limit = 100;
        {
            let mut s = Store::default();
            let expr = s.read("(if t (+ 5 5) 6)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(8, iterations);
            assert_eq!(Expression::num(10), result_expr);
        }
    }

    #[test]
    fn outer_evaluate_recursion1() {
        let mut s = Store::default();
        let limit = 200;
        let expr = s
            .read(
                "(letrec* ((exp (lambda (base)
                                  (lambda (exponent)
                                    (if (= 0 exponent)
                                        1
                                        (* base ((exp base) (- exponent 1))))))))
                   ((exp 5) 3))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(117, iterations);
        assert_eq!(Expression::num(125), result_expr);
    }

    #[test]
    fn outer_evaluate_recursion2() {
        let mut s = Store::default();
        let limit = 300;
        let expr = s
            .read(
                "(letrec* ((exp (lambda (base)
                                  (lambda (exponent)
                                     (lambda (acc)
                                       (if (= 0 exponent)
                                          acc
                                          (((exp base) (- exponent 1)) (* acc base))))))))
                   (((exp 5) 5) 1))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(248, iterations);
        assert_eq!(Expression::num(3125), result_expr);
    }

    #[test]
    fn outer_evaluate_recursion_multiarg() {
        let mut s = Store::default();
        let limit = 300;
        let expr = s
            .read(
                "(letrec* ((exp (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp base (- exponent 1)))))))
                          (exp 5 3))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(121, iterations);
        assert_eq!(Expression::num(125), result_expr);
    }

    #[test]
    fn outer_evaluate_recursion_optimized() {
        let mut s = Store::default();
        let limit = 300;
        let expr = s
            .read(
                "(let* ((exp (lambda (base)
                               (letrec* ((base-inner
                                          (lambda (exponent)
                                            (if (= 0 exponent)
                                                1
                                                (* base (base-inner (- exponent 1)))))))
                                        base-inner))))
                    ((exp 5) 3))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(99, iterations);
        assert_eq!(Expression::num(125), result_expr);
    }

    #[test]
    fn outer_evaluate_tail_recursion() {
        let mut s = Store::default();
        let limit = 300;
        let expr = s
            .read(
                "(letrec* ((exp (lambda (base)
                                  (lambda (exponent-remaining)
                                    (lambda (acc)
                                      (if (= 0 exponent-remaining)
                                          acc
                                          (((exp base) (- exponent-remaining 1)) (* acc base))))))))
                          (((exp 5) 3) 1))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(160, iterations);
        assert_eq!(Expression::num(125), result_expr);
    }

    #[test]
    fn outer_evaluate_tail_recursion_somewhat_optimized() {
        let mut s = Store::default();
        let limit = 300;
        let expr = s
            .read(
                "(letrec* ((exp (lambda (base)
                             (letrec* ((base-inner
                                        (lambda (exponent-remaining)
                                          (lambda (acc)
                                            (if (= 0 exponent-remaining)
                                              acc
                                             ((base-inner (- exponent-remaining 1)) (* acc base)))))))
                                      base-inner))))
                   (((exp 5) 3) 1))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(139, iterations);
        assert_eq!(Expression::num(125), result_expr);
    }

    #[test]
    fn outer_evaluate_multiple_letrecstar_bindings() {
        let mut s = Store::default();
        let limit = 300;
        let expr = s
            .read(
                "(letrec* ((double (lambda (x) (* 2 x)))
                           (square (lambda (x) (* x x))))
                   (+ (square 3) (double 2)))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(31, iterations);
        assert_eq!(Expression::num(13), result_expr);
    }

    #[test]
    fn outer_evaluate_multiple_letrecstar_bindings_referencing() {
        let mut s = Store::default();
        let limit = 300;
        let expr = s
            .read(
                "(letrec* ((double (lambda (x) (* 2 x)))
                           (double-inc (lambda (x) (+ 1 (double x)))))
                   (+ (double 3) (double-inc 2)))",
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(43, iterations);
        assert_eq!(Expression::num(11), result_expr);
    }

    #[test]
    fn outer_evaluate_multiple_letrecstar_bindings_recursive() {
        let mut s = Store::default();
        let limit = 500;
        let expr = s
            .read(
                "(letrec* ((exp (lambda (base exponent)
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
            )
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);
        assert_eq!(308, iterations);
        assert_eq!(Expression::num(33), result_expr);
    }

    #[test]
    fn outer_evaluate_eq() {
        {
            let mut s = Store::default();
            let limit = 20;
            let expr = s.read("(eq 'a 'a)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(5, iterations);
            assert_eq!(s.intern("T"), result_expr);
        }
        {
            let mut s = Store::default();
            let limit = 20;
            let expr = s.read("(eq 'a 1)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(5, iterations);
            assert_eq!(Expression::Nil, result_expr);
        }
    }

    #[test]
    fn outer_evaluate_zero_arg_lambda() {
        {
            let mut s = Store::default();
            let limit = 20;
            let expr = s.read("((lambda () 123))").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(6, iterations);
            assert_eq!(Expression::num(123), result_expr);
        }
        {
            let mut s = Store::default();
            let limit = 20;
            let expr = s
                .read("(letrec* ((x 9) (f (lambda () (+ x 1)))) (f))")
                .unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(19, iterations);
            assert_eq!(Expression::num(10), result_expr);
        }
    }

    #[test]
    fn outer_evaluate_make_tree() {
        {
            let mut s = Store::default();
            let limit = 800;
            let expr = s.read("(letrec* ((mapcar (lambda (f list)
                                                             (if (eq list nil)
                                                                 nil
                                                                 (cons (f (car list)) (mapcar f (cdr list))))))
                                         (make-row (lambda (list)
                                                     (if (eq list nil)
                                                         nil
                                                         (let* ((cdr (cdr list)))
                                                           (cons (cons (car list) (car cdr))
                                                                 (make-row (cdr cdr)))))))
                                         (make-tree-aux (lambda (list)
                                                          (let* ((row (make-row list)))
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
                                (reverse-tree (make-tree '(a b c d e f g h))))").unwrap();
            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(616, iterations);
            assert_eq!(
                s.read("(((h . g) . (f . e)) . ((d . c) . (b . a)))")
                    .unwrap(),
                result_expr
            );
        }
    }

    #[test]
    fn outer_evaluate_make_tree_minimal_regression() {
        {
            let mut s = Store::default();
            let limit = 1000;
            let expr = s
                .read(
                    "(letrec* ((fn-1 (lambda (x)
                                    (let* ((y x))
                                       y)))
                               (fn-2 (lambda (list)
                                       (let* ((z (fn-1 list)))
                                         (fn-2 z)))))
                                 (fn-2 '(a b c d e f g h)))",
                )
                .unwrap();
            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(1000, iterations);
        }
    }
    #[test]
    fn outer_evaluate_map_tree_bug() {
        {
            let mut s = Store::default();
            let limit = 1000;
            let expr = s
                .read(
                    "(letrec* ((map-tree (lambda (f tree)
                      (if (atom tree)
                          (f tree)
                          (cons (map-tree f (car tree))
                                (map-tree f (cdr tree)))))))
         (map-tree (lambda (x) (+ 1 x)) '((1 . 2) . (3 . 4))))",
                )
                .unwrap();
            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(s.read("((2 . 3) . (4 . 5))").unwrap(), result_expr);

            assert_eq!(214, iterations);
        }
    }
    #[test]
    fn outer_evaluate_map_tree_relop_bug() {
        {
            // Reuse map-tree failure case to test Relop behavior.
            // This failed initially and tests regression.
            let mut s = Store::default();
            let limit = 1000;
            let expr = s
                .read(
                    "(letrec* ((map-tree (lambda (f tree)
                                           (if (atom tree)
                                             (f tree)
                                               (= (map-tree f (car tree))
                                                  (map-tree f (cdr tree)))))))
                       (map-tree (lambda (x) (+ 1 x)) '((1 . 2) . (3 . 4))))",
                )
                .unwrap();
            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(Expression::Nil, result_expr);

            assert_eq!(214, iterations);
        }
    }

    #[test]
    fn env_lost_bug() {
        {
            // previously, an unbound variable `u` error
            let mut s = Store::default();
            let limit = 1000;
            let expr = s
                .read(
                    "
(letrec*
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
",
                )
                .unwrap();
            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(Expression::Nil, result_expr);

            assert_eq!(34, iterations);
        }
    }

    #[test]
    fn dont_discard_rest_env() {
        {
            // previously: Unbound variable: Sym("Z")
            let mut s = Store::default();
            let limit = 1000;
            let expr = s
                .read(
                    "(let* ((z 9))
                       (letrec* ((a 1)
                                 (b 2)
                                 (l (lambda (x) (+ z x))))
                         (l 9)))",
                )
                .unwrap();
            let (result_expr, _new_env, iterations, _continuation) =
                outer_evaluate(expr, empty_sym_env(&s), &mut s, limit);

            assert_eq!(Expression::num(18), result_expr);

            assert_eq!(29, iterations);
        }
    }
}
