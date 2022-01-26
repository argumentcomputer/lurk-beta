use crate::store::{
    ContPtr, ContTag, Continuation, Expression, Op1, Op2, Pointer, Ptr, Rel2, Store, Tag, Thunk,
};
use crate::writer::Write;
use std::cmp::PartialEq;
use std::iter::{Iterator, Take};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IO {
    pub expr: Ptr,
    pub env: Ptr,
    pub cont: ContPtr, // This could be a Ptr too, if we want Continuations to be first class.
}

impl Write for IO {
    fn fmt<W: std::io::Write>(&self, store: &Store, w: &mut W) -> std::io::Result<()> {
        write!(w, "IO {{ expr: ")?;
        self.expr.fmt(store, w)?;
        write!(w, ", env: ")?;
        self.env.fmt(store, w)?;
        write!(w, ", cont: ")?;
        self.cont.fmt(store, w)?;
        write!(w, " }}")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame<T, W> {
    pub input: T,
    pub output: T,
    pub i: usize,
    pub witness: W,
}

impl<T: PartialEq + std::fmt::Debug, W> Frame<T, W> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        let sequential = self.i + 1 == maybe_next.i;
        let io_match = self.output == maybe_next.input;

        sequential && io_match
    }
}

pub trait Evaluable<W> {
    fn eval(&self, store: &mut Store) -> (Self, W)
    where
        Self: Sized;

    fn is_terminal(&self) -> bool;
}

impl Evaluable<Witness> for IO {
    fn eval(&self, store: &mut Store) -> (Self, Witness) {
        let (expr, env, cont, witness) = eval_expr(self.expr, self.env, self.cont, store);
        (Self { expr, env, cont }, witness)
    }

    fn is_terminal(&self) -> bool {
        matches!(self.cont.tag(), ContTag::Error | ContTag::Terminal)
    }
}

impl<T: Evaluable<Witness> + Clone + PartialEq> Frame<T, Witness> {
    fn next(&self, store: &mut Store) -> Self {
        let input = self.output.clone();
        let (output, witness) = input.eval(store);

        Self {
            input,
            output,
            i: self.i + 1,
            witness,
        }
    }
}

impl<T: Evaluable<Witness> + Clone + PartialEq> Frame<T, Witness> {
    fn from_initial_input(input: T, store: &mut Store) -> Self {
        let (output, witness) = input.eval(store);

        Self {
            input,
            output,
            i: 0,
            witness,
        }
    }
}

pub struct FrameIt<'a, T, W> {
    first: bool,
    frame: Frame<T, W>,
    store: &'a mut Store,
}

impl<'a, 'b, T: Evaluable<Witness> + Clone + PartialEq> FrameIt<'a, T, Witness> {
    fn new(initial_input: T, store: &'a mut Store) -> Self {
        let frame = Frame::from_initial_input(initial_input, store);
        Self {
            first: true,
            frame,
            store,
        }
    }

    /// Like `.iter().take(n).last()`, but skips intermediary stages, to optimize
    /// for evaluation.
    fn next_n(mut self, n: usize) -> Option<Frame<T, Witness>> {
        for _i in 0..n {
            // skip first iteration, as one evlatuation happens on construction
            if self.first {
                self.first = false;
                continue;
            }

            if self.frame.output.is_terminal() {
                break;
            }

            self.frame = self.frame.next(self.store);
        }
        Some(self.frame)
    }
}

impl<'a, 'b, T: Evaluable<Witness> + Clone + PartialEq> Iterator for FrameIt<'a, T, Witness> {
    type Item = Frame<T, Witness>;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        // skip first iteration, as one evlatuation happens on construction
        if self.first {
            self.first = false;
            return Some(self.frame.clone());
        }

        if self.frame.output.is_terminal() {
            return None;
        }

        self.frame = self.frame.next(self.store);
        Some(self.frame.clone())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Witness {
    // TODO: Many of these fields ended up not being used.
    // once circuit is done, remove the excess.
    pub(crate) prethunk_output_expr: Ptr,
    pub(crate) prethunk_output_env: Ptr,
    pub(crate) prethunk_output_cont: ContPtr,

    pub(crate) destructured_thunk: Option<Thunk>,
    pub(crate) extended_closure: Option<Ptr>,
    pub(crate) invoke_continuation_cont: Option<ContPtr>,
}

impl Witness {
    fn witness_destructured_thunk(&mut self, thunk: &Thunk) {
        assert!(
            self.destructured_thunk.is_none(),
            "Only one thunk should be destructured per evaluation step."
        );
        self.destructured_thunk = Some(*thunk);
    }
}

fn eval_expr(
    expr: Ptr,
    env: Ptr,
    cont: ContPtr,
    store: &mut Store,
) -> (Ptr, Ptr, ContPtr, Witness) {
    let (ctrl, witness) = eval_expr_with_witness(expr, env, cont, store);
    let (new_expr, new_env, new_cont) = ctrl.into_results();

    (new_expr, new_env, new_cont, witness)
}

#[derive(Debug, Clone)]
pub enum Control {
    Return(Ptr, Ptr, ContPtr),
    MakeThunk(Ptr, Ptr, ContPtr),
    InvokeContinuation(Ptr, Ptr, ContPtr),
}

impl Control {
    pub fn as_results(&self) -> (&Ptr, &Ptr, &ContPtr) {
        match self {
            Self::Return(expr, env, cont) => (expr, env, cont),
            Self::MakeThunk(expr, env, cont) => (expr, env, cont),
            Self::InvokeContinuation(expr, env, cont) => (expr, env, cont),
        }
    }

    pub fn into_results(self) -> (Ptr, Ptr, ContPtr) {
        match self {
            Self::Return(expr, env, cont) => (expr, env, cont),
            Self::MakeThunk(expr, env, cont) => (expr, env, cont),
            Self::InvokeContinuation(expr, env, cont) => (expr, env, cont),
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
    expr: Ptr,
    env: Ptr,
    cont: ContPtr,
    store: &mut Store,
) -> (Control, Witness) {
    let mut extended_closure = None;
    let control = match expr.tag() {
        Tag::Thunk => match store.fetch(&expr).unwrap() {
            Expression::Thunk(thunk) => {
                Control::InvokeContinuation(thunk.value, env, thunk.continuation)
            }
            _ => unreachable!(),
        },
        Tag::Nil => Control::InvokeContinuation(expr, env, cont),
        Tag::Sym => {
            if expr == store.intern_sym("NIL") || (expr == store.intern_sym("T")) {
                // NIL and T are self-evaluating symbols, pass them to the continuation in a thunk.

                // CIRCUIT: sym_is_self_evaluating
                //          cond1
                Control::InvokeContinuation(expr, env, cont)
            } else {
                // Otherwise, look for a matching binding in env.

                // CIRCUIT: sym_otherwise
                if env.is_nil() {
                    //     //assert!(!env.is_nil(), "Unbound variable: {:?}", expr);
                    Control::Return(expr, env, store.intern_cont_error())
                } else {
                    let (binding, smaller_env) = store.car_cdr(&env);
                    if binding.is_nil() {
                        // If binding is NIL, it's empty. There is no match. Return an error due to unbound variable.

                        // CIRCUIT: binding_is_nil
                        //          otherwise_and_binding_is_nil
                        //          cond2
                        Control::Return(expr, env, store.intern_cont_error())
                    } else {
                        // Binding is not NIL, so it is either a normal binding or a recursive environment.

                        // CIRCUIT: binding_not_nil
                        //          otherwise_and_binding_not_nil
                        let (var_or_rec_binding, val_or_more_rec_env) = store.car_cdr(&binding);
                        match var_or_rec_binding.tag() {
                            Tag::Sym => {
                                // We are in a simple env (not a recursive env),
                                // looking at a binding's variable.

                                // CIRCUIT: var_or_rec_binding_is_sym
                                //          otherwise_and_sym
                                let v = var_or_rec_binding;
                                let val = val_or_more_rec_env;

                                if v == expr {
                                    // expr matches the binding's var.

                                    // CIRCUIT: v_is_expr1
                                    //          v_is_expr1_real
                                    //          otherwise_and_v_expr_and_sym
                                    //          cond3

                                    // Pass the binding's value to the continuation in a thunk.
                                    Control::InvokeContinuation(val, env, cont)
                                } else {
                                    // expr does not match the binding's var.

                                    // CIRCUIT: otherwise_and_v_not_expr
                                    match cont.tag() {
                                        ContTag::Lookup => {
                                            // If performing a lookup, continue with remaining env.

                                            // CIRCUIT: cont_is_lookup
                                            //          cont_is_lookup_sym
                                            //          cond4
                                            Control::Return(expr, smaller_env, cont)
                                        }
                                        _ =>
                                        // Otherwise, create a lookup continuation, packaging current env
                                        // to be restored later.

                                        // CIRCUIT: cont_not_lookup_sym
                                        //          cond5
                                        {
                                            Control::Return(
                                                expr,
                                                smaller_env,
                                                store.intern_cont_lookup(env, cont),
                                            )
                                        }
                                    }
                                }
                            }
                            // Start of a recursive_env.
                            Tag::Cons => {
                                // CIRCUIT: var_or_rec_binding_is_cons
                                //          otherwise_and_cons
                                let rec_env = binding;
                                let smaller_rec_env = val_or_more_rec_env;

                                let (v2, val2) = store.car_cdr(&var_or_rec_binding);
                                if v2 == expr {
                                    // CIRCUIT: v2_is_expr
                                    //          v2_is_expr_real
                                    //          cond6
                                    let val_to_use = {
                                        // CIRCUIT: val_to_use
                                        match val2.tag() {
                                            Tag::Fun => {
                                                // TODO: This is a misnomer. It's actually the closure *to be extended*.
                                                extended_closure = Some(val2);
                                                // CIRCUIT: val2_is_fun

                                                // We just found a closure in a recursive env.
                                                // We need to extend its environment to include that recursive env.

                                                extend_closure(&val2, &rec_env, store)
                                            }
                                            _ => {
                                                extended_closure = None;
                                                val2
                                            }
                                        }
                                    };
                                    Control::InvokeContinuation(val_to_use, env, cont)
                                } else {
                                    // CIRCUIT: v2_not_expr
                                    //          otherwise_and_v2_not_expr
                                    //          cond7
                                    let env_to_use = if smaller_rec_env.is_nil() {
                                        // CIRCUIT: smaller_rec_env_is_nil
                                        smaller_env
                                    } else {
                                        // CIRCUIT: with_smaller_rec_env
                                        store.intern_cons(smaller_rec_env, smaller_env)
                                    };
                                    match cont.tag() {
                                        ContTag::Lookup => {
                                            // CIRCUIT: cont_is_lookup
                                            //          cont_is_lookup_cons
                                            //          cond8
                                            Control::Return(expr, env_to_use, cont)
                                        }
                                        _ => Control::Return(
                                            // CIRCUIT: cont_not_lookup_cons
                                            //          cond9
                                            expr,
                                            env_to_use,
                                            store.intern_cont_lookup(env, cont),
                                        ),
                                    }
                                }
                            }
                            _ => panic!("Bad form."),
                        }
                    }
                }
            }
        }
        Tag::Str => unimplemented!(),
        Tag::Num => Control::InvokeContinuation(expr, env, cont),
        Tag::Fun => Control::InvokeContinuation(expr, env, cont),
        Tag::Cons => {
            let (head, rest) = store.car_cdr(&expr);
            let lambda = store.intern_sym("LAMBDA");
            let quote = store.intern_sym("QUOTE");
            let dummy_arg = store.intern_sym("_");

            if head == lambda {
                let (args, body) = store.car_cdr(&rest);
                let (arg, _rest) = if args.is_nil() {
                    // (LAMBDA () STUFF)
                    // becomes (LAMBDA (DUMMY) STUFF)
                    (dummy_arg, store.intern_nil())
                } else {
                    store.car_cdr(&args)
                };
                let cdr_args = store.cdr(&args);
                let inner_body = if cdr_args.is_nil() {
                    body
                } else {
                    // (LAMBDA (A B) STUFF)
                    // becomes (LAMBDA (A) (LAMBDA (B) STUFF))
                    let inner = store.intern_cons(cdr_args, body);
                    let l = store.intern_cons(lambda, inner);
                    store.intern_list(&[l])
                };
                let function = store.intern_fun(arg, inner_body, env);

                Control::InvokeContinuation(function, env, cont)
            } else if head == quote {
                let (quoted, end) = store.car_cdr(&rest);
                assert!(end.is_nil());
                Control::InvokeContinuation(quoted, env, cont)
            } else if head == store.intern_sym("LET*") {
                let (bindings, body) = store.car_cdr(&rest);
                let (body1, rest_body) = store.car_cdr(&body);
                // Only a single body form allowed for now.
                assert!(rest_body.is_nil());

                if bindings.is_nil() {
                    Control::Return(body1, env, cont)
                } else {
                    let (binding1, rest_bindings) = store.car_cdr(&bindings);
                    let (var, more_vals) = store.car_cdr(&binding1);
                    let (val, end) = store.car_cdr(&more_vals);
                    assert!(end.is_nil());

                    let expanded = if rest_bindings.is_nil() {
                        body1
                    } else {
                        let lt = store.intern_sym("LET*");
                        store.intern_list(&[lt, rest_bindings, body1])
                    };
                    Control::Return(
                        val,
                        env,
                        store.intern_cont_let_star(var, expanded, env, cont),
                    )
                }
            } else if head == store.intern_sym("LETREC*") {
                let (bindings, body) = store.car_cdr(&rest);
                let (body1, rest_body) = store.car_cdr(&body);
                // Only a single body form allowed for now.
                assert!(rest_body.is_nil());
                if bindings.is_nil() {
                    Control::Return(body1, env, cont)
                } else {
                    let (binding1, rest_bindings) = store.car_cdr(&bindings);
                    let (var, more_vals) = store.car_cdr(&binding1);
                    let (val, end) = store.car_cdr(&more_vals);
                    assert!(end.is_nil());

                    let expanded = if rest_bindings.is_nil() {
                        body1
                    } else {
                        let lt = store.intern_sym("LETREC*");
                        store.intern_list(&[lt, rest_bindings, body1])
                    };
                    Control::Return(
                        val,
                        env,
                        store.intern_cont_let_rec_star(var, expanded, env, cont),
                    )
                }
            } else if head == store.intern_sym("cons") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env,
                    store.intern_cont_binop(Op2::Cons, env, more, cont),
                )
            } else if head == store.intern_sym("car") {
                let (arg1, end) = store.car_cdr(&rest);
                assert!(end.is_nil());
                Control::Return(arg1, env, store.intern_cont_unop(Op1::Car, cont))
            } else if head == store.intern_sym("cdr") {
                let (arg1, end) = store.car_cdr(&rest);
                assert!(end.is_nil());
                Control::Return(arg1, env, store.intern_cont_unop(Op1::Cdr, cont))
            } else if head == store.intern_sym("atom") {
                let (arg1, end) = store.car_cdr(&rest);
                assert!(end.is_nil());
                Control::Return(arg1, env, store.intern_cont_unop(Op1::Atom, cont))
            } else if head == store.intern_sym("+") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env,
                    store.intern_cont_binop(Op2::Sum, env, more, cont),
                )
            } else if head == store.intern_sym("-") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env,
                    store.intern_cont_binop(Op2::Diff, env, more, cont),
                )
            } else if head == store.intern_sym("*") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env,
                    store.intern_cont_binop(Op2::Product, env, more, cont),
                )
            } else if head == store.intern_sym("/") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env,
                    store.intern_cont_binop(Op2::Quotient, env, more, cont),
                )
            } else if head == store.intern_sym("=") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env,
                    store.intern_cont_relop(Rel2::NumEqual, env, more, cont),
                )
            } else if head == store.intern_sym("eq") {
                let (arg1, more) = store.car_cdr(&rest);
                Control::Return(
                    arg1,
                    env,
                    store.intern_cont_relop(Rel2::Equal, env, more, cont),
                )
            } else if head == store.intern_sym("if") {
                let (condition, more) = store.car_cdr(&rest);
                Control::Return(condition, env, store.intern_cont_if(more, cont))
            } else if head == store.intern_sym("current-env") {
                assert!(rest.is_nil());
                Control::InvokeContinuation(env, env, cont)
            } else {
                // (fn . args)
                let fun_form = head;
                let args = rest;
                let (arg, more_args) = if args.is_nil() {
                    (store.intern_nil(), store.intern_nil())
                } else {
                    store.car_cdr(&args)
                };
                match more_args.tag() {
                    // (fn arg)
                    // Interpreting as call.
                    Tag::Nil => {
                        Control::Return(fun_form, env, store.intern_cont_call(arg, env, cont))
                    }
                    _ => {
                        // Interpreting as multi-arg call.
                        // (fn arg . more_args) => ((fn arg) . more_args)
                        let expanded_inner = store.intern_list(&[fun_form, arg]);
                        let expanded = store.intern_cons(expanded_inner, more_args);
                        Control::Return(expanded, env, cont)
                    }
                }
            }
        }
    };

    let (new_expr, new_env, new_cont) = control.as_results();

    let mut witness = Witness {
        prethunk_output_expr: *new_expr,
        prethunk_output_env: *new_env,
        prethunk_output_cont: *new_cont,

        destructured_thunk: None,
        extended_closure,
        invoke_continuation_cont: None,
    };

    let control = invoke_continuation(control, store, &mut witness);
    let ctrl = make_thunk(control, store, &mut witness);

    (ctrl, witness)
}

fn invoke_continuation(control: Control, store: &mut Store, witness: &mut Witness) -> Control {
    if !control.is_invoke_continuation() {
        return control;
    }

    let (result, env, cont) = control.as_results();

    witness.invoke_continuation_cont = Some(*cont);

    let control = match cont.tag() {
        ContTag::Terminal => unreachable!("Terminal Continuation should never be invoked."),
        ContTag::Dummy => unreachable!("Dummy Continuation should never be invoked."),
        ContTag::Outermost => match result.tag() {
            Tag::Thunk => match store.fetch(result).unwrap() {
                Expression::Thunk(thunk) => {
                    witness.witness_destructured_thunk(&thunk);
                    Control::Return(thunk.value, *env, store.intern_cont_terminal())
                }
                _ => unreachable!(),
            },
            _ => Control::Return(*result, *env, store.intern_cont_terminal()),
        },
        ContTag::Call => match result.tag() {
            // (arg, saved_env, continuation)
            Tag::Fun => match store.fetch_cont(cont).unwrap() {
                Continuation::Call(arg, saved_env, continuation) => {
                    let function = result;
                    let next_expr = arg;
                    let newer_cont = store.intern_cont_call2(*function, saved_env, continuation);
                    Control::Return(next_expr, *env, newer_cont)
                }
                _ => unreachable!(),
            },
            _ => {
                Control::Return(*result, *env, store.intern_cont_error())
                // Bad function
            }
        },
        ContTag::Call2 => match store.fetch_cont(cont).unwrap() {
            Continuation::Call2(function, saved_env, continuation) => match function.tag() {
                Tag::Fun => match store.fetch(&function).unwrap() {
                    Expression::Fun(arg, body, closed_env) => {
                        let body_form = store.car(&body);
                        let newer_env = extend(closed_env, arg, *result, store);
                        let cont = make_tail_continuation(saved_env, continuation, store);
                        Control::Return(body_form, newer_env, cont)
                    }
                    _ => unreachable!(),
                },
                _ => {
                    Control::Return(*result, *env, store.intern_cont_error())
                    // panic!("Call2 continuation contains a non-function: {:?}", function);
                }
            },
            _ => unreachable!(),
        },
        ContTag::LetStar => match store.fetch_cont(cont).unwrap() {
            Continuation::LetStar(var, body, saved_env, continuation) => {
                let extended_env = extend(*env, var, *result, store);
                let c = make_tail_continuation(saved_env, continuation, store);

                Control::Return(body, extended_env, c)
            }
            _ => unreachable!(),
        },
        ContTag::LetRecStar => match store.fetch_cont(cont).unwrap() {
            Continuation::LetRecStar(var, body, saved_env, continuation) => {
                let extended_env = extend_rec(*env, var, *result, store);
                let c = make_tail_continuation(saved_env, continuation, store);

                Control::Return(body, extended_env, c)
            }
            _ => unreachable!(),
        },
        ContTag::Unop => match store.fetch_cont(cont).unwrap() {
            Continuation::Unop(op1, continuation) => {
                let val = match op1 {
                    Op1::Car => store.car(result),
                    Op1::Cdr => store.cdr(result),
                    Op1::Atom => match result.tag() {
                        Tag::Cons => store.intern_nil(),
                        _ => store.intern_sym("T"),
                    },
                };
                Control::MakeThunk(val, *env, continuation)
            }
            _ => unreachable!(),
        },
        ContTag::Binop => match store.fetch_cont(cont).unwrap() {
            Continuation::Binop(op2, saved_env, unevaled_args, continuation) => {
                let (arg2, rest) = store.car_cdr(&unevaled_args);
                assert!(rest.is_nil());
                Control::Return(
                    arg2,
                    saved_env,
                    store.intern_cont_binop2(op2, *result, continuation),
                )
            }
            _ => unreachable!(),
        },
        ContTag::Binop2 => match store.fetch_cont(cont).unwrap() {
            Continuation::Binop2(op2, arg1, continuation) => {
                let arg2 = result;
                let result = match (store.fetch(&arg1).unwrap(), store.fetch(arg2).unwrap()) {
                    (Expression::Num(a), Expression::Num(b)) => match op2 {
                        Op2::Sum => {
                            let mut tmp = a;
                            tmp += b;
                            store.intern_num(tmp)
                        }
                        Op2::Diff => {
                            let mut tmp = a;
                            tmp -= b;
                            store.intern_num(tmp)
                        }
                        Op2::Product => {
                            let mut tmp = a;
                            tmp *= b;
                            store.intern_num(tmp)
                        }
                        Op2::Quotient => {
                            let mut tmp = a;
                            // TODO: Return error continuation.
                            let b_is_zero: bool = b.is_zero();
                            assert!(!b_is_zero, "Division by zero error.");
                            tmp /= b;
                            store.intern_num(tmp)
                        }
                        Op2::Cons => store.intern_cons(arg1, *arg2),
                    },
                    _ => match op2 {
                        Op2::Cons => store.intern_cons(arg1, *arg2),
                        _ => unimplemented!("Binop2"),
                    },
                };
                Control::MakeThunk(result, *env, continuation)
            }
            _ => unreachable!(),
        },
        ContTag::Relop => match store.fetch_cont(cont).unwrap() {
            Continuation::Relop(rel2, saved_env, unevaled_args, continuation) => {
                let (arg2, rest) = store.car_cdr(&unevaled_args);
                assert!(rest.is_nil());
                Control::Return(
                    arg2,
                    saved_env,
                    store.intern_cont_relop2(rel2, *result, continuation),
                )
            }
            _ => unreachable!(),
        },
        ContTag::Relop2 => match store.fetch_cont(cont).unwrap() {
            Continuation::Relop2(rel2, arg1, continuation) => {
                let arg2 = result;
                let result = match (arg1.tag(), arg2.tag()) {
                    (Tag::Num, Tag::Num) => match rel2 {
                        Rel2::NumEqual | Rel2::Equal => {
                            if &arg1 == arg2 {
                                store.intern_sym("T") // TODO: maybe explicit boolean.
                            } else {
                                store.intern_nil()
                            }
                        }
                    },
                    (_, _) => match rel2 {
                        Rel2::NumEqual => store.intern_nil(), // FIXME: This should be a type error.
                        Rel2::Equal => {
                            if &arg1 == arg2 {
                                store.intern_sym("T")
                            } else {
                                store.intern_nil()
                            }
                        }
                    },
                };
                Control::MakeThunk(result, *env, continuation)
            }
            _ => unreachable!(),
        },
        ContTag::If => match store.fetch_cont(cont).unwrap() {
            Continuation::If(more_args, continuation) => {
                let condition = result;
                let (arg1, more) = store.car_cdr(&more_args);
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

                if condition.is_nil() {
                    let (arg2, end) = store.car_cdr(&more);
                    assert!(end.is_nil());
                    Control::Return(arg2, *env, continuation)
                } else {
                    Control::Return(arg1, *env, continuation)
                }
            }
            _ => unreachable!(),
        },
        ContTag::Lookup => match store.fetch_cont(cont).unwrap() {
            Continuation::Lookup(saved_env, continuation) => {
                Control::MakeThunk(*result, saved_env, continuation)
            }
            _ => unreachable!(),
        },
        ContTag::Tail => match store.fetch_cont(cont).unwrap() {
            Continuation::Tail(saved_env, continuation) => {
                Control::MakeThunk(*result, saved_env, continuation)
            }
            _ => {
                unreachable!();
            }
        },
        ContTag::Simple | ContTag::Error => unreachable!(),
    };

    if control.is_invoke_continuation() {
        unreachable!();
    }

    control
}

// Returns (Expression::Thunk, Expression::Env, Continuation)
fn make_thunk(control: Control, store: &mut Store, _witness: &mut Witness) -> Control {
    if !control.is_make_thunk() {
        return control;
    }

    let (result, env, cont) = control.into_results();

    if let Tag::Thunk = result.tag() {
        unreachable!("make_thunk should never be called with a thunk");
    };

    match cont.tag() {
        ContTag::Tail => match store.fetch_cont(&cont).unwrap() {
            Continuation::Tail(saved_env, continuation) => {
                let thunk = store.intern_thunk(Thunk {
                    value: result,
                    continuation,
                });
                Control::Return(thunk, saved_env, store.intern_cont_dummy())
            }
            _ => unreachable!(),
        },
        // If continuation is outermost, we don't actually make a thunk. Instead, we signal
        // that this is the terminal result by returning a Terminal continuation.
        ContTag::Outermost => Control::Return(result, env, store.intern_cont_terminal()),
        _ => {
            let thunk = store.intern_thunk(Thunk {
                value: result,
                continuation: cont,
            });
            Control::Return(thunk, env, store.intern_cont_dummy())
        }
    }
}

fn make_tail_continuation(env: Ptr, continuation: ContPtr, store: &mut Store) -> ContPtr {
    // Result must be either a Tail or Outermost continuation.
    match continuation.tag() {
        // If continuation is already tail, just return it.
        ContTag::Tail => continuation,
        // Otherwise, package it along with supplied env as a new Tail continuation.
        _ => store.intern_cont_tail(env, continuation),
    }
    // Since this is the only place Tail continuation are created, this ensures Tail continuations never
    // point to one another: they can only be nested one deep.
}

pub struct Evaluator<'a> {
    expr: Ptr,
    env: Ptr,
    store: &'a mut Store,
    limit: usize,
}

impl<'a> Evaluator<'a> {
    pub fn new(expr: Ptr, env: Ptr, store: &'a mut Store, limit: usize) -> Self {
        Evaluator {
            expr,
            env,
            store,
            limit,
        }
    }

    pub fn eval(&mut self) -> (Ptr, Ptr, usize, ContPtr) {
        let initial_input = self.initial();
        let frame_iterator = FrameIt::new(initial_input, self.store);

        if let Some(last_frame) = frame_iterator.next_n(self.limit) {
            let output = last_frame.output;
            (output.expr, output.env, last_frame.i + 1, output.cont)
        } else {
            panic!("xxx")
        }
    }

    pub fn initial(&self) -> IO {
        IO {
            expr: self.expr,
            env: self.env,
            cont: self.store.intern_cont_outermost(),
        }
    }

    pub fn iter(&mut self) -> Take<FrameIt<'_, IO, Witness>> {
        let initial_input = self.initial();

        FrameIt::new(initial_input, self.store).take(self.limit)
    }
}

pub fn empty_sym_env(store: &Store) -> Ptr {
    store.get_nil()
}

fn extend(env: Ptr, var: Ptr, val: Ptr, store: &mut Store) -> Ptr {
    let cons = store.intern_cons(var, val);
    store.intern_cons(cons, env)
}

fn extend_rec(env: Ptr, var: Ptr, val: Ptr, store: &mut Store) -> Ptr {
    let (binding_or_env, rest) = store.car_cdr(&env);
    let (var_or_binding, _val_or_more_bindings) = store.car_cdr(&binding_or_env);
    match var_or_binding.tag() {
        // It's a var, so we are extending a simple env with a recursive env.
        Tag::Sym | Tag::Nil => {
            let cons = store.intern_cons(var, val);
            let list = store.intern_list(&[cons]);
            store.intern_cons(list, env)
        }
        // It's a binding, so we are extending a recursive env.
        Tag::Cons => {
            let cons = store.intern_cons(var, val);
            let cons2 = store.intern_cons(cons, binding_or_env);
            store.intern_cons(cons2, rest)
        }
        _ => {
            panic!("Bad input form.")
        }
    }
}

fn extend_closure(fun: &Ptr, rec_env: &Ptr, store: &mut Store) -> Ptr {
    match fun.tag() {
        Tag::Fun => match store.fetch(fun).unwrap() {
            Expression::Fun(arg, body, closed_env) => {
                let extended = store.intern_cons(*rec_env, closed_env);
                store.intern_fun(arg, body, extended)
            }
            _ => unreachable!(),
        },
        _ => panic!("extend_closure received non-Fun: {:?}", fun),
    }
}

#[allow(dead_code)]
fn lookup(env: &Ptr, var: &Ptr, store: &Store) -> Ptr {
    assert!(matches!(var.tag(), Tag::Sym));
    match env.tag() {
        Tag::Nil => store.get_nil(),
        Tag::Cons => {
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
    use crate::writer::Write;

    #[test]
    fn test_lookup() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let var = store.intern_sym("variable");
        let val = store.intern_num(123);

        assert!(lookup(&env, &var, &store).is_nil());

        let new_env = extend(env, var, val, &mut store);
        assert_eq!(val, lookup(&new_env, &var, &store));
    }

    #[test]
    fn test_eval_expr_simple() {
        let mut store = Store::default();

        {
            let num = store.intern_num(123);
            let (result, _new_env, _cont, _witness) = eval_expr(
                num,
                empty_sym_env(&store),
                store.intern_cont_outermost(),
                &mut store,
            );
            assert_eq!(num, result);
        }

        {
            let (result, _new_env, _cont, _witness) = eval_expr(
                store.intern_nil(),
                empty_sym_env(&store),
                store.intern_cont_outermost(),
                &mut store,
            );
            assert!(result.is_nil());
        }
    }

    #[test]
    fn outer_evaluate_simple() {
        let mut store = Store::default();

        let limit = 20;
        let val = store.intern_num(999);
        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(val, empty_sym_env(&store), &mut store, limit).eval();

        assert_eq!(1, iterations);
        assert_eq!(&result_expr, &val);
    }

    #[test]
    fn outer_evaluate_lookup() {
        let mut store = Store::default();

        let limit = 20;
        let val = store.intern_num(999);
        let var = store.intern_sym("apple");
        let val2 = store.intern_num(888);
        let var2 = store.intern_sym("banana");
        let env = extend(empty_sym_env(&store), var, val, &mut store);

        {
            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(var, env, &mut store, limit).eval();

            assert_eq!(1, iterations);
            assert_eq!(&result_expr, &val);
        }
        {
            let env2 = extend(env, var2, val2, &mut store);
            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(var, env2, &mut store, limit).eval();

            assert_eq!(2, iterations);
            assert_eq!(&result_expr, &val);
        }
    }

    #[test]
    fn print_expr() {
        let mut s = Store::default();
        let nil = s.intern_nil();
        let x = s.intern_sym("x");
        let lambda = s.intern_sym("lambda");
        let val = s.intern_num(123);
        let lambda_args = s.intern_cons(x, nil);
        let body = s.intern_cons(x, nil);
        let rest = s.intern_cons(lambda_args, body);
        let whole_lambda = s.intern_cons(lambda, rest);
        let lambda_arguments = s.intern_cons(val, nil);
        let expr = s.intern_cons(whole_lambda, lambda_arguments);
        let output = expr.fmt_to_string(&s);

        assert_eq!("((LAMBDA (X) X) Num(0x7b))".to_string(), output);
    }

    #[test]
    fn outer_evaluate_lambda() {
        let mut s = Store::default();
        let limit = 20;
        let val = s.intern_num(123);
        let expr = s.read("((lambda (x) x) 123)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(4, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_lambda2() {
        let mut s = Store::default();
        let limit = 20;
        let val = s.intern_num(123);
        let expr = s.read("((lambda (y) ((lambda (x) y) 321)) 123)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(9, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_lambda3() {
        let mut s = Store::default();
        let limit = 20;
        let val = s.intern_num(123);
        let expr = s
            .read("((lambda (y) ((lambda (x) ((lambda (z) z) x)) y)) 123)")
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(10, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_lambda4() {
        let mut s = Store::default();
        let limit = 20;
        let _val = s.intern_num(999);
        let val2 = s.intern_num(888);
        let expr = s
            // NOTE: We pass two different values. This tests which is returned.
            .read("((lambda (y) ((lambda (x) ((lambda (z) z) x)) 888)) 999)")
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(10, iterations);
        assert_eq!(val2, result_expr);
    }

    #[test]
    fn outer_evaluate_lambda5() {
        let mut s = Store::default();
        let limit = 20;
        let val = s.intern_num(999);
        let expr = s
            // Bind a function to the name FN, then call it.
            .read("(((lambda (fn) (lambda (x) (fn x))) (lambda (y) y)) 999)")
            .unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(13, iterations);
        assert_eq!(val, result_expr);
    }

    #[test]
    fn outer_evaluate_sum() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(+ 2 (+ 3 4))").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(6, iterations);
        assert_eq!(s.intern_num(9), result_expr);
    }

    #[test]
    fn outer_evaluate_diff() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(- 9 5)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(3, iterations);
        assert_eq!(s.intern_num(4), result_expr);
    }

    #[test]
    fn outer_evaluate_product() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(* 9 5)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(3, iterations);
        assert_eq!(s.intern_num(45), result_expr);
    }

    #[test]
    fn outer_evaluate_quotient() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(/ 21 7)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(3, iterations);
        assert_eq!(s.intern_num(3), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
    }

    #[test]
    fn outer_evaluate_num_equal() {
        let mut s = Store::default();
        let limit = 20;

        {
            let expr = s.read("(= 5 5)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(3, iterations);
            // TODO: Consider special-casing T, like NIL, and force it to the
            // immediate value 1 (with Symbol type-tag). That way boolean logic
            // will work out. It might be more consistent to have an explicit
            // boolean type (like Scheme), though. Otherwise we will have to
            // think about handling of symbol names (if made explicit), since
            // neither T/NIL as 1/0 will *not* be hashes of their symbol names.
            assert_eq!(s.intern_sym("T"), result_expr);
        }
        {
            let expr = s.read("(= 5 6)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(3, iterations);
            assert!(result_expr.is_nil());
        }
    }

    #[test]
    fn outer_evaluate_adder1() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(((lambda (x) (lambda (y) (+ x y))) 2) 3)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(13, iterations);
        assert_eq!(s.intern_num(5), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(15, iterations);
        assert_eq!(s.intern_num(5), result_expr);
    }

    #[test]
    fn outer_evaluate_let_simple() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(let* ((a 1)) a)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(3, iterations);
        assert_eq!(s.intern_num(1), result_expr);
    }

    #[test]
    fn outer_evaluate_empty_let_bug() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(let* () (+ 1 2))").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(4, iterations);
        assert_eq!(s.intern_num(3), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(10, iterations);
        assert_eq!(s.intern_num(3), result_expr);
    }

    #[test]
    fn outer_evaluate_letstar_parallel_binding() {
        let mut s = Store::default();
        let limit = 20;
        let expr = s.read("(let* ((a 1) (b a)) b)").unwrap();

        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(5, iterations);
        assert_eq!(s.intern_num(1), result_expr);
    }

    #[test]
    fn outer_evaluate_arithmetic_let() {
        let mut s = Store::default();
        let limit = 100;
        let expr = s
            .read(
                "(let* ((a 5)
                        (b 1)
                        (c 2))
                   (/ (+ a b) c))",
            )
            .unwrap();

        let (result_expr, new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(18, iterations);
        assert_eq!(s.intern_num(3), result_expr);

        assert!(new_env.is_nil());
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
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(35, iterations);
            assert_eq!(s.intern_num(5), result_expr);
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
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(32, iterations);
            assert_eq!(s.intern_num(6), result_expr);
        }
    }

    #[test]
    fn outer_evaluate_if() {
        let limit = 100;
        {
            let mut s = Store::default();
            let expr = s.read("(if t 5 6)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(3, iterations);
            assert_eq!(s.intern_num(5), result_expr);
        }
        {
            let mut s = Store::default();
            let expr = s.read("(if nil 5 6)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(3, iterations);
            assert_eq!(s.intern_num(6), result_expr);
        }
    }

    #[test]
    fn outer_evaluate_fully_evaluates() {
        let limit = 100;
        {
            let mut s = Store::default();
            let expr = s.read("(if t (+ 5 5) 6)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(5, iterations);
            assert_eq!(s.intern_num(10), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(91, iterations);
        assert_eq!(s.intern_num(125), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(201, iterations);
        assert_eq!(s.intern_num(3125), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(95, iterations);
        assert_eq!(s.intern_num(125), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(75, iterations);
        assert_eq!(s.intern_num(125), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(129, iterations);
        assert_eq!(s.intern_num(125), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(110, iterations);
        assert_eq!(s.intern_num(125), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(22, iterations);
        assert_eq!(s.intern_num(13), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(31, iterations);
        assert_eq!(s.intern_num(11), result_expr);
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
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();
        assert_eq!(242, iterations);
        assert_eq!(s.intern_num(33), result_expr);
    }

    #[test]
    fn outer_evaluate_eq() {
        {
            let mut s = Store::default();
            let limit = 20;
            let expr = s.read("(eq 'a 'a)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(3, iterations);
            assert_eq!(s.intern_sym("T"), result_expr);
        }
        {
            let mut s = Store::default();
            let limit = 20;
            let expr = s.read("(eq 'a 1)").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(3, iterations);
            assert!(result_expr.is_nil());
        }
    }

    #[test]
    fn outer_evaluate_zero_arg_lambda() {
        {
            let mut s = Store::default();
            let limit = 20;
            let expr = s.read("((lambda () 123))").unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(4, iterations);
            assert_eq!(s.intern_num(123), result_expr);
        }
        {
            let mut s = Store::default();
            let limit = 20;
            let expr = s
                .read("(letrec* ((x 9) (f (lambda () (+ x 1)))) (f))")
                .unwrap();

            let (result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(14, iterations);
            assert_eq!(s.intern_num(10), result_expr);
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
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(493, iterations);
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
            let (_result_expr, _new_env, iterations, _continuation) =
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

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
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(s.read("((2 . 3) . (4 . 5))").unwrap(), result_expr);

            assert_eq!(170, iterations);
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
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert!(result_expr.is_nil());

            assert_eq!(170, iterations);
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
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert!(result_expr.is_nil());
            assert_eq!(25, iterations);
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
                Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

            assert_eq!(s.intern_num(18), result_expr);
            assert_eq!(22, iterations);
        }
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

        let mut s = Store::default();
        let limit = 1000000;
        let expr = s
            .read(
                r#"
(let* ((foo (lambda (a b)
              (letrec* ((aux (lambda (i a x)
                               (if (= i b)
                                     x
                                     (let* ((x (+ x a))
                                            (a (+ a (* b 2))))
                                       (aux (+ i 1) a x))))))
                       (let* ((x (+ (* a b) 4)))
                         (aux 0 a x))))))
  (foo 10 16))
"#,
            )
            .unwrap();
        let (result_expr, _new_env, iterations, _continuation) =
            Evaluator::new(expr, empty_sym_env(&s), &mut s, limit).eval();

        assert_eq!(s.intern_num(0x1044), result_expr);
        assert_eq!(1114, iterations);
    }
}
