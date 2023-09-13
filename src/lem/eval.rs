use anyhow::Result;
use once_cell::sync::OnceCell;

use crate::{field::LurkField, func, state::initial_lurk_state, tag::ContTag::*};

use super::{interpreter::Frame, pointers::Ptr, store::Store, Func, Tag};

static EVAL_STEP: OnceCell<Func> = OnceCell::new();

/// Lurk's step function
pub fn eval_step() -> &'static Func {
    EVAL_STEP.get_or_init(|| {
        let reduce = reduce();
        let apply_cont = apply_cont();
        let make_thunk = make_thunk();

        func!(step(expr, env, cont): 3 => {
            let (expr, env, cont, ctrl) = reduce(expr, env, cont);
            let (expr, env, cont, ctrl) = apply_cont(expr, env, cont, ctrl);
            let (expr, env, cont, _ctrl) = make_thunk(expr, env, cont, ctrl);
            return (expr, env, cont)
        })
    })
}

pub fn evaluate_with_env_and_cont<F: LurkField>(
    expr: Ptr<F>,
    env: Ptr<F>,
    cont: Ptr<F>,
    store: &mut Store<F>,
    limit: usize,
) -> Result<(Vec<Frame<F>>, usize)> {
    let stop_cond = |output: &[Ptr<F>]| {
        output[2] == Ptr::null(Tag::Cont(Terminal)) || output[2] == Ptr::null(Tag::Cont(Error))
    };
    let state = initial_lurk_state();
    let log_fmt = |i: usize, inp: &[Ptr<F>], emit: &[Ptr<F>], store: &Store<F>| {
        let mut out = format!(
            "Frame: {i}\n\tExpr: {}\n\tEnv:  {}\n\tCont: {}",
            inp[0].fmt_to_string(store, state),
            inp[1].fmt_to_string(store, state),
            inp[2].fmt_to_string(store, state)
        );
        if let Some(ptr) = emit.first() {
            out.push_str(&format!("\n\tEmtd: {}", ptr.fmt_to_string(store, state)));
        }
        out
    };

    let input = &[expr, env, cont];
    let (frames, iterations, _) =
        eval_step().call_until(input, store, stop_cond, limit, log_fmt)?;
    Ok((frames, iterations))
}

pub fn evaluate<F: LurkField>(
    expr: Ptr<F>,
    store: &mut Store<F>,
    limit: usize,
) -> Result<(Vec<Frame<F>>, usize)> {
    evaluate_with_env_and_cont(
        expr,
        store.intern_nil(),
        Ptr::null(Tag::Cont(Outermost)),
        store,
        limit,
    )
}

pub fn evaluate_simple<F: LurkField>(
    expr: Ptr<F>,
    store: &mut Store<F>,
    limit: usize,
) -> Result<(Vec<Ptr<F>>, usize, Vec<Ptr<F>>)> {
    let stop_cond = |output: &[Ptr<F>]| {
        output[2] == Ptr::null(Tag::Cont(Terminal)) || output[2] == Ptr::null(Tag::Cont(Error))
    };
    let input = vec![expr, store.intern_nil(), Ptr::null(Tag::Cont(Outermost))];
    eval_step().call_until_simple(input, store, stop_cond, limit)
}

fn car_cdr() -> Func {
    func!(car_cdr(xs): 2 => {
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        let empty_str = String("");
        match xs.tag {
            Expr::Nil => {
                return (nil, nil)
            }
            Expr::Cons => {
                let (car, cdr) = decons2(xs);
                return (car, cdr)
            }
            Expr::Str => {
                if xs == empty_str {
                    return (nil, empty_str)
                }
                let (car, cdr) = decons2(xs);
                return (car, cdr)
            }
        }
    })
}

fn reduce() -> Func {
    // Auxiliary functions
    let car_cdr = car_cdr();
    let env_to_use = func!(env_to_use(smaller_env, smaller_rec_env): 1 => {
        match smaller_rec_env.tag {
            Expr::Nil => {
                return (smaller_env)
            }
        };
        let env: Expr::Cons = cons2(smaller_rec_env, smaller_env);
        return (env)
    });
    let extract_arg = func!(extract_arg(args): 2 => {
        match args.tag {
            Expr::Nil => {
                let dummy = Symbol("dummy");
                let nil = Symbol("nil");
                let nil = cast(nil, Expr::Nil);
                return (dummy, nil)
            }
            Expr::Cons => {
                let (arg, rest) = decons2(args);
                return (arg, rest)
            }
        }
    });
    let expand_bindings = func!(expand_bindings(head, body, body1, rest_bindings): 1 => {
        match rest_bindings.tag {
            Expr::Nil => {
                return (body1)
            }
        };
        let expanded_0: Expr::Cons = cons2(rest_bindings, body);
        let expanded: Expr::Cons = cons2(head, expanded_0);
        return (expanded)
    });
    let choose_let_cont = func!(choose_let_cont(head, var, env, expanded, cont): 1 => {
        match symbol head {
            "let" => {
                let cont: Cont::Let = cons4(var, env, expanded, cont);
                return (cont)
            }
            "letrec" => {
                let cont: Cont::LetRec = cons4(var, env, expanded, cont);
                return (cont)
            }
        }
    });
    let is_unop = func!(is_unop(head): 1 => {
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        let t = Symbol("t");
        match symbol head {
            "car", "cdr", "commit", "num", "u64", "comm", "char", "open", "secret", "atom", "emit" => {
                return (t)
            }
        };
        return (nil)
    });

    let is_binop = func!(is_binop(head): 1 => {
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        let t = Symbol("t");
        match symbol head {
            "cons", "strcons", "hide", "+", "-", "*", "/", "%", "=", "eq", "<", ">", "<=", ">=" => {
                return (t)
            }
        };
        return (nil)
    });
    let make_call = func!(make_call(head, rest, env, cont): 4 => {
        let ret: Ctrl::Return;
        match rest.tag {
            Expr::Nil => {
                let cont: Cont::Call0 = cons2(env, cont);
                return (head, env, cont, ret)
            }
            Expr::Cons => {
                let (arg, more_args) = decons2(rest);
                match more_args.tag {
                    Expr::Nil => {
                        let cont: Cont::Call = cons3(arg, env, cont);
                        return (head, env, cont, ret)
                    }
                };
                let nil = Symbol("nil");
                let nil = cast(nil, Expr::Nil);
                let expanded_inner0: Expr::Cons = cons2(arg, nil);
                let expanded_inner: Expr::Cons = cons2(head, expanded_inner0);
                let expanded: Expr::Cons = cons2(expanded_inner, more_args);
                return (expanded, env, cont, ret)
            }
        }
    });
    let is_potentially_fun = func!(is_potentially_fun(head): 1 => {
        let t = Symbol("t");
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        match head.tag {
            Expr::Fun | Expr::Cons | Expr::Thunk => {
                return (t)
            }
        };
        return (nil)
    });

    func!(reduce(expr, env, cont): 4 => {
        // Useful constants
        let ret: Ctrl::Return;
        let apply: Ctrl::ApplyContinuation;
        let errctrl: Ctrl::Error;
        let err: Cont::Error;
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        let t = Symbol("t");

        match cont.tag {
            Cont::Terminal | Cont::Error => {
                return (expr, env, cont, ret)
            }
        };


        match expr.tag {
            Expr::Nil | Expr::Fun | Expr::Num | Expr::Str | Expr::Char | Expr::Comm | Expr::U64 | Expr::Key => {
                return (expr, env, cont, apply)
            }
            Expr::Thunk => {
                let (thunk_expr, thunk_continuation) = decons2(expr);
                return (thunk_expr, env, thunk_continuation, apply)
            }
            Expr::Sym => {
                match symbol expr {
                    "nil", "t" => {
                        return (expr, env, cont, apply)
                    }
                };

                match env.tag {
                    Expr::Nil => {
                        return (expr, env, err, errctrl)
                    }
                };

                let (binding, smaller_env) = car_cdr(env);
                match binding.tag {
                    Expr::Nil => {
                        return (expr, env, err, errctrl)
                    }
                };

                let (var_or_rec_binding, val_or_more_rec_env) =
                    car_cdr(binding);
                match var_or_rec_binding.tag {
                    Expr::Sym => {
                        if var_or_rec_binding == expr {
                            return (val_or_more_rec_env, env, cont, apply)
                        }
                        match cont.tag {
                            Cont::Lookup => {
                                return (expr, smaller_env, cont, ret)
                            }
                        };
                        let cont: Cont::Lookup = cons2(env, cont);
                        return (expr, smaller_env, cont, ret)
                    }
                    Expr::Cons => {
                        let (v2, val2) = car_cdr(var_or_rec_binding);

                        if v2 == expr {
                            match val2.tag {
                                Expr::Fun => {
                                    // if `val2` is a closure, then extend its environment
                                    let (arg, body, closed_env) = decons3(val2);
                                    let extended: Expr::Cons = cons2(binding, closed_env);
                                    // and return the extended closure
                                    let fun: Expr::Fun = cons3(arg, body, extended);
                                    return (fun, env, cont, apply)
                                }
                            };
                            // otherwise return `val2`
                            return (val2, env, cont, apply)
                        }
                        let (env_to_use) = env_to_use(smaller_env, val_or_more_rec_env);

                        match cont.tag {
                            Cont::Lookup => {
                                return (expr, env_to_use, cont, ret)
                            }
                        };
                        let cont: Cont::Lookup = cons2(env, cont);
                        return (expr, env_to_use, cont, ret)
                    }
                };
                return (expr, env, err, errctrl)
            }
            Expr::Cons => {
                // No need for `car_cdr` since the expression is already a `Cons`
                let (head, rest) = decons2(expr);
                match rest.tag {
                    // rest's tag can only be Nil or Cons
                    Expr::Sym | Expr::Fun | Expr::Num | Expr::Thunk | Expr::Str
                    | Expr::Char | Expr::Comm | Expr::U64 | Expr::Key => {
                        return (expr, env, err, errctrl);
                    }
                };
                match head.tag {
                    Expr::Sym => {
                        match symbol head {
                            "lambda" => {
                                let (args, body) = car_cdr(rest);
                                let (arg, cdr_args) = extract_arg(args);

                                match arg.tag {
                                    Expr::Sym => {
                                        match cdr_args.tag {
                                            Expr::Nil => {
                                                let function: Expr::Fun = cons3(arg, body, env);
                                                return (function, env, cont, apply)
                                            }
                                        };
                                        let inner: Expr::Cons = cons2(cdr_args, body);
                                        let l: Expr::Cons = cons2(head, inner);
                                        let inner_body: Expr::Cons = cons2(l, nil);
                                        let function: Expr::Fun = cons3(arg, inner_body, env);
                                        return (function, env, cont, apply)
                                    }
                                };
                                return (expr, env, err, errctrl)
                            }
                            "quote" => {
                                let (quoted, end) = car_cdr(rest);

                                match end.tag {
                                    Expr::Nil => {
                                        return (quoted, env, cont, apply)
                                    }
                                };
                                return (expr, env, err, errctrl)
                            }
                            "let", "letrec" => {
                                let (bindings, body) = car_cdr(rest);
                                let (body1, rest_body) = car_cdr(body);
                                // Only a single body form allowed for now.
                                match body.tag {
                                    Expr::Nil => {
                                        return (expr, env, err, errctrl)
                                    }
                                };
                                match rest_body.tag {
                                    Expr::Nil => {
                                        match bindings.tag {
                                            Expr::Nil => {
                                                return (body1, env, cont, ret)
                                            }
                                        };
                                        let (binding1, rest_bindings) = car_cdr(bindings);
                                        let (var, vals) = car_cdr(binding1);
                                        match var.tag {
                                            Expr::Sym => {
                                                let (val, end) = car_cdr(vals);
                                                match end.tag {
                                                    Expr::Nil => {
                                                        let (expanded) = expand_bindings(head, body, body1, rest_bindings);
                                                        let (cont) = choose_let_cont(head, var, env, expanded, cont);
                                                        return (val, env, cont, ret)
                                                    }
                                                };
                                                return (expr, env, err, errctrl)
                                            }
                                        };
                                        return (expr, env, err, errctrl)
                                    }
                                };
                                return (expr, env, err, errctrl)
                            }
                            "begin" => {
                                let (arg1, more) = car_cdr(rest);
                                match more.tag {
                                    Expr::Nil => {
                                        return (arg1, env, cont, ret)
                                    }
                                };
                                let cont: Cont::Binop = cons4(head, env, more, cont);
                                return (arg1, env, cont, ret)
                            }
                            "eval" => {
                                match rest.tag {
                                    Expr::Nil => {
                                        return (expr, env, err, errctrl)
                                    }
                                };
                                let (arg1, more) = car_cdr(rest);
                                match more.tag {
                                    Expr::Nil => {
                                        let cont: Cont::Unop = cons2(head, cont);
                                        return (arg1, env, cont, ret)
                                    }
                                };
                                let cont: Cont::Binop = cons4(head, env, more, cont);
                                return (arg1, env, cont, ret)
                            }
                            "if" => {
                                let (condition, more) = car_cdr(rest);
                                match more.tag {
                                    Expr::Nil => {
                                        return (expr, env, err, errctrl)
                                    }
                                };
                                let cont: Cont::If = cons2(more, cont);
                                return (condition, env, cont, ret)
                            }
                            "current-env" => {
                                match rest.tag {
                                    Expr::Nil => {
                                        return (env, env, cont, apply)
                                    }
                                };
                                return (expr, env, err, errctrl)
                            }
                        };
                        // unops
                        let (op) = is_unop(head);
                        if op == t {
                            match rest.tag {
                                Expr::Nil => {
                                    return (expr, env, err, errctrl)
                                }
                            };
                            let (arg1, end) = decons2(rest);
                            match end.tag {
                                Expr::Nil => {
                                    let cont: Cont::Unop = cons2(head, cont);
                                    return (arg1, env, cont, ret)
                                }
                            };
                            return (expr, env, err, errctrl)
                        }
                        // binops
                        let (op) = is_binop(head);
                        if op == t {
                            match rest.tag {
                                Expr::Nil => {
                                    return (expr, env, err, errctrl)
                                }
                            };
                            let (arg1, more) = decons2(rest);
                            match more.tag {
                                Expr::Nil => {
                                    return (expr, env, err, errctrl)
                                }
                            };
                            let cont: Cont::Binop = cons4(head, env, more, cont);
                            return (arg1, env, cont, ret)
                        }
                        // just call assuming that the symbol is bound to a function
                        let (fun, env, cont, ret) = make_call(head, rest, env, cont);
                        return (fun, env, cont, ret);
                    }
                };

                // TODO coprocessors (could it be simply a `func`?)
                // head -> fn, rest -> args
                let (potentially_fun) = is_potentially_fun(head);
                if potentially_fun == t {
                    let (fun, env, cont, ret) = make_call(head, rest, env, cont);
                    return (fun, env, cont, ret);
                }
                return (expr, env, err, errctrl)
            }
        }
    })
}

fn apply_cont() -> Func {
    let car_cdr = car_cdr();
    let make_tail_continuation = func!(make_tail_continuation(env, continuation): 1 => {
        match continuation.tag {
            Cont::Tail => {
                return (continuation);
            }
        };
        let tail_continuation: Cont::Tail = cons2(env, continuation);
        return (tail_continuation);
    });

    let extend_rec = func!(extend_rec(env, var, result): 1 => {
        let (binding_or_env, rest) = car_cdr(env);
        let (var_or_binding, _val_or_more_bindings) = car_cdr(binding_or_env);
        let cons: Expr::Cons = cons2(var, result);
        match var_or_binding.tag {
            // It's a var, so we are extending a simple env with a recursive env.
            Expr::Sym | Expr::Nil => {
                let nil = Symbol("nil");
                let nil = cast(nil, Expr::Nil);
                let list: Expr::Cons = cons2(cons, nil);
                let res: Expr::Cons = cons2(list, env);
                return (res)
            }
            // It's a binding, so we are extending a recursive env.
            Expr::Cons => {
                let cons2: Expr::Cons = cons2(cons, binding_or_env);
                let res: Expr::Cons = cons2(cons2, rest);

                return (res)
            }
        }
    });
    // Returns 0u64 if both arguments are U64, 0 (num) if the arguments are some kind of number (either U64 or Num),
    // and nil otherwise
    let args_num_type = func!(args_num_type(arg1, arg2): 1 => {
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        match arg1.tag {
            Expr::Num => {
                match arg2.tag {
                    Expr::Num => {
                        let ret: Expr::Num;
                        return (ret)
                    }
                    Expr::U64 => {
                        let ret: Expr::Num;
                        return (ret)
                    }
                };
                return (nil)
            }
            Expr::U64 => {
                match arg2.tag {
                    Expr::Num => {
                        let ret: Expr::Num;
                        return (ret)
                    }
                    Expr::U64 => {
                        let ret: Expr::U64;
                        return (ret)
                    }
                };
                return (nil)
            }
        };
        return (nil)
    });
    func!(apply_cont(result, env, cont, ctrl): 4 => {
        // Useful constants
        let ret: Ctrl::Return;
        let makethunk: Ctrl::MakeThunk;
        let errctrl: Ctrl::Error;
        let err: Cont::Error;
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        let t = Symbol("t");
        let zero = Num(0);
        let size_u64 = Num(18446744073709551616);
        let empty_str = String("");

        match ctrl.tag {
            Ctrl::ApplyContinuation => {
                match cont.tag {
                    Cont::Terminal | Cont::Error => {
                        return (result, env, cont, ret)
                    }
                    Cont::Outermost => {
                        let cont: Cont::Terminal;
                        return (result, env, cont, ret)
                    }
                    Cont::Emit => {
                        // TODO Does this make sense?
                        let (cont, _rest) = decons2(cont);
                        return (result, env, cont, makethunk)
                    }
                    Cont::Call0 => {
                        let (saved_env, continuation) = decons2(cont);
                        match result.tag {
                            Expr::Fun => {
                                let (arg, body, closed_env) = decons3(result);
                                match symbol arg {
                                    "dummy" => {
                                        match body.tag {
                                            Expr::Nil => {
                                                return (result, env, err, errctrl)
                                            }
                                        };
                                        let (body_form, end) = car_cdr(body);
                                        match end.tag {
                                            Expr::Nil => {
                                                let (cont) = make_tail_continuation(saved_env, continuation);
                                                return (body_form, closed_env, cont, ret)
                                            }
                                        };
                                        return (result, env, err, errctrl)
                                    }
                                };
                                return (result, env, continuation, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Call => {
                        match result.tag {
                            Expr::Fun => {
                                let (unevaled_arg, saved_env, continuation) = decons3(cont);
                                let newer_cont: Cont::Call2 = cons3(result, saved_env, continuation);
                                return (unevaled_arg, env, newer_cont, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Call2 => {
                        let (function, saved_env, continuation) = decons3(cont);
                        match function.tag {
                            Expr::Fun => {
                                let (arg, body, closed_env) = decons3(function);
                                match symbol arg {
                                    "dummy" => {
                                        return (result, env, err, errctrl)
                                    }
                                };
                                match body.tag {
                                    Expr::Nil => {
                                        return (result, env, err, errctrl)
                                    }
                                };
                                let (body_form, end) = decons2(body);
                                match end.tag {
                                    Expr::Nil => {
                                        let binding: Expr::Cons = cons2(arg, result);
                                        let newer_env: Expr::Cons = cons2(binding, closed_env);
                                        let (cont) = make_tail_continuation(saved_env, continuation);
                                        return (body_form, newer_env, cont, ret)
                                    }
                                };
                                return (result, env, err, errctrl)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Let => {
                        let (var, saved_env, body, cont) = decons4(cont);
                        let binding: Expr::Cons = cons2(var, result);
                        let extended_env: Expr::Cons = cons2(binding, env);
                        let (cont) = make_tail_continuation(saved_env, cont);
                        return (body, extended_env, cont, ret)
                    }
                    Cont::LetRec => {
                        let (var, saved_env, body, cont) = decons4(cont);
                        let (extended_env) = extend_rec(env, var, result);
                        let (cont) = make_tail_continuation(saved_env, cont);
                        return (body, extended_env, cont, ret)
                    }
                    Cont::Unop => {
                        let (operator, continuation) = decons2(cont);
                        match symbol operator {
                            "car" => {
                                // Almost like car_cdr, except it returns
                                // an error in case it can't unhash it
                                match result.tag {
                                    Expr::Nil => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                    Expr::Cons => {
                                        let (car, _cdr) = decons2(result);
                                        return (car, env, continuation, makethunk)
                                    }
                                    Expr::Str => {
                                        if result == empty_str {
                                            return (nil, env, continuation, makethunk)
                                        }
                                        let (car, _cdr) = decons2(result);
                                        return (car, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            "cdr" => {
                                match result.tag {
                                    Expr::Nil => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                    Expr::Cons => {
                                        let (_car, cdr) = decons2(result);
                                        return (cdr, env, continuation, makethunk)
                                    }
                                    Expr::Str => {
                                        if result == empty_str {
                                            return (empty_str, env, continuation, makethunk)
                                        }
                                        let (_car, cdr) = decons2(result);
                                        return (cdr, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            "atom" => {
                                match result.tag {
                                    Expr::Cons => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                };
                                return (t, env, continuation, makethunk)
                            }
                            "emit" => {
                                // TODO Does this make sense?
                                emit(result);
                                let emit: Cont::Emit = cons2(continuation, nil);
                                return (result, env, emit, makethunk)
                            }
                            "open" => {
                                match result.tag {
                                    Expr::Num => {
                                        let result = cast(result, Expr::Comm);
                                        let (_secret, payload) = open(result);
                                        return(payload, env, continuation, makethunk)
                                    }
                                    Expr::Comm => {
                                        let (_secret, payload) = open(result);
                                        return(payload, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            "secret" => {
                                match result.tag {
                                    Expr::Num => {
                                        let result = cast(result, Expr::Comm);
                                        let (secret, _payload) = open(result);
                                        return(secret, env, continuation, makethunk)
                                    }
                                    Expr::Comm => {
                                        let (secret, _payload) = open(result);
                                        return(secret, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            "commit" => {
                                let comm = hide(zero, result);
                                return(comm, env, continuation, makethunk)
                            }
                            "num" => {
                                match result.tag {
                                    Expr::Num | Expr::Comm | Expr::Char | Expr::U64 => {
                                        let cast = cast(result, Expr::Num);
                                        return(cast, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            "u64" => {
                                match result.tag {
                                    Expr::Num => {
                                        // The limit is 2**64 - 1
                                        let trunc = truncate(result, 64);
                                        let cast = cast(trunc, Expr::U64);
                                        return(cast, env, continuation, makethunk)
                                    }
                                    Expr::U64 => {
                                        return(result, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            "comm" => {
                                match result.tag {
                                    Expr::Num | Expr::Comm => {
                                        let cast = cast(result, Expr::Comm);
                                        return(cast, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            "char" => {
                                match result.tag {
                                    Expr::Num => {
                                        // The limit is 2**32 - 1
                                        let trunc = truncate(result, 32);
                                        let cast = cast(trunc, Expr::Char);
                                        return(cast, env, continuation, makethunk)
                                    }
                                    Expr::Char => {
                                        return(result, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            "eval" => {
                                return(result, nil, continuation, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Binop => {
                        let (operator, saved_env, unevaled_args, continuation) = decons4(cont);
                        let (arg2, rest) = car_cdr(unevaled_args);
                        match symbol operator {
                            "begin" => {
                                match rest.tag {
                                    Expr::Nil => {
                                        return (arg2, saved_env, continuation, ret)
                                    }
                                };
                                let begin_again: Expr::Cons = cons2(operator, unevaled_args);
                                return (begin_again, saved_env, continuation, ctrl)
                            }
                        };
                        match rest.tag {
                            Expr::Nil => {
                                let cont: Cont::Binop2 = cons3(operator, result, continuation);
                                return (arg2, saved_env, cont, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Binop2 => {
                        let (operator, evaled_arg, continuation) = decons3(cont);
                        let (args_num_type) = args_num_type(evaled_arg, result);
                        match symbol operator {
                            "eval" => {
                                return (evaled_arg, result, continuation, ret)
                            }
                            "cons" => {
                                let val: Expr::Cons = cons2(evaled_arg, result);
                                return (val, env, continuation, makethunk)
                            }
                            "strcons" => {
                                match evaled_arg.tag {
                                    Expr::Char => {
                                        match result.tag {
                                            Expr::Str => {
                                                let val: Expr::Str = cons2(evaled_arg, result);
                                                return (val, env, continuation, makethunk)
                                            }
                                        };
                                        return (result, env, err, errctrl)
                                    }
                                };
                                return (result, env, err, errctrl)
                            }
                            "hide" => {
                                match evaled_arg.tag {
                                    Expr::Num => {
                                        let hidden = hide(evaled_arg, result);
                                        return(hidden, env, continuation, makethunk)
                                    }
                                };
                                return (result, env, err, errctrl)
                            }
                            "eq" => {
                                let eq_tag = eq_tag(evaled_arg, result);
                                let eq_val = eq_val(evaled_arg, result);
                                let eq = mul(eq_tag, eq_val);
                                if eq == zero {
                                    return (nil, env, continuation, makethunk)
                                }
                                return (t, env, continuation, makethunk)
                            }
                            "+" => {
                                match args_num_type.tag {
                                    Expr::Nil => {
                                        return (result, env, err, errctrl)
                                    }
                                    Expr::Num => {
                                        let val = add(evaled_arg, result);
                                        return (val, env, continuation, makethunk)
                                    }
                                    Expr::U64 => {
                                        let val = add(evaled_arg, result);
                                        let not_overflow = lt(val, size_u64);
                                        if not_overflow == zero {
                                            let val = sub(val, size_u64);
                                            let val = cast(val, Expr::U64);
                                            return (val, env, continuation, makethunk)
                                        }
                                        let val = cast(val, Expr::U64);
                                        return (val, env, continuation, makethunk)
                                    }
                                }
                            }
                            "-" => {
                                match args_num_type.tag {
                                    Expr::Nil => {
                                        return (result, env, err, errctrl)
                                    }
                                    Expr::Num => {
                                        let val = sub(evaled_arg, result);
                                        return (val, env, continuation, makethunk)
                                    }
                                    Expr::U64 => {
                                        // Subtraction in U64 is almost the same as subtraction
                                        // in the field. If the difference is negative, we need
                                        // to add 2^64 to get back to U64 domain.
                                        let val = sub(evaled_arg, result);
                                        let is_neg = lt(val, zero);
                                        if is_neg == zero {
                                            let val = cast(val, Expr::U64);
                                            return (val, env, continuation, makethunk)
                                        }
                                        let val = add(val, size_u64);
                                        let val = cast(val, Expr::U64);
                                        return (val, env, continuation, makethunk)
                                    }
                                }
                            }
                            "*" => {
                                match args_num_type.tag {
                                    Expr::Nil => {
                                        return (result, env, err, errctrl)
                                    }
                                    Expr::Num => {
                                        let val = mul(evaled_arg, result);
                                        return (val, env, continuation, makethunk)
                                    }
                                    Expr::U64 => {
                                        let val = mul(evaled_arg, result);
                                        // The limit is 2**64 - 1
                                        let trunc = truncate(val, 64);
                                        let cast = cast(trunc, Expr::U64);
                                        return (cast, env, continuation, makethunk)
                                    }
                                }
                            }
                            "/" => {
                                let is_z = eq_val(result, zero);
                                if is_z == zero {
                                    match args_num_type.tag {
                                        Expr::Nil => {
                                            return (result, env, err, errctrl)
                                        }
                                        Expr::Num => {
                                            let val = div(evaled_arg, result);
                                            return (val, env, continuation, makethunk)
                                        }
                                        Expr::U64 => {
                                            let (div, _rem) = div_rem64(evaled_arg, result);
                                            let div = cast(div, Expr::U64);
                                            return (div, env, continuation, makethunk)
                                        }
                                    }
                                }
                                return (result, env, err, errctrl)
                            }
                            "%" => {
                                let is_z = eq_val(result, zero);
                                if is_z == zero {
                                    match args_num_type.tag {
                                        Expr::U64 => {
                                            let (_div, rem) = div_rem64(evaled_arg, result);
                                            let rem = cast(rem, Expr::U64);
                                            return (rem, env, continuation, makethunk)
                                        }
                                    };
                                    return (result, env, err, errctrl)
                                }
                                return (result, env, err, errctrl)
                            }
                            "=" => {
                                match args_num_type.tag {
                                    Expr::Nil => {
                                        return (result, env, err, errctrl)
                                    }
                                };
                                let eq = eq_val(evaled_arg, result);
                                if eq == zero {
                                    return (nil, env, continuation, makethunk)
                                }
                                return (t, env, continuation, makethunk)
                            }
                            "<" => {
                                let val = lt(evaled_arg, result);
                                if val == zero {
                                    return (nil, env, continuation, makethunk)
                                }
                                return (t, env, continuation, makethunk)
                            }
                            ">" => {
                                let val = lt(result, evaled_arg);
                                if val == zero {
                                    return (nil, env, continuation, makethunk)
                                }
                                return (t, env, continuation, makethunk)
                            }
                            "<=" => {
                                let val = lt(result, evaled_arg);
                                if val == zero {
                                    return (t, env, continuation, makethunk)
                                }
                                return (nil, env, continuation, makethunk)
                            }
                            ">=" => {
                                let val = lt(evaled_arg, result);
                                if val == zero {
                                    return (t, env, continuation, makethunk)
                                }
                                return (nil, env, continuation, makethunk)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::If => {
                        let (unevaled_args, continuation) = decons2(cont);
                        let (arg1, more) = car_cdr(unevaled_args);
                        let (arg2, end) = car_cdr(more);
                        match end.tag {
                            Expr::Nil => {
                                match result.tag {
                                    Expr::Nil => {
                                        return (arg2, env, continuation, ret)
                                    }
                                };
                                return (arg1, env, continuation, ret)
                            }
                        };
                        return (arg1, env, err, errctrl)
                    }
                    Cont::Lookup => {
                        let (saved_env, continuation) = decons2(cont);
                        return (result, saved_env, continuation, makethunk)
                    }
                    Cont::Tail => {
                        let (saved_env, continuation) = decons2(cont);
                        return (result, saved_env, continuation, makethunk)
                    }
                }
            }
        };
        return (result, env, cont, ctrl)
    })
}

fn make_thunk() -> Func {
    func!(make_thunk(expr, env, cont, ctrl): 4 => {
        let ret: Ctrl::Return;
        match ctrl.tag {
            Ctrl::MakeThunk => {
                match cont.tag {
                    Cont::Tail => {
                        let (saved_env, saved_cont) = decons2(cont);
                        let thunk: Expr::Thunk = cons2(expr, saved_cont);
                        let cont: Cont::Dummy;
                        return (thunk, saved_env, cont, ret)
                    }
                    Cont::Outermost => {
                        let cont: Cont::Terminal;
                        return (expr, env, cont, ret)
                    }
                };
                let thunk: Expr::Thunk = cons2(expr, cont);
                let cont: Cont::Dummy;
                return (thunk, env, cont, ret)
            }
        };
        return (expr, env, cont, ctrl)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lem::{pointers::Ptr, slot::SlotsCounter, store::Store, Tag},
        state::State,
    };
    use bellpepper_core::{test_cs::TestConstraintSystem, Comparable, Delta};
    use blstrs::Scalar as Fr;

    const NUM_INPUTS: usize = 1;
    const NUM_AUX: usize = 10744;
    const NUM_CONSTRAINTS: usize = 13299;
    const NUM_SLOTS: SlotsCounter = SlotsCounter {
        hash4: 16,
        hash6: 4,
        hash8: 2,
        commitment: 1,
        less_than: 1,
    };

    fn test_eval_and_constrain_aux(
        eval_step: &Func,
        store: &mut Store<Fr>,
        pairs: Vec<(Ptr<Fr>, Ptr<Fr>)>,
    ) {
        assert_eq!(eval_step.slot, NUM_SLOTS);

        let computed_num_constraints = eval_step.num_constraints::<Fr>(store);

        let mut all_paths = vec![];

        // Auxiliary Lurk constants
        let outermost = Ptr::null(Tag::Cont(Outermost));
        let terminal = Ptr::null(Tag::Cont(Terminal));
        let error = Ptr::null(Tag::Cont(Error));
        let nil = store.intern_nil();

        // Stop condition: the continuation is either terminal or error
        let stop_cond = |output: &[Ptr<Fr>]| output[2] == terminal || output[2] == error;

        let log_fmt = |_: usize, _: &[Ptr<Fr>], _: &[Ptr<Fr>], _: &Store<Fr>| String::default();

        let limit = 10000;

        let mut cs_prev = None;
        for (expr_in, expr_out) in pairs {
            let input = [expr_in, nil, outermost];
            let (frames, _, paths) = eval_step
                .call_until(&input, store, stop_cond, limit, log_fmt)
                .unwrap();
            let last_frame = frames.last().expect("eval should add at least one frame");
            assert_eq!(last_frame.output[0], expr_out);
            store.hydrate_z_cache();
            for frame in frames.iter() {
                let mut cs = TestConstraintSystem::<Fr>::new();
                eval_step
                    .synthesize_frame_aux(&mut cs, store, frame)
                    .unwrap();
                assert!(cs.is_satisfied());
                assert_eq!(cs.num_inputs(), NUM_INPUTS);
                assert_eq!(cs.aux().len(), NUM_AUX);

                let num_constraints = cs.num_constraints();
                assert_eq!(computed_num_constraints, num_constraints);
                assert_eq!(num_constraints, NUM_CONSTRAINTS);

                if let Some(cs_prev) = cs_prev {
                    // Check for all input expresssions that all frames are uniform.
                    assert_eq!(cs.delta(&cs_prev, true), Delta::Equal);
                }
                cs_prev = Some(cs);
            }
            all_paths.extend(paths);
        }

        // TODO do we really need this?
        // eval_step.assert_all_paths_taken(&all_paths);
    }

    fn expr_in_expr_out_pairs(s: &mut Store<Fr>) -> Vec<(Ptr<Fr>, Ptr<Fr>)> {
        let state = State::init_lurk_state().rccell();
        let mut read = |code: &str| s.read(state.clone(), code).unwrap();
        let div = read("(/ 70u64 8u64)");
        let div_res = read("8u64");
        let rem = read("(% 70u64 8u64)");
        let rem_res = read("6u64");
        let u64_1 = read("(u64 100000000)");
        let u64_1_res = read("100000000u64");
        let u64_2 = read("(u64 1000000000000000000000000)");
        let u64_2_res = read("2003764205206896640u64");
        let mul_overflow = read("(* 1000000000000u64 100000000000000u64)");
        let mul_overflow_res = read("15908979783594147840u64");
        let char_conv = read("(char 97)");
        let char_conv_res = read("'a'");
        let char_overflow = read("(char 4294967393)");
        let char_overflow_res = read("'a'");
        let t = read("t");
        let nil = read("nil");
        let le1 = read("(<= 4 8)");
        let le2 = read("(<= 8 8)");
        let le3 = read("(<= 10 8)");
        let gt1 = read("(> 4 8)");
        let gt2 = read("(> 8 8)");
        let gt3 = read("(> 10 8)");
        let ltz = read("(< (- 0 10) 0)");
        let sum = read("(+ 21 21)");
        let sum_res = read("42");
        let car = read("(car (cons 1 2))");
        let car_res = read("1");
        let let_ = read(
            "(let ((x (cons 1 2)))
                (cons (car x) (cdr x)))",
        );
        let let_res = read("(1 . 2)");
        let lam0 = read("((lambda () 1))");
        let lam0_res = read("1");
        let lam = read("((lambda (x y) (+ x y)) 3 4)");
        let lam_res = read("7");
        let fold = read(
            "(letrec ((build (lambda (x)
                                (if (eq x 0)
                                    nil
                                (cons x (build (- x 1))))))
                    (sum (lambda (xs)
                            (if (eq xs nil)
                                0
                                (+ (car xs) (sum (cdr xs)))))))
                (sum (build 4)))",
        );
        let fold_res = read("10");
        vec![
            (div, div_res),
            (rem, rem_res),
            (u64_1, u64_1_res),
            (u64_2, u64_2_res),
            (mul_overflow, mul_overflow_res),
            (char_conv, char_conv_res),
            (char_overflow, char_overflow_res),
            (le1, t),
            (le2, t),
            (le3, nil),
            (gt1, nil),
            (gt2, nil),
            (gt3, t),
            (ltz, t),
            (sum, sum_res),
            (car, car_res),
            (let_, let_res),
            (lam0, lam0_res),
            (lam, lam_res),
            (fold, fold_res),
        ]
    }

    #[test]
    fn test_pairs() {
        let step_fn = eval_step();
        let store = &mut step_fn.init_store();
        let pairs = expr_in_expr_out_pairs(store);
        store.hydrate_z_cache();
        test_eval_and_constrain_aux(step_fn, store, pairs);
    }
}
