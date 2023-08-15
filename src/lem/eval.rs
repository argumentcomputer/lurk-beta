use crate::func;

use super::Func;

/// Lurk's step function
#[allow(dead_code)]
pub(crate) fn eval_step() -> Func {
    let reduce = reduce();
    let apply_cont = apply_cont();
    let make_thunk = make_thunk();

    func!(step(expr, env, cont): 3 => {
        let (expr, env, cont, ctrl) = reduce(expr, env, cont);
        let (expr, env, cont, ctrl) = apply_cont(expr, env, cont, ctrl);
        let (expr, env, cont, _ctrl) = make_thunk(expr, env, cont, ctrl);
        return (expr, env, cont)
    })
}

fn safe_uncons() -> Func {
    func!(safe_uncons(xs): 2 => {
        let nil: Expr::Nil;
        let nilstr = Symbol("");
        match xs.tag {
            Expr::Nil => {
                return (nil, nil)
            }
            Expr::Cons => {
                let (car, cdr) = unhash2(xs);
                return (car, cdr)
            }
            Expr::Str => {
                if xs == nilstr {
                    return (nil, nilstr)
                }
                let (car, cdr) = unhash2(xs);
                return (car, cdr)
            }
        }
    })
}

fn reduce() -> Func {
    // Auxiliary functions
    let safe_uncons = safe_uncons();
    let env_to_use = func!(env_to_use(smaller_env, smaller_rec_env): 1 => {
        match smaller_rec_env.tag {
            Expr::Nil => {
                return (smaller_env)
            }
        };
        let env: Expr::Cons = hash2(smaller_rec_env, smaller_env);
        return (env)
    });
    let extract_arg = func!(extract_arg(args): 2 => {
        match args.tag {
            Expr::Nil => {
                let dummy = Symbol("dummy");
                let nil: Expr::Nil;
                return (dummy, nil)
            }
            Expr::Cons => {
                let (arg, rest) = unhash2(args);
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
        let expanded_0: Expr::Cons = hash2(rest_bindings, body);
        let expanded: Expr::Cons = hash2(head, expanded_0);
        return (expanded)
    });
    let choose_let_cont = func!(choose_let_cont(head, var, env, expanded, cont): 1 => {
        match head.val {
            Symbol("let") => {
                let cont: Cont::Let = hash4(var, env, expanded, cont);
                return (cont)
            }
            Symbol("letrec") => {
                let cont: Cont::LetRec = hash4(var, env, expanded, cont);
                return (cont)
            }
        }
    });
    let is_unop = func!(is_unop(head): 1 => {
        let nil: Expr::Nil;
        let t = Symbol("t");
        match head.val {
            Symbol("car")
            | Symbol("cdr")
            | Symbol("commit")
            | Symbol("num")
            | Symbol("u64")
            | Symbol("comm")
            | Symbol("char")
            | Symbol("open")
            | Symbol("secret")
            | Symbol("atom")
            | Symbol("emit") => {
                return (t)
            }
        };
        return (nil)
    });

    let is_binop = func!(is_binop(head): 1 => {
        let nil: Expr::Nil;
        let t = Symbol("t");
        match head.val {
            Symbol("cons")
            | Symbol("strcons")
            | Symbol("hide")
            | Symbol("+")
            | Symbol("-")
            | Symbol("*")
              // TODO: bellperson complains if we use "/"
            | Symbol("div")
            | Symbol("%")
            | Symbol("=")
            | Symbol("eq")
            | Symbol("<")
            | Symbol(">")
            | Symbol("<=")
            | Symbol(">=") => {
                return (t)
            }
        };
        return (nil)
    });
    let is_potentially_fun = func!(is_potentially_fun(head): 1 => {
        let t = Symbol("t");
        let nil: Expr::Nil;
        match head.tag {
            Expr::Fun | Expr::Cons | Expr::Sym | Expr::Thunk => {
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
        let nil: Expr::Nil;
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
                let (thunk_expr, thunk_continuation) = unhash2(expr);
                return (thunk_expr, env, thunk_continuation, apply)
            }
            Expr::Sym => {
                match expr.val {
                    Symbol("nil") | Symbol("t") => {
                        return (expr, env, cont, apply)
                    }
                };

                match env.tag {
                    Expr::Nil => {
                        return (expr, env, err, errctrl)
                    }
                };

                let (binding, smaller_env) = safe_uncons(env);
                match binding.tag {
                    Expr::Nil => {
                        return (expr, env, err, errctrl)
                    }
                };

                let (var_or_rec_binding, val_or_more_rec_env) =
                    safe_uncons(binding);
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
                        let cont: Cont::Lookup = hash2(env, cont);
                        return (expr, smaller_env, cont, ret)
                    }
                    Expr::Cons => {
                        let (v2, val2) = safe_uncons(var_or_rec_binding);

                        if v2 == expr {
                            match val2.tag {
                                Expr::Fun => {
                                    // if `val2` is a closure, then extend its environment
                                    let (arg, body, closed_env) = unhash3(val2);
                                    let extended: Expr::Cons = hash2(binding, closed_env);
                                    // and return the extended closure
                                    let fun: Expr::Fun = hash3(arg, body, extended);
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
                        let cont: Cont::Lookup = hash2(env, cont);
                        return (expr, env_to_use, cont, ret)
                    }
                }
            }
            Expr::Cons => {
                // No need for `safe_uncons` since the expression is already a `Cons`
                let (head, rest) = unhash2(expr);
                match head.val {
                    Symbol("lambda") => {
                        let (args, body) = safe_uncons(rest);
                        let (arg, cdr_args) = extract_arg(args);

                        match arg.tag {
                            Expr::Sym => {
                                match cdr_args.tag {
                                    Expr::Nil => {
                                        let function: Expr::Fun = hash3(arg, body, env);
                                        return (function, env, cont, apply)
                                    }
                                };
                                let inner: Expr::Cons = hash2(cdr_args, body);
                                let lambda = Symbol("lambda");
                                let l: Expr::Cons = hash2(lambda, inner);
                                let inner_body: Expr::Cons = hash2(l, nil);
                                let function: Expr::Fun = hash3(arg, inner_body, env);
                                return (function, env, cont, apply)
                            }
                        };
                        return (expr, env, err, errctrl)
                    }
                    Symbol("quote") => {
                        let (quoted, end) = safe_uncons(rest);

                        match end.tag {
                            Expr::Nil => {
                                return (quoted, env, cont, apply)
                            }
                        };
                        return (expr, env, err, errctrl)
                    }
                    Symbol("let") | Symbol("letrec") => {
                        let (bindings, body) = safe_uncons(rest);
                        let (body1, rest_body) = safe_uncons(body);
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
                                let (binding1, rest_bindings) = safe_uncons(bindings);
                                let (var, vals) = safe_uncons(binding1);
                                match var.tag {
                                    Expr::Sym => {
                                        let (val, end) = safe_uncons(vals);
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
                    Symbol("begin") => {
                        let (arg1, more) = safe_uncons(rest);
                        match more.tag {
                            Expr::Nil => {
                                return (arg1, env, cont, ret)
                            }
                        };
                        let cont: Cont::Binop = hash4(head, env, more, cont);
                        return (arg1, env, cont, ret)
                    }
                    Symbol("eval") => {
                        match rest.tag {
                            Expr::Nil => {
                                return (expr, env, err, errctrl)
                            }
                        };
                        let (arg1, more) = safe_uncons(rest);
                        match more.tag {
                            Expr::Nil => {
                                let cont: Cont::Unop = hash2(head, cont);
                                return (arg1, env, cont, ret)
                            }
                        };
                        let cont: Cont::Binop = hash4(head, env, more, cont);
                        return (arg1, env, cont, ret)
                    }
                    Symbol("if") => {
                        let (condition, more) = safe_uncons(rest);
                        match more.tag {
                            Expr::Nil => {
                                return (condition, env, err, errctrl)
                            }
                        };
                        let cont: Cont::If = hash2(more, cont);
                        return (condition, env, cont, ret)
                    }
                    Symbol("current-env") => {
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
                    let (arg1, end) = unhash2(rest);
                    match end.tag {
                        Expr::Nil => {
                            let cont: Cont::Unop = hash2(head, cont);
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
                    let (arg1, more) = unhash2(rest);
                    match more.tag {
                        Expr::Nil => {
                            return (expr, env, err, errctrl)
                        }
                    };
                    let cont: Cont::Binop = hash4(head, env, more, cont);
                    return (arg1, env, cont, ret)
                }

                // TODO coprocessors (could it be simply a `func`?)
                // head -> fn, rest -> args
                let (potentially_fun) = is_potentially_fun(head);
                if potentially_fun == t {
                    match rest.tag {
                        Expr::Nil => {
                            let cont: Cont::Call0 = hash2(env, cont);
                            return (head, env, cont, ret)
                        }
                        Expr::Cons => {
                            let (arg, more_args) = unhash2(rest);
                            match more_args.tag {
                                Expr::Nil => {
                                    let cont: Cont::Call = hash3(arg, env, cont);
                                    return (head, env, cont, ret)
                                }
                            };
                            let expanded_inner0: Expr::Cons = hash2(arg, nil);
                            let expanded_inner: Expr::Cons = hash2(head, expanded_inner0);
                            let expanded: Expr::Cons = hash2(expanded_inner, more_args);
                            return (expanded, env, cont, ret)
                        }
                    }
                }
                return (expr, env, err, errctrl)
            }
        }
    })
}

fn apply_cont() -> Func {
    let safe_uncons = safe_uncons();
    let make_tail_continuation = func!(make_tail_continuation(env, continuation): 1 => {
        match continuation.tag {
            Cont::Tail => {
                return (continuation);
            }
        };
        let tail_continuation: Cont::Tail = hash2(env, continuation);
        return (tail_continuation);
    });

    let extend_rec = func!(extend_rec(env, var, result): 1 => {
        let (binding_or_env, rest) = safe_uncons(env);
        let (var_or_binding, _val_or_more_bindings) = safe_uncons(binding_or_env);
        let cons: Expr::Cons = hash2(var, result);
        match var_or_binding.tag {
            // It's a var, so we are extending a simple env with a recursive env.
            Expr::Sym | Expr::Nil => {
                let nil: Expr::Nil;
                let list: Expr::Cons = hash2(cons, nil);
                let res: Expr::Cons = hash2(list, env);
                return (res)
            }
            // It's a binding, so we are extending a recursive env.
            Expr::Cons => {
                let cons2: Expr::Cons = hash2(cons, binding_or_env);
                let res: Expr::Cons = hash2(cons2, rest);

                return (res)
            }
        }
    });
    func!(apply_cont(result, env, cont, ctrl): 4 => {
        // Useful constants
        let ret: Ctrl::Return;
        let makethunk: Ctrl::MakeThunk;
        let errctrl: Ctrl::Error;
        let err: Cont::Error;
        let nil: Expr::Nil;
        let t = Symbol("t");

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
                        emit(result);
                        // TODO Does this make sense?
                        let (cont, _rest) = unhash2(cont);
                        return (result, env, cont, makethunk)
                    }
                    Cont::Call0 => {
                        let (saved_env, continuation) = unhash2(cont);
                        match result.tag {
                            Expr::Fun => {
                                let (arg, body, closed_env) = unhash3(result);
                                match arg.val {
                                    Symbol("dummy") => {
                                        match body.tag {
                                            Expr::Nil => {
                                                return (result, env, err, errctrl)
                                            }
                                        };
                                        let (body_form, end) = safe_uncons(body);
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
                                let (unevaled_arg, saved_env, continuation) = unhash3(cont);
                                let newer_cont: Cont::Call2 = hash3(result, saved_env, continuation);
                                return (unevaled_arg, env, newer_cont, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Call2 => {
                        let (function, saved_env, continuation) = unhash3(cont);
                        match function.tag {
                            Expr::Fun => {
                                let (arg, body, closed_env) = unhash3(function);
                                match arg.val {
                                    Symbol("dummy") => {
                                        return (result, env, err, errctrl)
                                    }
                                };
                                match body.tag {
                                    Expr::Nil => {
                                        return (result, env, err, errctrl)
                                    }
                                };
                                let (body_form, end) = unhash2(body);
                                match end.tag {
                                    Expr::Nil => {
                                        let binding: Expr::Cons = hash2(arg, result);
                                        let newer_env: Expr::Cons = hash2(binding, closed_env);
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
                        let (var, saved_env, body, cont) = unhash4(cont);
                        let binding: Expr::Cons = hash2(var, result);
                        let extended_env: Expr::Cons = hash2(binding, env);
                        let (cont) = make_tail_continuation(saved_env, cont);
                        return (body, extended_env, cont, ret)
                    }
                    Cont::LetRec => {
                        let (var, saved_env, body, cont) = unhash4(cont);
                        let (extended_env) = extend_rec(env, var, result);
                        let (cont) = make_tail_continuation(saved_env, cont);
                        return (body, extended_env, cont, ret)
                    }
                    Cont::Unop => {
                        let (operator, continuation) = unhash2(cont);
                        match operator.val {
                            Symbol("car") => {
                                let (car, _cdr) = safe_uncons(result);
                                return (car, env, continuation, makethunk)
                            }
                            Symbol("cdr") => {
                                let (_car, cdr) = safe_uncons(result);
                                return (cdr, env, continuation, makethunk)
                            }
                            Symbol("atom") => {
                                match result.tag {
                                    Expr::Cons => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                };
                                return (t, env, continuation, makethunk)
                            }
                            Symbol("emit") => {
                                // TODO Does this make sense?
                                let emit: Cont::Emit = hash2(cont, nil);
                                return (result, env, emit, makethunk)
                            }
                            Symbol("open") => {
                                let (_secret, payload) = open(result);
                                return(payload, env, continuation, makethunk)
                            }
                            Symbol("secret") => {
                                let (secret, _payload) = open(result);
                                return(secret, env, continuation, makethunk)
                            }
                            Symbol("commit") => {
                                let zero = Num(0);
                                let comm = hide(zero, result);
                                return(comm, env, continuation, makethunk)
                            }
                            Symbol("num") => {
                                match result.tag {
                                    Expr::Num | Expr::Comm | Expr::Char | Expr::U64 => {
                                        let cast = cast(result, Expr::Num);
                                        return(cast, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            Symbol("u64") => {
                                match result.tag {
                                    Expr::Num => {
                                        // TODO we also need to use `Mod` to truncate
                                        // But 2^64 is out-of-range of u64, so we will
                                        // maybe use u128
                                        // let limit = Num(18446744073709551616);
                                        let cast = cast(result, Expr::U64);
                                        return(cast, env, continuation, makethunk)
                                    }
                                    Expr::U64 => {
                                        return(result, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            Symbol("comm") => {
                                match result.tag {
                                    Expr::Num | Expr::Comm => {
                                        let cast = cast(result, Expr::Num);
                                        return(cast, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            Symbol("char") => {
                                match result.tag {
                                    Expr::Num | Expr::Char => {
                                        // TODO we also need to use `Mod` to truncate
                                        // let limit = Num(4294967296);
                                        let cast = cast(result, Expr::Num);
                                        return(cast, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            Symbol("eval") => {
                                return(result, nil, continuation, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Binop => {
                        let (operator, saved_env, unevaled_args, continuation) = unhash4(cont);
                        let (arg2, rest) = safe_uncons(unevaled_args);
                        match operator.val {
                            Symbol("begin") => {
                                match rest.tag {
                                    Expr::Nil => {
                                        return (arg2, saved_env, continuation, ret)
                                    }
                                };
                                let begin = Symbol("begin");
                                let begin_again: Expr::Cons = hash2(begin, unevaled_args);
                                return (begin_again, saved_env, continuation, ctrl)
                            }
                        };
                        match rest.tag {
                            Expr::Nil => {
                                let cont: Cont::Binop2 = hash3(operator, result, continuation);
                                return (arg2, saved_env, cont, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Binop2 => {
                        let (operator, evaled_arg, continuation) = unhash3(cont);
                        match operator.val {
                            Symbol("eval") => {
                                return (evaled_arg, result, continuation, ret)
                            }
                            Symbol("cons") => {
                                let val: Expr::Cons = hash2(evaled_arg, result);
                                return (val, env, continuation, makethunk)
                            }
                            Symbol("strcons") => {
                                match evaled_arg.tag {
                                    Expr::Char => {
                                        match evaled_arg.tag {
                                            Expr::Str => {
                                                let val: Expr::Cons = hash2(evaled_arg, result);
                                                return (val, env, continuation, makethunk)
                                            }
                                        };
                                        return (result, env, err, errctrl)
                                    }
                                };
                                return (result, env, err, errctrl)
                            }
                            Symbol("hide") => {
                                let num = cast(evaled_arg, Expr::Num);
                                let hidden = hide(num, result);
                                return(hidden, env, continuation, makethunk)
                            }
                            Symbol("eq") => {
                                // TODO should we check whether the tags are also equal?
                                if evaled_arg == result {
                                    return (t, env, continuation, makethunk)
                                }
                                return (nil, env, continuation, makethunk)
                            }
                            Symbol("+") => {
                                // TODO deal with U64
                                let val = add(evaled_arg, result);
                                return (val, env, continuation, makethunk)
                            }
                            Symbol("-") => {
                                // TODO deal with U64
                                let val = sub(evaled_arg, result);
                                return (val, env, continuation, makethunk)
                            }
                            Symbol("*") => {
                                // TODO deal with U64
                                let val = mul(evaled_arg, result);
                                return (val, env, continuation, makethunk)
                            }
                            Symbol("div") => {
                                // TODO deal with U64
                                let val = div(evaled_arg, result);
                                return (val, env, continuation, makethunk)
                            }
                            Symbol("%") => {
                                // TODO
                                return (result, env, err, errctrl)
                            }
                            Symbol("=") => {
                                // TODO
                                return (result, env, err, errctrl)
                            }
                            Symbol("<") => {
                                let val = lt(evaled_arg, result);
                                match val.val {
                                    Num(0) => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                    Num(1) => {
                                        return (t, env, continuation, makethunk)
                                    }
                                }
                            }
                            Symbol(">") => {
                                let val = lt(result, evaled_arg);
                                match val.val {
                                    Num(0) => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                    Num(1) => {
                                        return (t, env, continuation, makethunk)
                                    }
                                }
                            }
                            Symbol("<=") => {
                                let val = lt(result, evaled_arg);
                                match val.val {
                                    Num(0) => {
                                        return (t, env, continuation, makethunk)
                                    }
                                    Num(1) => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                }
                            }
                            Symbol(">=") => {
                                let val = lt(evaled_arg, result);
                                match val.val {
                                    Num(0) => {
                                        return (t, env, continuation, makethunk)
                                    }
                                    Num(1) => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                }
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::If => {
                        let (unevaled_args, continuation) = unhash2(cont);
                        let (arg1, more) = safe_uncons(unevaled_args);
                        let (arg2, end) = safe_uncons(more);
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
                        return (result, env, err, errctrl)
                    }
                    Cont::Lookup => {
                        let (saved_env, continuation) = unhash2(cont);
                        return (result, saved_env, continuation, makethunk)
                    }
                    Cont::Tail => {
                        let (saved_env, continuation) = unhash2(cont);
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
                        let (saved_env, saved_cont) = unhash2(cont);
                        let thunk: Expr::Thunk = hash2(expr, saved_cont);
                        let cont: Cont::Dummy;
                        return (thunk, saved_env, cont, ret)
                    }
                    Cont::Outermost => {
                        let cont: Cont::Terminal;
                        return (expr, env, cont, ret)
                    }
                };
                let thunk: Expr::Thunk = hash2(expr, cont);
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
    use crate::lem::{pointers::Ptr, slot::SlotsCounter, store::Store, Tag};
    use crate::tag::ContTag::*;
    use bellperson::util_cs::{test_cs::TestConstraintSystem, Comparable};
    use blstrs::Scalar as Fr;

    const NUM_INPUTS: usize = 1;
    const NUM_AUX: usize = 8512;
    const NUM_CONSTRAINTS: usize = 10597;
    const NUM_SLOTS: SlotsCounter = SlotsCounter {
        hash2: 16,
        hash3: 4,
        hash4: 2,
        is_diff_neg: 1,
    };

    fn test_eval_and_constrain_aux(store: &mut Store<Fr>, pairs: Vec<(Ptr<Fr>, Ptr<Fr>)>) {
        let eval_step = eval_step();

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

        for (expr_in, expr_out) in pairs {
            let input = vec![expr_in, nil, outermost];
            let (frames, paths) = eval_step.call_until(input, store, stop_cond).unwrap();
            let last_frame = frames.last().expect("eval should add at least one frame");
            assert_eq!(last_frame.output[0], expr_out);
            store.hydrate_z_cache();
            for frame in frames.iter() {
                let mut cs = TestConstraintSystem::<Fr>::new();
                eval_step.synthesize(&mut cs, store, frame).unwrap();
                assert!(cs.is_satisfied());
                assert_eq!(cs.num_inputs(), NUM_INPUTS);
                assert_eq!(cs.aux().len(), NUM_AUX);

                let num_constraints = cs.num_constraints();
                assert_eq!(computed_num_constraints, num_constraints);
                assert_eq!(num_constraints, NUM_CONSTRAINTS);
                // TODO: assert uniformity with `Delta` from bellperson
            }
            all_paths.extend(paths);
        }

        // TODO do we really need this?
        // eval_step.assert_all_paths_taken(&all_paths);
    }

    fn expr_in_expr_out_pairs(s: &mut Store<Fr>) -> Vec<(Ptr<Fr>, Ptr<Fr>)> {
        let t = s.read("t").unwrap();
        let nil = s.read("nil").unwrap();
        let le1 = s.read("(<= 4 8)").unwrap();
        let le2 = s.read("(<= 8 8)").unwrap();
        let le3 = s.read("(<= 10 8)").unwrap();
        let gt1 = s.read("(> 4 8)").unwrap();
        let gt2 = s.read("(> 8 8)").unwrap();
        let gt3 = s.read("(> 10 8)").unwrap();
        let ltz = s.read("(< (- 0 10) 0)").unwrap();
        let sum = s.read("(+ 21 21)").unwrap();
        let sum_res = s.read("42").unwrap();
        let car = s.read("(car (cons 1 2))").unwrap();
        let car_res = s.read("1").unwrap();
        let let_ = s
            .read(
                "(let ((x (cons 1 2)))
                   (cons (car x) (cdr x)))",
            )
            .unwrap();
        let let_res = s.read("(1 . 2)").unwrap();
        let lam0 = s.read("((lambda () 1))").unwrap();
        let lam0_res = s.read("1").unwrap();
        let lam = s.read("((lambda (x y) (+ x y)) 3 4)").unwrap();
        let lam_res = s.read("7").unwrap();
        let fold = s
            .read(
                "(letrec ((build (lambda (x)
                                             (if (eq x 0)
                                                 nil
                                               (cons x (build (- x 1))))))
                                    (sum (lambda (xs)
                                           (if (eq xs nil)
                                               0
                                             (+ (car xs) (sum (cdr xs)))))))
                             (sum (build 10)))",
            )
            .unwrap();
        let fold_res = s.read("55").unwrap();
        vec![
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
        let mut store = Store::default();
        let pairs = expr_in_expr_out_pairs(&mut store);
        store.hydrate_z_cache();
        test_eval_and_constrain_aux(&mut store, pairs);
    }
}
