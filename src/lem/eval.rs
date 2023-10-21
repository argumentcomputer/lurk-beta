use anyhow::Result;
use indexmap::IndexMap;
use once_cell::sync::OnceCell;

use crate::{
    coprocessor::Coprocessor,
    ctrl,
    eval::lang::Lang,
    field::LurkField,
    func,
    lem::Block,
    op,
    state::initial_lurk_state,
    tag::{
        ContTag::{Error, Outermost, Terminal},
        ExprTag::Cproc,
    },
    Symbol,
};

use super::{
    interpreter::{Frame, Hints},
    pointers::Ptr,
    store::Store,
    Ctrl, Func, Op, Tag, Var,
};

static EVAL_STEP: OnceCell<Func> = OnceCell::new();

/// Cached version of Lurk's default step function (IVC, no coprocessors)
#[inline]
pub fn eval_step() -> &'static Func {
    EVAL_STEP.get_or_init(|| make_eval_step(&[], true))
}

#[inline]
fn get_pc<F: LurkField, C: Coprocessor<F>>(
    expr: &Ptr<F>,
    store: &Store<F>,
    lang: &Lang<F, C>,
) -> usize {
    match expr {
        Ptr::Tuple2(Tag::Expr(Cproc), idx) => {
            let (cproc, _) = store
                .fetch_2_ptrs(*idx)
                .expect("Coprocessor expression is not interned");
            let cproc_sym = store
                .fetch_symbol(cproc)
                .expect("Coprocessor expression is not interned");
            lang.get_index_by_symbol(&cproc_sym)
                .expect("Coprocessor not found")
                + 1
        }
        _ => 0,
    }
}

fn compute_frame<F: LurkField, C: Coprocessor<F>>(
    lurk_step: &Func,
    cprocs_run: &[Func],
    input: &[Ptr<F>],
    store: &Store<F>,
    lang: &Lang<F, C>,
    emitted: &mut Vec<Ptr<F>>,
    pc: usize,
) -> Result<(Frame<F>, bool)> {
    let func = if pc == 0 {
        lurk_step
    } else {
        cprocs_run
            .get(pc - 1)
            .expect("Program counter outside range")
    };
    assert_eq!(func.input_params.len(), input.len());
    let preimages = Hints::new_from_func(func);
    let (frame, _) = func.call(input, store, preimages, emitted, lang, pc)?;
    let must_break = matches!(frame.output[2].tag(), Tag::Cont(Terminal | Error));
    Ok((frame, must_break))
}

// Builds frames for IVC or NIVC scheme
fn build_frames<
    F: LurkField,
    C: Coprocessor<F>,
    LogFmt: Fn(usize, &[Ptr<F>], &[Ptr<F>], &Store<F>) -> String,
>(
    lurk_step: &Func,
    cprocs_run: &[Func],
    mut input: Vec<Ptr<F>>,
    store: &Store<F>,
    limit: usize,
    lang: &Lang<F, C>,
    log_fmt: LogFmt,
) -> Result<(Vec<Frame<F>>, usize)> {
    let mut pc = 0;
    let mut frames = vec![];
    let mut iterations = 0;
    tracing::info!("{}", &log_fmt(0, &input, &[], store));
    for _ in 0..limit {
        let mut emitted = vec![];
        let (frame, must_break) =
            compute_frame(lurk_step, cprocs_run, &input, store, lang, &mut emitted, pc)?;

        iterations += 1;
        input = frame.output.clone();
        tracing::info!("{}", &log_fmt(iterations, &input, &emitted, store));
        let expr = frame.output[0];
        frames.push(frame);

        if must_break {
            break;
        }
        pc = get_pc(&expr, store, lang);
    }
    // TODO: remove this after #729 is merged
    if iterations < limit {
        let frame = lurk_step.call_simple(&input, store, lang, pc)?;
        frames.push(frame);
    }
    Ok((frames, iterations))
}

/// Faster version of `build_frames` that doesn't accumulate frames
fn traverse_frames<F: LurkField, C: Coprocessor<F>>(
    lurk_step: &Func,
    cprocs_run: &[Func],
    mut input: Vec<Ptr<F>>,
    store: &Store<F>,
    limit: usize,
    lang: &Lang<F, C>,
) -> Result<(Vec<Ptr<F>>, usize, Vec<Ptr<F>>)> {
    let mut pc = 0;
    let mut iterations = 0;
    let mut emitted = vec![];
    for _ in 0..limit {
        let (frame, must_break) =
            compute_frame(lurk_step, cprocs_run, &input, store, lang, &mut emitted, pc)?;

        iterations += 1;
        input = frame.output.clone();

        if must_break {
            break;
        }
        pc = get_pc(&frame.output[0], store, lang);
    }
    Ok((input, iterations, emitted))
}

pub fn evaluate_with_env_and_cont<F: LurkField, C: Coprocessor<F>>(
    func_lang: Option<(&Func, &Lang<F, C>)>,
    expr: Ptr<F>,
    env: Ptr<F>,
    cont: Ptr<F>,
    store: &Store<F>,
    limit: usize,
) -> Result<(Vec<Frame<F>>, usize)> {
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

    let input = vec![expr, env, cont];

    match func_lang {
        None => {
            let lang: Lang<F, C> = Lang::new();
            build_frames(eval_step(), &[], input, store, limit, &lang, log_fmt)
        }
        Some((func, lang)) => {
            let funcs = make_cprocs_funcs_from_lang(lang);
            build_frames(func, &funcs, input, store, limit, lang, log_fmt)
        }
    }
}

pub fn evaluate<F: LurkField, C: Coprocessor<F>>(
    func_lang: Option<(&Func, &Lang<F, C>)>,
    expr: Ptr<F>,
    store: &Store<F>,
    limit: usize,
) -> Result<(Vec<Frame<F>>, usize)> {
    evaluate_with_env_and_cont(
        func_lang,
        expr,
        store.intern_nil(),
        Ptr::null(Tag::Cont(Outermost)),
        store,
        limit,
    )
}

pub fn evaluate_simple<F: LurkField, C: Coprocessor<F>>(
    func_lang: Option<(&Func, &Lang<F, C>)>,
    expr: Ptr<F>,
    store: &Store<F>,
    limit: usize,
) -> Result<(Vec<Ptr<F>>, usize, Vec<Ptr<F>>)> {
    let input = vec![expr, store.intern_nil(), Ptr::null(Tag::Cont(Outermost))];
    match func_lang {
        None => {
            let lang: Lang<F, C> = Lang::new();
            traverse_frames(eval_step(), &[], input, store, limit, &lang)
        }
        Some((func, lang)) => {
            let funcs = make_cprocs_funcs_from_lang(lang);
            traverse_frames(func, &funcs, input, store, limit, lang)
        }
    }
}

/// Creates a LEM `Func` corresponding to Lurk's step function from a `Lang`.
/// The `ivc` flag tells whether the generated step function is used for IVC or
/// NIVC. In the IVC case, the step function is capable of reducing calls to the
/// coprocessors present in `Lang` and their circuit will go in the circuit of
/// the step function. In the NIVC case, the step function won't be able to reduce
/// calls to coprocessors and sets up a loop via the `Expr::Cproc` tag, meaning
/// that the reduction must be done from outside.
pub fn make_eval_step_from_lang<F: LurkField, C: Coprocessor<F>>(
    lang: &Lang<F, C>,
    ivc: bool,
) -> Func {
    make_eval_step(
        &lang
            .coprocessors()
            .iter()
            .map(|(s, (c, _))| (s, c.arity()))
            .collect::<Vec<_>>(),
        ivc,
    )
}

fn make_eval_step(cprocs: &[(&Symbol, usize)], ivc: bool) -> Func {
    let reduce = reduce(cprocs);
    let apply_cont = apply_cont(cprocs, ivc);
    let make_thunk = make_thunk();

    func!(step(expr, env, cont): 3 => {
        let (expr, env, cont, ctrl) = reduce(expr, env, cont);
        let (expr, env, cont, ctrl) = apply_cont(expr, env, cont, ctrl);
        let (expr, env, cont) = make_thunk(expr, env, cont, ctrl);
        return (expr, env, cont)
    })
}

fn car_cdr() -> Func {
    func!(car_cdr(xs): 2 => {
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        match xs.tag {
            Expr::Nil => {
                return (nil, nil)
            }
            Expr::Cons => {
                let (car, cdr) = decons2(xs);
                return (car, cdr)
            }
        }
    })
}

/// This `Func` is used to call a standalone coprocessor out of the Lurk's step
/// function. It checks whether the coprocessor expression corresponds the right
/// coprocessor. If it doesn't, return the same input. If it does, destructure
/// the list of arguments and call the coprocessor.
///
/// `run_cproc` is meant to be used in the context of NIVC, when the circuit for
/// each coprocessor is detached from Lurk's universal circuit.
///
/// run_cproc(cproc, env, cont): 3 {
///     let err: Cont::Error;
///     let nil = Symbol("nil");
///     let nil = cast(nil, Expr::Nil);
///     match cproc.tag {
///         Expr::Cproc => {
///             let (cproc_name, evaluated_args) = decons2(cproc);
///             match symbol cproc_name {
///                 // `x` is the name of the coprocessor being called
///                 x => {
///                     // `n` is the arity of the coprocessor `x`
///                     if evaluated_args != nil {
///                         let (x{n-1}, evaluated_args) = car_cdr(evaluated_args);
///                         if evaluated_args != nil {
///                             ...
///                             let (x0, evaluated_args) = car_cdr(evaluated_args);
///                             if evaluated_args == nil {
///                                 Op::Cproc([expr, env, cont], x, [x0, x1, ..., x{n-1}, env, cont]);
///                                 return (expr, env, cont);
///                             }
///                             return (cproc_name, env, err);
///                         }
///                         return (cproc_name, env, err);
///                     }
///                     return (cproc_name, env, err);
///                 }
///             };
///             return (cproc, env, cont);
///         }
///     };
///     return (cproc, env, cont);
/// }
fn run_cproc(cproc_sym: Symbol, arity: usize) -> Func {
    let evaluated_args = Var::new("evaluated_args");
    let expr = Var::new("expr");
    let env = Var::new("env");
    let cont = Var::new("cont");
    let nil = Var::new("nil");
    let is_nil = Var::new("is_nil");
    let cproc = Var::new("cproc");
    let cproc_out = vec![expr.clone(), env.clone(), cont.clone()];
    let func_out = vec![expr, env.clone(), cont.clone()];
    let err_block = Block {
        ops: vec![],
        ctrl: ctrl!(return (cproc_name, env, err)),
    };
    let def_block = Block {
        ops: vec![],
        ctrl: ctrl!(return (cproc, env, err)),
    };
    let mut cproc_inp = (0..arity)
        .map(|i| Var(format!("x{i}").into()))
        .collect::<Vec<_>>();
    cproc_inp.push(env.clone());
    cproc_inp.push(cont.clone());
    let mut block = Block {
        ops: vec![Op::Cproc(cproc_out, cproc_sym.clone(), cproc_inp.clone())],
        ctrl: Ctrl::Return(func_out),
    };
    for (i, cproc_arg) in cproc_inp[0..arity].iter().enumerate() {
        let ops = vec![
            Op::Call(
                vec![cproc_arg.clone(), evaluated_args.clone()],
                Box::new(car_cdr()),
                vec![evaluated_args.clone()],
            ),
            Op::EqVal(is_nil.clone(), evaluated_args.clone(), nil.clone()),
        ];
        block = if i == 0 {
            Block {
                ops,
                ctrl: Ctrl::If(is_nil.clone(), Box::new(block), Box::new(err_block.clone())),
            }
        } else {
            Block {
                ops,
                ctrl: Ctrl::If(is_nil.clone(), Box::new(err_block.clone()), Box::new(block)),
            }
        }
    }

    // MatchSymbol
    let mut match_symbol_map = IndexMap::default();
    match_symbol_map.insert(cproc_sym, block);
    block = Block {
        ops: vec![op!(let (cproc_name, evaluated_args) = decons2(cproc))],
        ctrl: Ctrl::MatchSymbol(
            Var::new("cproc_name"),
            match_symbol_map,
            Some(Box::new(def_block.clone())),
        ),
    };

    // MatchTag
    let mut match_tag_map = IndexMap::default();
    match_tag_map.insert(Tag::Expr(Cproc), block);
    block = Block {
        ops: vec![
            op!(let err: Cont::Error),
            op!(let nil = Symbol("nil")),
            op!(let nil = cast(nil, Expr::Nil)),
        ],
        ctrl: Ctrl::MatchTag(cproc.clone(), match_tag_map, Some(Box::new(def_block))),
    };
    let func_inp = vec![cproc, env, cont];
    Func::new("run_cproc".into(), func_inp, 3, block).unwrap()
}

/// Creates the `Func`s used to call coprocessors in the NIVC scenario. Each
/// coprocessor in the `Lang` will have its own specialized `Func`
pub fn make_cprocs_funcs_from_lang<F: LurkField, C: Coprocessor<F>>(
    lang: &Lang<F, C>,
) -> std::sync::Arc<[Func]> {
    lang.coprocessors()
        .iter()
        .map(|(name, (c, _))| run_cproc(name.clone(), c.arity()))
        .collect()
}

/// Tells whether `head`, which is assumed to be a symbol, corresponds to the name
/// of a coprocessor in the `Lang`.
///
/// is_cproc(head): 1 {
///     let nil = Symbol("nil");
///     let nil = cast(nil, Expr::Nil);
///     let t = Symbol("t");
///     match symbol head {
///         // one arm for each coprocessor in the `Lang`
///         ... => {
///             return (t)
///         }
///     };
///     return (nil)
/// }
fn is_cproc(cprocs: &[(&Symbol, usize)]) -> Func {
    if cprocs.is_empty() {
        func!(is_cproc(_head): 1 => {
            let nil = Symbol("nil");
            let nil = cast(nil, Expr::Nil);
            return (nil);
        })
    } else {
        let head = Var::new("head");
        let ops = vec![
            op!(let nil = Symbol("nil")),
            op!(let nil = cast(nil, Expr::Nil)),
            op!(let t = Symbol("t")),
        ];
        let mut match_symbol_map = IndexMap::default();
        for (cproc, _) in cprocs {
            match_symbol_map.insert(
                (*cproc).clone(),
                Block {
                    ops: vec![],
                    ctrl: ctrl!(return (t)),
                },
            );
        }
        let def = Some(Box::new(Block {
            ops: vec![],
            ctrl: ctrl!(return (nil)),
        }));
        let ctrl = Ctrl::MatchSymbol(head.clone(), match_symbol_map, def);
        Func::new("is_cproc".into(), vec![head], 1, Block { ops, ctrl }).unwrap()
    }
}

/// Checks which coprocessor a name corresponds to, destructures its list of
/// arguments according to its arity and then calls it.
///
/// `match_and_run_cproc` is meant to be used in the context of IVC, when the
/// circuit for each coprocessor goes within Lurk's universal circuit.
///
/// Bonus: destructuring the list of arguments for the coprocessors share
/// allocated slots
///
/// match_and_run_cproc(cproc_name, evaluated_args, env, cont): 4 {
///     let err: Cont::Error;
///     let nil = Symbol("nil");
///     let nil = cast(nil, Expr::Nil);
///     let makethunk = Symbol("make-thunk");
///     let errctrl = Symbol("error");
///     match symbol cproc_name {
///         x => {
///             // `n` is the arity of the coprocessor `x`
///             if evaluated_args != nil {
///                 let (x{n-1}, evaluated_args) = car_cdr(evaluated_args);
///                 if evaluated_args != nil {
///                     ...
///                     let (x0, evaluated_args) = car_cdr(evaluated_args);
///                     if evaluated_args == nil {
///                         Op::Cproc([expr, env, cont], x, [x0, x1, ..., x{n-1}, env, cont]);
///                         return (expr, env, cont, makethunk);
///                     }
///                     return (cproc_name, env, err, errctrl);
///                 }
///                 return (cproc_name, env, err, errctrl);
///             }
///             return (cproc_name, env, err, errctrl);
///         }
///         ...
///     };
///     return (cproc_name, env, err, errctrl);
/// }
fn match_and_run_cproc(cprocs: &[(&Symbol, usize)]) -> Func {
    let cproc_name = Var::new("cproc_name");
    let evaluated_args = Var::new("evaluated_args");
    let expr = Var::new("expr");
    let env = Var::new("env");
    let cont = Var::new("cont");
    let nil = Var::new("nil");
    let is_nil = Var::new("is_nil");
    let cproc_out = vec![expr.clone(), env.clone(), cont.clone()];
    let func_out = vec![expr, env.clone(), cont.clone(), Var::new("makethunk")];
    let err_block = Block {
        ops: vec![],
        ctrl: ctrl!(return (cproc_name, env, err, errctrl)),
    };
    let mut match_symbol_map = IndexMap::default();
    for (cproc, arity) in cprocs {
        let cproc = *cproc;
        let arity = *arity;
        let mut cproc_inp = (0..arity)
            .map(|i| Var(format!("x{i}").into()))
            .collect::<Vec<_>>();
        cproc_inp.push(env.clone());
        cproc_inp.push(cont.clone());
        let mut block = Block {
            ops: vec![Op::Cproc(
                cproc_out.clone(),
                cproc.clone(),
                cproc_inp.clone(),
            )],
            ctrl: Ctrl::Return(func_out.clone()),
        };
        for (i, cproc_arg) in cproc_inp[0..arity].iter().enumerate() {
            let ops = vec![
                Op::Call(
                    vec![cproc_arg.clone(), evaluated_args.clone()],
                    Box::new(car_cdr()),
                    vec![evaluated_args.clone()],
                ),
                Op::EqVal(is_nil.clone(), evaluated_args.clone(), nil.clone()),
            ];
            block = if i == 0 {
                Block {
                    ops,
                    ctrl: Ctrl::If(is_nil.clone(), Box::new(block), Box::new(err_block.clone())),
                }
            } else {
                Block {
                    ops,
                    ctrl: Ctrl::If(is_nil.clone(), Box::new(err_block.clone()), Box::new(block)),
                }
            }
        }
        match_symbol_map.insert(cproc.clone(), block);
    }
    let def = Some(Box::new(err_block));
    let ctrl = Ctrl::MatchSymbol(cproc_name.clone(), match_symbol_map, def);
    let func_inp = vec![cproc_name, evaluated_args, env, cont];
    let ops = vec![
        op!(let err: Cont::Error),
        op!(let nil = Symbol("nil")),
        op!(let nil = cast(nil, Expr::Nil)),
        op!(let makethunk = Symbol("make-thunk")),
        op!(let errctrl = Symbol("error")),
    ];
    Func::new(
        "match_and_run_cproc".into(),
        func_inp,
        4,
        Block { ops, ctrl },
    )
    .unwrap()
}

fn reduce(cprocs: &[(&Symbol, usize)]) -> Func {
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
    let get_unop = func!(get_unop(head): 1 => {
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        match symbol head {
            "car" => {
                let op: Op1::Car;
                return (op);
            }
            "cdr" => {
                let op: Op1::Cdr;
                return (op);
            }
            "commit" => {
                let op: Op1::Commit;
                return (op);
            }
            "num" => {
                let op: Op1::Num;
                return (op);
            }
            "u64" => {
                let op: Op1::U64;
                return (op);
            }
            "comm" => {
                let op: Op1::Comm;
                return (op);
            }
            "char" => {
                let op: Op1::Char;
                return (op);
            }
            "open" => {
                let op: Op1::Open;
                return (op);
            }
            "secret" => {
                let op: Op1::Secret;
                return (op);
            }
            "atom" => {
                let op: Op1::Atom;
                return (op);
            }
            "emit" => {
                let op: Op1::Emit;
                return (op);
            }
        };
        return (nil)
    });
    let get_binop = func!(get_binop(head): 1 => {
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        match symbol head {
            "cons" => {
                let op: Op2::Cons;
                return (op);
            }
            "strcons" => {
                let op: Op2::StrCons;
                return (op);
            }
            "hide" => {
                let op: Op2::Hide;
                return (op);
            }
            "+" => {
                let op: Op2::Sum;
                return (op);
            }
            "-" => {
                let op: Op2::Diff;
                return (op);
            }
            "*" => {
                let op: Op2::Product;
                return (op);
            }
            "/" => {
                let op: Op2::Quotient;
                return (op);
            }
            "%" => {
                let op: Op2::Modulo;
                return (op);
            }
            "=" => {
                let op: Op2::NumEqual;
                return (op);
            }
            "eq" => {
                let op: Op2::Equal;
                return (op);
            }
            "<" => {
                let op: Op2::Less;
                return (op);
            }
            ">" => {
                let op: Op2::Greater;
                return (op);
            }
            "<=" => {
                let op: Op2::LessEqual;
                return (op);
            }
            ">=" => {
                let op: Op2::GreaterEqual;
                return (op);
            }
        };
        return (nil)
    });
    let make_call = func!(make_call(head, rest, env, cont): 4 => {
        let ret = Symbol("return");
        let foo: Expr::Nil;
        match rest.tag {
            Expr::Nil => {
                let cont: Cont::Call0 = cons4(env, cont, foo, foo);
                return (head, env, cont, ret)
            }
            Expr::Cons => {
                let (arg, more_args) = decons2(rest);
                match more_args.tag {
                    Expr::Nil => {
                        let cont: Cont::Call = cons4(arg, env, cont, foo);
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
        let fun: Expr::Fun;
        let cons: Expr::Cons;
        let thunk: Expr::Thunk;
        let head_is_fun = eq_tag(head, fun);
        let head_is_cons = eq_tag(head, cons);
        let head_is_thunk = eq_tag(head, thunk);
        let acc = or(head_is_fun, head_is_cons);
        let acc = or(acc, head_is_thunk);
        if acc {
            let t = Symbol("t");
            return (t)
        }
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        return (nil)
    });
    let is_cproc = is_cproc(cprocs);

    func!(reduce(expr, env, cont): 4 => {
        let ret = Symbol("return");
        let term: Cont::Terminal;
        let err: Cont::Error;
        let cproc: Expr::Cproc;

        let cont_is_term = eq_tag(cont, term);
        let cont_is_err = eq_tag(cont, err);
        let expr_is_cproc = eq_tag(expr, cproc);
        let acc_ret = or(cont_is_term, cont_is_err);
        let acc_ret = or(acc_ret, expr_is_cproc);
        if acc_ret {
            return (expr, env, cont, ret)
        }
        let apply = Symbol("apply-continuation");
        let thunk: Expr::Thunk;
        let sym: Expr::Sym;
        let cons: Expr::Cons;

        let expr_is_thunk = eq_tag(expr, thunk);
        let expr_is_sym = eq_tag(expr, sym);
        let expr_is_cons = eq_tag(expr, cons);
        let acc_not_apply = or(expr_is_thunk, expr_is_sym);
        let acc_not_apply = or(acc_not_apply, expr_is_cons);
        if !acc_not_apply {
            return (expr, env, cont, apply)
        }
        let errctrl = Symbol("error");
        let t = Symbol("t");
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        let foo: Expr::Nil;

        match expr.tag {
            Expr::Thunk => {
                let (thunk_expr, thunk_continuation) = decons2(expr);
                return (thunk_expr, env, thunk_continuation, apply)
            }
            Expr::Sym => {
                let expr_is_nil = eq_val(expr, nil);
                let expr_is_t = eq_val(expr, t);
                let expr_is_nil_or_t = or(expr_is_nil, expr_is_t);
                if expr_is_nil_or_t {
                    return (expr, env, cont, apply)
                }

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
                        let eq_val = eq_val(var_or_rec_binding, expr);
                        if eq_val {
                            return (val_or_more_rec_env, env, cont, apply)
                        }
                        match cont.tag {
                            Cont::Lookup => {
                                return (expr, smaller_env, cont, ret)
                            }
                        };
                        let cont: Cont::Lookup = cons4(env, cont, foo, foo);
                        return (expr, smaller_env, cont, ret)
                    }
                    Expr::Cons => {
                        let (v2, val2) = decons2(var_or_rec_binding);

                        let eq_val = eq_val(v2, expr);
                        if eq_val {
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
                        let cont: Cont::Lookup = cons4(env, cont, foo, foo);
                        return (expr, env_to_use, cont, ret)
                    }
                };
                return (expr, env, err, errctrl)
            }
            Expr::Cons => {
                // No need for `car_cdr` since the expression is already a `Cons`
                let (head, rest) = decons2(expr);
                let rest_is_nil = eq_tag(rest, nil);
                let rest_is_cons = eq_tag(rest, expr);
                let rest_is_nil_or_cons = or(rest_is_nil, rest_is_cons);
                if !rest_is_nil_or_cons {
                    // rest's tag can only be Nil or Cons
                    return (expr, env, err, errctrl);
                }
                match head.tag {
                    Expr::Sym => {
                        let let_sym = Symbol("let");
                        let letrec_sym = Symbol("letrec");
                        let head_is_let_sym = eq_val(head, let_sym);
                        let head_is_letrec_sym = eq_val(head, letrec_sym);
                        let head_is_let_or_letrec_sym = or(head_is_let_sym, head_is_letrec_sym);
                        if head_is_let_or_letrec_sym {
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
                            "begin" => {
                                let (arg1, more) = car_cdr(rest);
                                match more.tag {
                                    Expr::Nil => {
                                        return (arg1, env, cont, ret)
                                    }
                                };
                                let op: Op2::Begin;
                                let cont: Cont::Binop = cons4(op, env, more, cont);
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
                                        let op: Op1::Eval;
                                        let cont: Cont::Unop = cons4(op, cont, foo, foo);
                                        return (arg1, env, cont, ret)
                                    }
                                };
                                let op: Op2::Eval;
                                let cont: Cont::Binop = cons4(op, env, more, cont);
                                return (arg1, env, cont, ret)
                            }
                            "if" => {
                                let (condition, more) = car_cdr(rest);
                                match more.tag {
                                    Expr::Nil => {
                                        return (expr, env, err, errctrl)
                                    }
                                };
                                let cont: Cont::If = cons4(more, cont, foo, foo);
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
                        let (op) = get_unop(head);
                        let op_is_nil = eq_tag(op, nil);
                        if !op_is_nil {
                            let rest_is_nil = eq_tag(rest, nil);
                            if !rest_is_nil {
                                let (arg1, end) = decons2(rest);
                                let end_is_nil = eq_tag(end, nil);
                                if end_is_nil {
                                    let cont: Cont::Unop = cons4(op, cont, foo, foo);
                                    return (arg1, env, cont, ret)
                                }
                                return (expr, env, err, errctrl);
                            }
                            return (expr, env, err, errctrl);
                        }
                        // binops
                        let (op) = get_binop(head);
                        let op_is_nil = eq_tag(op, nil);
                        if !op_is_nil {
                            let rest_is_nil = eq_tag(rest, nil);
                            if !rest_is_nil {
                                let (arg1, more) = decons2(rest);
                                let more_is_nil = eq_tag(more, nil);
                                if !more_is_nil {
                                    let cont: Cont::Binop = cons4(op, env, more, cont);
                                    return (arg1, env, cont, ret);
                                }
                                return (expr, env, err, errctrl);
                            }
                            return (expr, env, err, errctrl);
                        }
                        //coprocessors
                        let (is_cproc) = is_cproc(head);
                        let is_cproc_is_t = eq_val(is_cproc, t);
                        if is_cproc_is_t {
                            let (arg, unevaled_args) = car_cdr(rest);
                            let cont: Cont::Cproc = cons4(head, unevaled_args, nil, cont);
                            return (arg, env, cont, ret);
                        }
                        // just call assuming that the symbol is bound to a function
                        let (fun, env, cont, ret) = make_call(head, rest, env, cont);
                        return (fun, env, cont, ret);
                    }
                };

                // head -> fn, rest -> args
                let (potentially_fun) = is_potentially_fun(head);
                let eq_val = eq_val(potentially_fun, t);
                if eq_val {
                    let (fun, env, cont, ret) = make_call(head, rest, env, cont);
                    return (fun, env, cont, ret);
                }
                return (expr, env, err, errctrl)
            }
        }
    })
}

/// Produces the correct `Func` used to call a coprocessor, depending on the context.
///
/// If there are no coprocessors available, just error straightaway. Otherwise:
///
/// * In the IVC context, just return the `Func` that does the coprocessor matching,
/// argument list destructuring and coprocessor call
/// * In the NIVC context, build an expression tagged as `Cproc`, setting up an
/// infinite loop in Lurk's step's `reduce`
///
/// Note: to break out of the (intended) NIVC loop, choose the correct coprocessor
/// from outside, which is supposed to know how to reduce such expression.
fn choose_cproc_call(cprocs: &[(&Symbol, usize)], ivc: bool) -> Func {
    if cprocs.is_empty() {
        func!(no_cproc_error(cproc_name, _evaluated_args, env, _cont): 4 => {
            let err: Cont::Error;
            let errctrl = Symbol("error");
            return (cproc_name, env, err, errctrl);
        })
    } else if ivc {
        match_and_run_cproc(cprocs)
    } else {
        func!(setup_cproc_loop(cproc_name, evaluated_args, env, cont): 4 => {
            let ret = Symbol("return");
            // setup loop
            let cproc: Expr::Cproc = cons2(cproc_name, evaluated_args);
            return (cproc, env, cont, ret);
        })
    }
}

fn apply_cont(cprocs: &[(&Symbol, usize)], ivc: bool) -> Func {
    let car_cdr = car_cdr();
    let make_tail_continuation = func!(make_tail_continuation(env, continuation): 1 => {
        match continuation.tag {
            Cont::Tail => {
                return (continuation);
            }
        };
        let foo: Expr::Nil;
        let tail_continuation: Cont::Tail = cons4(env, continuation, foo, foo);
        return (tail_continuation);
    });

    let extend_rec = func!(extend_rec(env, var, result): 1 => {
        let nil = Symbol("nil");
        let nil = cast(nil, Expr::Nil);
        let sym: Expr::Sym;
        let (binding_or_env, rest) = car_cdr(env);
        let (var_or_binding, _val_or_more_bindings) = car_cdr(binding_or_env);
        let binding: Expr::Cons = cons2(var, result);
        let var_or_binding_is_sym = eq_tag(var_or_binding, sym);
        let var_or_binding_is_nil = eq_tag(var_or_binding, nil);
        let var_or_binding_is_sym_or_nil = or(var_or_binding_is_sym, var_or_binding_is_nil);
        if var_or_binding_is_sym_or_nil {
            // It's a var, so we are extending a simple env with a recursive env.
            let list: Expr::Cons = cons2(binding, nil);
            let res: Expr::Cons = cons2(list, env);
            return (res)
        }
        // It's a binding, so we are extending a recursive env.
        let cons2: Expr::Cons = cons2(binding, binding_or_env);
        let res: Expr::Cons = cons2(cons2, rest);
        return (res)
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
    let choose_cproc_call = choose_cproc_call(cprocs, ivc);
    func!(apply_cont(result, env, cont, ctrl): 4 => {
        match symbol ctrl {
            "apply-continuation" => {
                let makethunk = Symbol("make-thunk");
                let lookup: Cont::Lookup;
                let tail: Cont::Tail;
                let cont_is_lookup = eq_tag(cont, lookup);
                let cont_is_tail = eq_tag(cont, tail);
                let cont_is_tail_or_lookup = or(cont_is_lookup, cont_is_tail);
                if cont_is_tail_or_lookup {
                    let (saved_env, continuation, _foo, _foo) = decons4(cont);
                    return (result, saved_env, continuation, makethunk)
                }

                let errctrl = Symbol("error");
                let ret = Symbol("return");
                let t = Symbol("t");
                let nil = Symbol("nil");
                let nil = cast(nil, Expr::Nil);
                let empty_str = String("");
                let zero = Num(0);
                let foo: Expr::Nil;
                let char: Expr::Char;
                let u64: Expr::U64;
                let err: Cont::Error;
                let term: Cont::Terminal;
                match cont.tag {
                    Cont::Outermost => {
                        return (result, env, term, ret)
                    }
                    Cont::Emit => {
                        let (cont, _rest, _foo, _foo) = decons4(cont);
                        return (result, env, cont, makethunk)
                    }
                    Cont::Call0 => {
                        let (saved_env, continuation, _foo, _foo) = decons4(cont);
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
                                let (unevaled_arg, saved_env, continuation, _foo) = decons4(cont);
                                let newer_cont: Cont::Call2 = cons4(result, saved_env, continuation, foo);
                                return (unevaled_arg, env, newer_cont, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Call2 => {
                        let (function, saved_env, continuation, _foo) = decons4(cont);
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
                        let comm: Expr::Comm;
                        let result_is_char = eq_tag(result, char);
                        let result_is_u64 = eq_tag(result, u64);
                        let result_is_num = eq_tag(result, zero);
                        let result_is_comm = eq_tag(result, comm);
                        let result_is_num_or_comm = or(result_is_num, result_is_comm);
                        let (operator, continuation, _foo, _foo) = decons4(cont);
                        match operator.tag {
                            Op1::Car => {
                                // Almost like car_cdr, except it returns
                                // an error in case it can't deconstruct it
                                match result.tag {
                                    Expr::Nil => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                    Expr::Cons => {
                                        let (car, _cdr) = decons2(result);
                                        return (car, env, continuation, makethunk)
                                    }
                                    Expr::Str => {
                                        let eq_val = eq_val(result, empty_str);
                                        if eq_val {
                                            return (nil, env, continuation, makethunk)
                                        }
                                        let (car, _cdr) = decons2(result);
                                        return (car, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            Op1::Cdr => {
                                match result.tag {
                                    Expr::Nil => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                    Expr::Cons => {
                                        let (_car, cdr) = decons2(result);
                                        return (cdr, env, continuation, makethunk)
                                    }
                                    Expr::Str => {
                                        let eq_val = eq_val(result, empty_str);
                                        if eq_val {
                                            return (empty_str, env, continuation, makethunk)
                                        }
                                        let (_car, cdr) = decons2(result);
                                        return (cdr, env, continuation, makethunk)
                                    }
                                };
                                return(result, env, err, errctrl)
                            }
                            Op1::Atom => {
                                match result.tag {
                                    Expr::Cons => {
                                        return (nil, env, continuation, makethunk)
                                    }
                                };
                                return (t, env, continuation, makethunk)
                            }
                            Op1::Emit => {
                                emit(result);
                                let emit: Cont::Emit = cons4(continuation, nil, foo, foo);
                                return (result, env, emit, makethunk)
                            }
                            Op1::Open => {
                                if result_is_num_or_comm {
                                    let result = cast(result, Expr::Comm);
                                    let (_secret, payload) = open(result);
                                    return(payload, env, continuation, makethunk)
                                }
                                return(result, env, err, errctrl)
                            }
                            Op1::Secret => {
                                if result_is_num_or_comm {
                                    let result = cast(result, Expr::Comm);
                                    let (secret, _payload) = open(result);
                                    return(secret, env, continuation, makethunk)
                                }
                                return(result, env, err, errctrl)
                            }
                            Op1::Commit => {
                                let comm = hide(zero, result);
                                return(comm, env, continuation, makethunk)
                            }
                            Op1::Num => {
                                let acc_cast = or(result_is_num_or_comm, result_is_char);
                                let acc_cast = or(acc_cast, result_is_u64);
                                if acc_cast {
                                    let cast = cast(result, Expr::Num);
                                    return(cast, env, continuation, makethunk)
                                }
                                return(result, env, err, errctrl)
                            }
                            Op1::U64 => {
                                let result_is_num_or_u64 = or(result_is_num, result_is_u64);
                                if result_is_num_or_u64 {
                                    // The limit is 2**64 - 1
                                    let trunc = truncate(result, 64);
                                    let cast = cast(trunc, Expr::U64);
                                    return(cast, env, continuation, makethunk)
                                }
                                return(result, env, err, errctrl)
                            }
                            Op1::Comm => {
                                if result_is_num_or_comm {
                                    let cast = cast(result, Expr::Comm);
                                    return(cast, env, continuation, makethunk)
                                }
                                return(result, env, err, errctrl)
                            }
                            Op1::Char => {
                                let result_is_num_or_char = or(result_is_num, result_is_char);
                                if result_is_num_or_char {
                                    // The limit is 2**32 - 1
                                    let trunc = truncate(result, 32);
                                    let cast = cast(trunc, Expr::Char);
                                    return(cast, env, continuation, makethunk)
                                }
                                return(result, env, err, errctrl)
                            }
                            Op1::Eval => {
                                return(result, nil, continuation, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Binop => {
                        let (operator, saved_env, unevaled_args, continuation) = decons4(cont);
                        let (arg2, rest) = car_cdr(unevaled_args);
                        match operator.tag {
                            Op2::Begin => {
                                match rest.tag {
                                    Expr::Nil => {
                                        return (arg2, saved_env, continuation, ret)
                                    }
                                };
                                let begin = Symbol("begin");
                                let begin_again: Expr::Cons = cons2(begin, unevaled_args);
                                return (begin_again, saved_env, continuation, ctrl)
                            }
                        };
                        match rest.tag {
                            Expr::Nil => {
                                let cont: Cont::Binop2 = cons4(operator, result, continuation, foo);
                                return (arg2, saved_env, cont, ret)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Binop2 => {
                        let size_u64 = Num(18446744073709551616);
                        let (operator, evaled_arg, continuation, _foo) = decons4(cont);
                        let (args_num_type) = args_num_type(evaled_arg, result);
                        let args_num_type_eq_nil = eq_tag(args_num_type, nil);
                        match operator.tag {
                            Op2::Eval => {
                                return (evaled_arg, result, continuation, ret)
                            }
                            Op2::Cons => {
                                let val: Expr::Cons = cons2(evaled_arg, result);
                                return (val, env, continuation, makethunk)
                            }
                            Op2::StrCons => {
                                let result_is_str = eq_tag(result, empty_str);
                                let evaled_arg_is_char = eq_tag(evaled_arg, char);
                                let acc_ok = and(result_is_str, evaled_arg_is_char);
                                if acc_ok {
                                    let val: Expr::Str = cons2(evaled_arg, result);
                                    return (val, env, continuation, makethunk)
                                }
                                return (result, env, err, errctrl)
                            }
                            Op2::Hide => {
                                match evaled_arg.tag {
                                    Expr::Num => {
                                        let hidden = hide(evaled_arg, result);
                                        return(hidden, env, continuation, makethunk)
                                    }
                                };
                                return (result, env, err, errctrl)
                            }
                            Op2::Equal => {
                                let eq_tag = eq_tag(evaled_arg, result);
                                let eq_val = eq_val(evaled_arg, result);
                                let eq = and(eq_tag, eq_val);
                                if eq {
                                    return (t, env, continuation, makethunk)
                                }
                                return (nil, env, continuation, makethunk)
                            }
                            Op2::Sum => {
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
                                        if not_overflow {
                                            let val = cast(val, Expr::U64);
                                            return (val, env, continuation, makethunk)
                                        }
                                        let val = sub(val, size_u64);
                                        let val = cast(val, Expr::U64);
                                        return (val, env, continuation, makethunk)
                                    }
                                }
                            }
                            Op2::Diff => {
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
                                        let not_neg = not(is_neg);
                                        if not_neg {
                                            let val = cast(val, Expr::U64);
                                            return (val, env, continuation, makethunk)
                                        }
                                        let val = add(val, size_u64);
                                        let val = cast(val, Expr::U64);
                                        return (val, env, continuation, makethunk)
                                    }
                                }
                            }
                            Op2::Product => {
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
                            Op2::Quotient => {
                                let is_z = eq_val(result, zero);
                                let acc_err = or(is_z, args_num_type_eq_nil);
                                if acc_err {
                                    return (result, env, err, errctrl)
                                }
                                match args_num_type.tag {
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
                            Op2::Modulo => {
                                let is_z = eq_val(result, zero);
                                let is_not_z = not(is_z);
                                let args_num_type_is_num = eq_tag(args_num_type, u64);
                                let acc_ok = and(is_not_z, args_num_type_is_num);
                                if acc_ok {
                                    let (_div, rem) = div_rem64(evaled_arg, result);
                                    let rem = cast(rem, Expr::U64);
                                    return (rem, env, continuation, makethunk)
                                }
                                return (result, env, err, errctrl)
                            }
                            Op2::NumEqual => {
                                if args_num_type_eq_nil {
                                    return (result, env, err, errctrl)
                                }
                                let eq = eq_val(evaled_arg, result);
                                if eq {
                                    return (t, env, continuation, makethunk)
                                }
                                return (nil, env, continuation, makethunk)
                            }
                            Op2::Less => {
                                if args_num_type_eq_nil {
                                    return (result, env, err, errctrl)
                                }
                                let val = lt(evaled_arg, result);
                                if val {
                                    return (t, env, continuation, makethunk)
                                }
                                return (nil, env, continuation, makethunk)
                            }
                            Op2::Greater => {
                                if args_num_type_eq_nil {
                                    return (result, env, err, errctrl)
                                }
                                let val = lt(result, evaled_arg);
                                if val {
                                    return (t, env, continuation, makethunk)
                                }
                                return (nil, env, continuation, makethunk)
                            }
                            Op2::LessEqual => {
                                if args_num_type_eq_nil {
                                    return (result, env, err, errctrl)
                                }
                                let val = lt(result, evaled_arg);
                                if val {
                                    return (nil, env, continuation, makethunk)
                                }
                                return (t, env, continuation, makethunk)
                            }
                            Op2::GreaterEqual => {
                                if args_num_type_eq_nil {
                                    return (result, env, err, errctrl)
                                }
                                let val = lt(evaled_arg, result);
                                if val {
                                    return (nil, env, continuation, makethunk)
                                }
                                return (t, env, continuation, makethunk)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::If => {
                        let (unevaled_args, continuation, _foo, _foo) = decons4(cont);
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
                    Cont::Cproc => {
                        let (cproc_name, unevaled_args, evaluated_args, cont) = decons4(cont);
                        // accumulate the evaluated arg (`result`)
                        let evaluated_args: Expr::Cons = cons2(result, evaluated_args);
                        match unevaled_args.tag {
                            Expr::Nil => {
                                // nothing else to evaluate
                                let (expr, env, cont, ctrl) = choose_cproc_call(cproc_name, evaluated_args, env, cont);
                                return (expr, env, cont, ctrl);
                            }
                            Expr::Cons => {
                                // pop the next argument that needs to be evaluated
                                let (arg, unevaled_args) = decons2(unevaled_args);
                                let cont: Cont::Cproc = cons4(
                                    cproc_name,
                                    unevaled_args,
                                    evaluated_args,
                                    cont
                                );
                                return (arg, env, cont, ret);
                            }
                        }
                    }
                }
            }
        };
        return (result, env, cont, ctrl)
    })
}

fn make_thunk() -> Func {
    func!(make_thunk(expr, env, cont, ctrl): 3 => {
        match symbol ctrl {
            "make-thunk" => {
                match cont.tag {
                    Cont::Tail => {
                        let (saved_env, saved_cont, _foo, _foo) = decons4(cont);
                        let thunk: Expr::Thunk = cons2(expr, saved_cont);
                        let cont: Cont::Dummy;
                        return (thunk, saved_env, cont)
                    }
                    Cont::Outermost => {
                        let cont: Cont::Terminal;
                        return (expr, env, cont)
                    }
                };
                let thunk: Expr::Thunk = cons2(expr, cont);
                let cont: Cont::Dummy;
                return (thunk, env, cont)
            }
        };
        return (expr, env, cont)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        eval::lang::{Coproc, Lang},
        lem::{slot::SlotsCounter, store::Store},
    };
    use bellpepper_core::{test_cs::TestConstraintSystem, Comparable};
    use pasta_curves::pallas::Scalar as Fr;

    const NUM_INPUTS: usize = 1;
    const NUM_AUX: usize = 9120;
    const NUM_CONSTRAINTS: usize = 11052;
    const NUM_SLOTS: SlotsCounter = SlotsCounter {
        hash4: 14,
        hash6: 3,
        hash8: 4,
        commitment: 1,
        bit_decomp: 3,
    };

    #[test]
    fn test_values() {
        let store = Store::default();
        let func = eval_step();
        let frame = Frame::<Fr>::blank(func, 0);
        let mut cs = TestConstraintSystem::<Fr>::new();
        let lang: Lang<Fr, Coproc<Fr>> = Lang::new();
        let _ = func.synthesize_frame_aux(&mut cs, &store, &frame, &lang);
        assert_eq!(func.slot, NUM_SLOTS);
        assert_eq!(cs.num_inputs(), NUM_INPUTS);
        assert_eq!(
            (cs.aux().len(), cs.num_constraints()),
            (NUM_AUX, NUM_CONSTRAINTS)
        );
        assert_eq!(func.num_constraints(&store), NUM_CONSTRAINTS);
    }
}
