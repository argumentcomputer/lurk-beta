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
    proof::FoldingMode,
    state::initial_lurk_state,
    tag::{
        ContTag::{Error, Terminal},
        ExprTag::Cproc,
    },
    Symbol,
};

use super::{
    interpreter::{Frame, Hints},
    pointers::{Ptr, RawPtr},
    store::{fetch_ptrs, Store},
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
    expr: &Ptr,
    store: &Store<F>,
    lang: &Lang<F, C>,
) -> usize {
    match expr.parts() {
        (Tag::Expr(Cproc), RawPtr::Hash4(idx)) => {
            let [cproc, _] =
                &fetch_ptrs!(store, 2, *idx).expect("Coprocessor expression is not interned");
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
    cprocs: &[Func],
    input: &[Ptr],
    store: &Store<F>,
    lang: &Lang<F, C>,
    emitted: &mut Vec<Ptr>,
    pc: usize,
) -> Result<(Frame, bool)> {
    let func = if pc == 0 {
        lurk_step
    } else {
        cprocs.get(pc - 1).expect("Program counter outside range")
    };
    assert_eq!(func.input_params.len(), input.len());
    let preimages = Hints::new_from_func(func);
    let frame = func.call(input, store, preimages, emitted, lang, pc)?;
    let must_break = matches!(frame.output[2].tag(), Tag::Cont(Terminal | Error));
    Ok((frame, must_break))
}

// Builds frames for IVC or NIVC scheme
fn build_frames<
    F: LurkField,
    C: Coprocessor<F>,
    LogFmt: Fn(usize, &[Ptr], &[Ptr], &Store<F>) -> String,
>(
    lurk_step: &Func,
    cprocs: &[Func],
    mut input: Vec<Ptr>,
    store: &Store<F>,
    limit: usize,
    lang: &Lang<F, C>,
    log_fmt: LogFmt,
) -> Result<Vec<Frame>> {
    let mut pc = 0;
    let mut frames = vec![];
    let mut iterations = 0;
    tracing::info!("{}", &log_fmt(0, &input, &[], store));
    for _ in 0..limit {
        let mut emitted = vec![];
        let (frame, must_break) =
            compute_frame(lurk_step, cprocs, &input, store, lang, &mut emitted, pc)?;

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
    Ok(frames)
}

/// Faster version of `build_frames` that doesn't accumulate frames
fn traverse_frames<F: LurkField, C: Coprocessor<F>>(
    lurk_step: &Func,
    cprocs: &[Func],
    mut input: Vec<Ptr>,
    store: &Store<F>,
    limit: usize,
    lang: &Lang<F, C>,
) -> Result<(Vec<Ptr>, usize, Vec<Ptr>)> {
    let mut pc = 0;
    let mut iterations = 0;
    let mut emitted = vec![];
    for _ in 0..limit {
        let (frame, must_break) =
            compute_frame(lurk_step, cprocs, &input, store, lang, &mut emitted, pc)?;

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
    lang_setup: Option<(&Func, &[Func], &Lang<F, C>)>,
    expr: Ptr,
    env: Ptr,
    cont: Ptr,
    store: &Store<F>,
    limit: usize,
) -> Result<Vec<Frame>> {
    let state = initial_lurk_state();
    let log_fmt = |i: usize, inp: &[Ptr], emit: &[Ptr], store: &Store<F>| {
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

    match lang_setup {
        None => {
            let lang: Lang<F, C> = Lang::new();
            build_frames(eval_step(), &[], input, store, limit, &lang, log_fmt)
        }
        Some((lurk_step, cprocs, lang)) => {
            build_frames(lurk_step, cprocs, input, store, limit, lang, log_fmt)
        }
    }
}

#[inline]
pub fn evaluate_with_env<F: LurkField, C: Coprocessor<F>>(
    lang_setup: Option<(&Func, &[Func], &Lang<F, C>)>,
    expr: Ptr,
    env: Ptr,
    store: &Store<F>,
    limit: usize,
) -> Result<Vec<Frame>> {
    evaluate_with_env_and_cont(lang_setup, expr, env, store.cont_outermost(), store, limit)
}

#[inline]
pub fn evaluate<F: LurkField, C: Coprocessor<F>>(
    lang_setup: Option<(&Func, &[Func], &Lang<F, C>)>,
    expr: Ptr,
    store: &Store<F>,
    limit: usize,
) -> Result<Vec<Frame>> {
    evaluate_with_env_and_cont(
        lang_setup,
        expr,
        store.intern_empty_env(),
        store.cont_outermost(),
        store,
        limit,
    )
}

pub fn evaluate_simple_with_env<F: LurkField, C: Coprocessor<F>>(
    lang_setup: Option<(&Func, &[Func], &Lang<F, C>)>,
    expr: Ptr,
    env: Ptr,
    store: &Store<F>,
    limit: usize,
) -> Result<(Vec<Ptr>, usize, Vec<Ptr>)> {
    let input = vec![expr, env, store.cont_outermost()];
    match lang_setup {
        None => {
            let lang: Lang<F, C> = Lang::new();
            traverse_frames(eval_step(), &[], input, store, limit, &lang)
        }
        Some((lurk_step, cprocs, lang)) => {
            traverse_frames(lurk_step, cprocs, input, store, limit, lang)
        }
    }
}

#[inline]
pub fn evaluate_simple<F: LurkField, C: Coprocessor<F>>(
    lang_setup: Option<(&Func, &[Func], &Lang<F, C>)>,
    expr: Ptr,
    store: &Store<F>,
    limit: usize,
) -> Result<(Vec<Ptr>, usize, Vec<Ptr>)> {
    evaluate_simple_with_env(lang_setup, expr, store.intern_empty_env(), store, limit)
}

pub struct EvalConfig<'a, F, C> {
    lang: &'a Lang<F, C>,
    folding_mode: FoldingMode,
}

impl<'a, F, C> EvalConfig<'a, F, C> {
    #[inline]
    pub fn new_ivc(lang: &'a Lang<F, C>) -> Self {
        Self {
            lang,
            folding_mode: FoldingMode::IVC,
        }
    }

    #[inline]
    pub fn new_nivc(lang: &'a Lang<F, C>) -> Self {
        Self {
            lang,
            folding_mode: FoldingMode::NIVC,
        }
    }

    #[inline]
    pub(crate) fn lang(&self) -> &Lang<F, C> {
        self.lang
    }

    #[inline]
    fn is_ivc(&self) -> bool {
        matches!(self.folding_mode, FoldingMode::IVC)
    }
}

/// Creates a LEM `Func` corresponding to Lurk's step function from a `Lang`.
/// The `ivc` flag tells whether the generated step function is used for IVC or
/// NIVC. In the IVC case, the step function is capable of reducing calls to the
/// coprocessors present in `Lang` and their circuit will go in the circuit of
/// the step function. In the NIVC case, the step function won't be able to reduce
/// calls to coprocessors and sets up a loop via the `Expr::Cproc` tag, meaning
/// that the reduction must be done from outside.
pub fn make_eval_step_from_config<F: LurkField, C: Coprocessor<F>>(
    ec: &EvalConfig<'_, F, C>,
) -> Func {
    make_eval_step(
        &ec.lang
            .coprocessors()
            .iter()
            .map(|(s, c)| (s, c.arity()))
            .collect::<Vec<_>>(),
        ec.is_ivc(),
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

/// Simpler version of `car_cdr` that doesn't deconstruct strings to save some
/// constraints
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
/// function. It checks whether the coprocessor expression corresponds to the
/// right coprocessor. If it doesn't, evaluation will error and the circuit
/// becomes unsatisfiable. If it does, destructure the list of arguments and
/// call the coprocessor.
///
/// `run_cproc` is meant to be used in the context of NIVC, when the circuit for
/// each coprocessor is detached from Lurk's universal circuit.
///
/// The following is a LEM pseudo-code for what this function implements:
///
/// ```ignore
/// run_cproc(cproc, env, cont): 3 {
///     let err: Cont::Error = HASH_8_ZEROS;
///     let nil = Symbol("nil");
///     let nil = cast(nil, Expr::Nil);
///     match cproc.tag {
///         Expr::Cproc => {
///             let (cproc_name, evaluated_args) = decons2(cproc);
///             match symbol cproc_name {
///                 // `x` is the name of the coprocessor being called
///                 x => {
///                     // `n` is the arity of the coprocessor `x`
///                     let is_nil = eq_tag(evaluated_args, nil);
///                     // save a copy of the evaluated arguments for possible arity error
///                     let evaluated_args_cp = copy(evaluated_args);
///                     if !is_nil {
///                         let (x{n-1}, evaluated_args) = car_cdr(evaluated_args);
///                         let is_nil = eq_tag(evaluated_args, nil);
///                         if !is_nil {
///                             ...
///                             let (x0, evaluated_args) = car_cdr(evaluated_args);
///                             let is_nil = eq_tag(evaluated_args, nil);
///                             // there must be no remaining arguments
///                             if is_nil {
///                                 Op::Cproc([expr, env, cont], x, [x0, x1, ..., x{n-1}, env, cont]);
///                                 return (expr, env, cont);
///                             }
///                             return (evaluated_args_cp, env, err);
///                         }
///                         return (evaluated_args_cp, env, err);
///                     }
///                     return (evaluated_args_cp, env, err);
///                 }
///             }
///             // no default case
///         }
///     }
///     // no default case
/// }
/// ```
fn run_cproc(cproc_sym: Symbol, arity: usize) -> Func {
    let evaluated_args = if arity == 0 {
        Var::new("_evaluated_args")
    } else {
        Var::new("evaluated_args")
    };
    let expr = Var::new("expr");
    let env = Var::new("env");
    let cont = Var::new("cont");
    let nil = Var::new("nil");
    let is_nil = Var::new("is_nil");
    let cproc = Var::new("cproc");
    let cproc_name = Var::new("cproc_name");
    let cproc_out = vec![expr.clone(), env.clone(), cont.clone()];
    let func_out = vec![expr, env.clone(), cont.clone()];
    let err_block = Block::ctrl(ctrl!(return (evaluated_args_cp, env, err)));
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
            Op::EqTag(is_nil.clone(), evaluated_args.clone(), nil.clone()),
        ];
        block = Block {
            ops,
            ctrl: if i == 0 {
                Ctrl::if_(is_nil.clone(), block, err_block.clone())
            } else {
                Ctrl::if_(is_nil.clone(), err_block.clone(), block)
            },
        };
    }
    if arity > 0 {
        let ops = vec![
            Op::EqTag(is_nil.clone(), evaluated_args.clone(), nil.clone()),
            Op::Copy(Var::new("evaluated_args_cp"), evaluated_args.clone()),
        ];
        block = Block {
            ops,
            ctrl: Ctrl::if_(is_nil.clone(), err_block.clone(), block),
        }
    }

    // MatchSymbol
    block = Block {
        ops: vec![Op::Decons2(
            [cproc_name.clone(), evaluated_args],
            cproc.clone(),
        )],
        ctrl: Ctrl::match_symbol(cproc_name, vec![(cproc_sym, block)], None),
    };

    // MatchTag
    block = Block {
        ops: if arity == 0 {
            vec![]
        } else {
            vec![
                op!(let err: Cont::Error = HASH_8_ZEROS),
                op!(let nil = Symbol("nil")),
                op!(let nil = cast(nil, Expr::Nil)),
            ]
        },
        ctrl: Ctrl::match_tag(cproc.clone(), vec![(Tag::Expr(Cproc), block)], None),
    };
    let func_inp = vec![cproc, env, cont];
    Func::new("run_cproc".into(), func_inp, 3, block).unwrap()
}

/// Creates the `Func`s used to call coprocessors in the NIVC scenario. Each
/// coprocessor in the `Lang` will have its own specialized `Func`
pub fn make_cprocs_funcs_from_lang<F: LurkField, C: Coprocessor<F>>(
    lang: &Lang<F, C>,
) -> Vec<Func> {
    lang.coprocessors()
        .iter()
        .map(|(name, c)| run_cproc(name.clone(), c.arity()))
        .collect()
}

/// Tells whether `head`, which is assumed to be a symbol, corresponds to the name
/// of a coprocessor in the `Lang`.
///
/// The following is a LEM pseudo-code for what this function implements:
///
/// ```ignore
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
/// ```
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
        let match_symbol_cases = cprocs
            .iter()
            .map(|(cproc, _)| ((*cproc).clone(), Block::ctrl(ctrl!(return (t)))))
            .collect();
        let def = Some(Block::ctrl(ctrl!(return (nil))));
        let ctrl = Ctrl::match_symbol(head.clone(), match_symbol_cases, def);
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
/// The following is a LEM pseudo-code for what this function implements:
///
/// ```ignore
/// match_and_run_cproc(cproc_name, evaluated_args, env, cont): 4 {
///     let err: Cont::Error = HASH_8_ZEROS;
///     let nil = Symbol("nil");
///     let nil = cast(nil, Expr::Nil);
///     let makethunk = Symbol("make-thunk");
///     let errctrl = Symbol("error");
///     let ret = Symbol("return");
///     match symbol cproc_name {
///         x => {
///             // `n` is the arity of the coprocessor `x`
///             let is_nil = eq_tag(evaluated_args, nil);
///             // save a copy of the evaluated arguments for possible arity error
///             let evaluated_args_cp = copy(evaluated_args);
///             if !is_nil {
///                 let (x{n-1}, evaluated_args) = car_cdr(evaluated_args);
///                 let is_nil = eq_tag(evaluated_args, nil);
///                 if !is_nil {
///                     ...
///                     let (x0, evaluated_args) = car_cdr(evaluated_args);
///                     let is_nil = eq_tag(evaluated_args, nil);
///                     // there must be no remaining arguments
///                     if is_nil {
///                         Op::Cproc([expr, env, cont], x, [x0, x1, ..., x{n-1}, env, cont]);
///                         match cont.tag {
///                             Cont::Error => {
///                                 return (expr, env, err, errctrl);
///                             }
///                             Cont::Terminal => {
///                                 return (expr, env, cont, ret);
///                             }
///                         };
///                         return (expr, env, cont, makethunk);
///                     }
///                     return (evaluated_args_cp, env, err, errctrl);
///                 }
///                 return (evaluated_args_cp, env, err, errctrl);
///             }
///             return (evaluated_args_cp, env, err, errctrl);
///         }
///         ...
///     }
/// }
/// ```
fn match_and_run_cproc(cprocs: &[(&Symbol, usize)]) -> Func {
    let max_arity = cprocs.iter().fold(0, |acc, (_, a)| acc.max(*a));
    let cproc_name = Var::new("cproc_name");
    let evaluated_args = if max_arity == 0 {
        Var::new("_evaluated_args")
    } else {
        Var::new("evaluated_args")
    };
    let expr = Var::new("expr");
    let env = Var::new("env");
    let cont = Var::new("cont");
    let nil = Var::new("nil");
    let is_nil = Var::new("is_nil");
    let cproc_out = vec![expr.clone(), env.clone(), cont.clone()];
    let func_out = vec![expr, env.clone(), cont.clone(), Var::new("makethunk")];
    let err_block = Block::ctrl(ctrl!(return (evaluated_args_cp, env, err, errctrl)));
    let err_block_from_cproc = Block::ctrl(ctrl!(return (expr, env, err, errctrl)));
    let ret_block_from_cproc = Block::ctrl(ctrl!(return (expr, env, cont, ret)));
    let check_cproc_error_ctrl = Ctrl::match_tag(
        cont.clone(),
        vec![
            (Tag::Cont(Error), err_block_from_cproc),
            (Tag::Cont(Terminal), ret_block_from_cproc),
        ],
        Some(Block::ctrl(Ctrl::Return(func_out))),
    );
    let mut match_symbol_map = IndexMap::with_capacity(cprocs.len());
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
            ctrl: check_cproc_error_ctrl.clone(),
        };
        for (i, cproc_arg) in cproc_inp[0..arity].iter().enumerate() {
            let ops = vec![
                Op::Call(
                    vec![cproc_arg.clone(), evaluated_args.clone()],
                    Box::new(car_cdr()),
                    vec![evaluated_args.clone()],
                ),
                Op::EqTag(is_nil.clone(), evaluated_args.clone(), nil.clone()),
            ];
            block = Block {
                ops,
                ctrl: if i == 0 {
                    Ctrl::if_(is_nil.clone(), block, err_block.clone())
                } else {
                    Ctrl::if_(is_nil.clone(), err_block.clone(), block)
                },
            };
        }
        if arity > 0 {
            let ops = vec![
                Op::EqTag(is_nil.clone(), evaluated_args.clone(), nil.clone()),
                Op::Copy(Var::new("evaluated_args_cp"), evaluated_args.clone()),
            ];
            block = Block {
                ops,
                ctrl: Ctrl::if_(is_nil.clone(), err_block.clone(), block),
            }
        }
        match_symbol_map.insert(cproc.clone(), block);
    }
    let ctrl = Ctrl::MatchSymbol(cproc_name.clone(), match_symbol_map, None);
    let func_inp = vec![cproc_name, evaluated_args, env, cont];
    let ops = if max_arity == 0 {
        vec![
            op!(let err: Cont::Error = HASH_8_ZEROS),
            op!(let makethunk = Symbol("make-thunk")),
            op!(let errctrl = Symbol("error")),
            op!(let ret = Symbol("return")),
        ]
    } else {
        vec![
            op!(let err: Cont::Error = HASH_8_ZEROS),
            op!(let makethunk = Symbol("make-thunk")),
            op!(let errctrl = Symbol("error")),
            op!(let ret = Symbol("return")),
            op!(let nil = Symbol("nil")),
            op!(let nil = cast(nil, Expr::Nil)),
        ]
    };
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
    let lookup = func!(lookup(expr, env, state): 3 => {
        let found = Symbol("found");
        let not_found = Symbol("not_found");
        let error = Symbol("error");
        let continue = eq_val(not_found, state);
        if !continue {
            return (expr, env, state)
        }
        let zero = Num(0);
        let env_is_zero = eq_val(env, zero);
        if env_is_zero {
            return (expr, env, error)
        }
        let (var, val, smaller_env) = pop_binding(env);
        let eq_val = eq_val(var, expr);
        if eq_val {
            return (val, env, found)
        }
        return (expr, smaller_env, not_found)
    });

    func!(reduce(expr, env, cont): 4 => {
        let ret = Symbol("return");
        let term: Cont::Terminal = HASH_8_ZEROS;
        let err: Cont::Error = HASH_8_ZEROS;
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
                let not_found = Symbol("not_found");
                // `expr` is the symbol. If the lookup was successful, it will
                // return the result as `res` and a "found" state. If the lookup
                // is incomplete, it will return the original symbol as `res`
                // and a "not_found" state
                let (res, res_env, state) = lookup(expr, env, not_found);
                let (res, res_env, state) = lookup(res, res_env, state);
                let (res, res_env, state) = lookup(res, res_env, state);
                let (res, res_env, state) = lookup(res, res_env, state);
                let (res, res_env, state) = lookup(res, res_env, state);
                let (res, res_env, state) = lookup(res, res_env, state);
                let (res, res_env, state) = lookup(res, res_env, state);
                let (res, res_env, state) = lookup(res, res_env, state);
                match symbol state {
                    "error" => {
                        return (expr, env, err, errctrl)
                    }
                    "found" => {
                        match res.tag {
                            // if `val2` is a recursive closure, then extend its environment
                            Expr::Rec => {
                                let (args, body, closed_env, _foo) = decons4(res);
                                // remember `expr` is the original symbol, i.e. the symbol
                                // of the recursive closure
                                let extended = push_binding(expr, res, closed_env);
                                let fun: Expr::Fun = cons4(args, body, extended, foo);
                                return (fun, res_env, cont, apply)
                            }
                        };
                        return (res, res_env, cont, apply)
                    }
                    "not_found" => {
                        // if it's not yet found, we must keep reducing
                        return (res, res_env, cont, ret)
                    }
                }
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
                                            let end_is_nil = eq_tag(end, nil);
                                            if !end_is_nil {
                                                return (expr, env, err, errctrl)
                                            }
                                            let (expanded) = expand_bindings(head, body, body1, rest_bindings);
                                            if head_is_let_sym {
                                                let cont: Cont::Let = cons4(var, env, expanded, cont);
                                                return (val, env, cont, ret)
                                            }
                                            let cont: Cont::LetRec = cons4(var, env, expanded, cont);
                                            return (val, env, cont, ret)
                                        }
                                    };
                                    return (expr, env, err, errctrl)
                                }
                            };
                            return (expr, env, err, errctrl)
                        }
                        match symbol head {
                            "lambda" => {
                                let (vars, rest) = car_cdr(rest);
                                let rest_nil = eq_tag(rest, nil);
                                if rest_nil {
                                    return (expr, env, err, errctrl)
                                }
                                let (body, end) = car_cdr(rest);
                                let end_nil = eq_tag(end, nil);
                                if !end_nil {
                                    return (expr, env, err, errctrl)
                                }
                                match vars.tag {
                                    Expr::Cons => {
                                        let (var, _rest_vars) = decons2(vars);
                                        match var.tag {
                                            Expr::Sym => {
                                                let fun: Expr::Fun = cons4(vars, body, env, foo);
                                                return (fun, env, cont, apply)
                                            }
                                        };
                                        return (expr, env, err, errctrl)
                                    }
                                    Expr::Nil => {
                                        let fun: Expr::Fun = cons4(vars, body, env, foo);
                                        return (fun, env, cont, apply)
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
                                let cont: Cont::If = cons4(more, env, cont, foo);
                                return (condition, env, cont, ret)
                            }
                            "empty-env" => {
                                match rest.tag {
                                    Expr::Nil => {
                                        let empty_env: Expr::Env;
                                        return (empty_env, env, cont, apply)
                                    }
                                };
                                return (expr, env, err, errctrl)
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
                            if rest_is_nil {
                                let args: Expr::Cons = cons2(nil, nil);
                                let cont: Cont::Cproc = cons4(head, args, env, cont);
                                return (nil, env, cont, apply);
                            }
                            let (arg, unevaled_args) = car_cdr(rest);
                            let args: Expr::Cons = cons2(unevaled_args, nil);
                            let cont: Cont::Cproc = cons4(head, args, env, cont);
                            return (arg, env, cont, ret);
                        }
                        // just call assuming that the symbol is bound to a function
                        let cont: Cont::Call = cons4(rest, env, cont, foo);
                        return (head, env, cont, ret);
                    }
                };

                // head -> fn, rest -> args
                let (potentially_fun) = is_potentially_fun(head);
                let eq_val = eq_val(potentially_fun, t);
                if eq_val {
                    let cont: Cont::Call = cons4(rest, env, cont, foo);
                    return (head, env, cont, ret);
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
            let err: Cont::Error = HASH_8_ZEROS;
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

                let errctrl = Symbol("error");
                let ret = Symbol("return");
                let t = Symbol("t");
                let nil = Symbol("nil");
                let nil = cast(nil, Expr::Nil);
                let empty_env: Expr::Env;
                let empty_str = String("");
                let zero = Num(0);
                let foo: Expr::Nil;
                let char: Expr::Char;
                let u64: Expr::U64;
                let err: Cont::Error = HASH_8_ZEROS;
                let term: Cont::Terminal = HASH_8_ZEROS;
                match cont.tag {
                    Cont::Outermost => {
                        // We erase the environment as to not leak any information about internal variables.
                        return (result, empty_env, term, ret)
                    }
                    Cont::Emit => {
                        let (cont, _rest, _foo, _foo) = decons4(cont);
                        return (result, env, cont, makethunk)
                    }
                    Cont::Call => {
                        match result.tag {
                            Expr::Fun => {
                                let (args, args_env, continuation, _foo) = decons4(cont);
                                let (vars, body, fun_env, _foo) = decons4(result);
                                match args.tag {
                                    Expr::Cons => {
                                        match vars.tag {
                                            Expr::Nil => {
                                                // Cannot apply non-zero number of arguments to a zero argument function
                                                return (result, env, err, errctrl)
                                            }
                                            Expr::Cons => {
                                                let (arg, rest_args) = decons2(args);
                                                let newer_cont: Cont::Call2 = cons4(result, rest_args, args_env, continuation);
                                                return (arg, args_env, newer_cont, ret)
                                            }
                                        }
                                    }
                                    Expr::Nil => {
                                        match vars.tag {
                                            Expr::Nil => {
                                                return (body, fun_env, continuation, ret)
                                            }
                                            Expr::Cons => {
                                                // TODO should we not fail here in an analogous way to the non-zero application
                                                // on a zero argument function case?
                                                return (result, env, continuation, ret)
                                            }
                                        }
                                    }
                                }
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Call2 => {
                        let (function, args, args_env, continuation) = decons4(cont);
                        match function.tag {
                            Expr::Fun => {
                                let (vars, body, fun_env, _foo) = decons4(function);
                                // vars must be non-empty, so:
                                let (var, rest_vars) = decons2(vars);
                                let ext_env = push_binding(var, result, fun_env);
                                let rest_vars_empty = eq_tag(rest_vars, nil);
                                let args_empty = eq_tag(args, nil);
                                if rest_vars_empty {
                                    if args_empty {
                                        return (body, ext_env, continuation, ret)
                                    }
                                    // Oversaturated call
                                    let cont: Cont::Call = cons4(args, args_env, continuation, foo);
                                    return (body, ext_env, cont, ret)
                                }
                                let ext_function: Expr::Fun = cons4(rest_vars, body, ext_env, foo);
                                let (var, _rest_vars) = car_cdr(rest_vars);
                                match var.tag {
                                    Expr::Sym => {
                                        if args_empty {
                                            // Undersaturated call
                                            return (ext_function, ext_env, continuation, ret)
                                        }
                                        let (arg, rest_args) = decons2(args);
                                        let cont: Cont::Call2 = cons4(ext_function, rest_args, args_env, continuation);
                                        return (arg, args_env, cont, ret)
                                    }
                                };
                                return (result, env, err, errctrl)
                            }
                        };
                        return (result, env, err, errctrl)
                    }
                    Cont::Let => {
                        let (var, saved_env, body, cont) = decons4(cont);
                        let extended_env = push_binding(var, result, saved_env);
                        return (body, extended_env, cont, ret)
                    }
                    Cont::LetRec => {
                        let (var, saved_env, body, cont) = decons4(cont);
                        match result.tag {
                            Expr::Fun => {
                                let result = cast(result, Expr::Rec);
                                let extended_env = push_binding(var, result, saved_env);
                                return (body, extended_env, cont, ret)
                            }
                        };
                        let extended_env = push_binding(var, result, saved_env);
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
                                // `car_cdr` semantics
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
                                // `car_cdr` semantics
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
                                return(result, empty_env, continuation, ret)
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
                                match result.tag {
                                    Expr::Env => {
                                        return (evaled_arg, result, continuation, ret)
                                    }
                                };
                                return (result, env, err, errctrl)
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
                        let (unevaled_args, args_env, continuation, _foo) = decons4(cont);
                        let (arg1, more) = car_cdr(unevaled_args);
                        let (arg2, end) = car_cdr(more);
                        match end.tag {
                            Expr::Nil => {
                                match result.tag {
                                    Expr::Nil => {
                                        return (arg2, args_env, continuation, ret)
                                    }
                                };
                                return (arg1, args_env, continuation, ret)
                            }
                        };
                        return (arg1, env, err, errctrl)
                    }
                    Cont::Cproc => {
                        let (cproc_name, args, saved_env, cont) = decons4(cont);
                        let (unevaled_args, evaluated_args) = decons2(args);
                        // accumulate the evaluated arg (`result`)
                        let evaluated_args: Expr::Cons = cons2(result, evaluated_args);
                        match unevaled_args.tag {
                            Expr::Nil => {
                                // nothing else to evaluate
                                let (expr, env, cont, ctrl) = choose_cproc_call(cproc_name, evaluated_args, saved_env, cont);
                                return (expr, env, cont, ctrl);
                            }
                            Expr::Cons => {
                                // pop the next argument that needs to be evaluated
                                let (arg, unevaled_args) = decons2(unevaled_args);
                                let args: Expr::Cons = cons2(unevaled_args, evaluated_args);
                                let cont: Cont::Cproc = cons4(
                                    cproc_name,
                                    args,
                                    saved_env,
                                    cont
                                );
                                return (arg, saved_env, cont, ret);
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
                    Cont::Outermost => {
                        let empty_env: Expr::Env;
                        let cont: Cont::Terminal = HASH_8_ZEROS;
                        return (expr, empty_env, cont)
                    }
                };
                let thunk: Expr::Thunk = cons2(expr, cont);
                let cont: Cont::Dummy = HASH_8_ZEROS;
                return (thunk, env, cont)
            }
        };
        return (expr, env, cont)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{eval::lang::Lang, lem::store::Store};
    use bellpepper_core::{test_cs::TestConstraintSystem, Comparable};
    use expect_test::{expect, Expect};
    use halo2curves::bn256::Fr;

    #[test]
    fn test_counts() {
        let store = Store::default();
        let func = eval_step();
        let frame = Frame::blank(func, 0, &store);
        let mut cs = TestConstraintSystem::<Fr>::new();
        let lang: Lang<Fr> = Lang::new();
        let _ = func.synthesize_frame_aux(&mut cs, &store, &frame, &lang);
        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };
        expect_eq(func.slots_count.hash4, expect!["14"]);
        expect_eq(func.slots_count.hash6, expect!["0"]);
        expect_eq(func.slots_count.hash8, expect!["6"]);
        expect_eq(func.slots_count.commitment, expect!["1"]);
        expect_eq(func.slots_count.bit_decomp, expect!["3"]);
        expect_eq(cs.num_inputs(), expect!["1"]);
        expect_eq(cs.aux().len(), expect!["9095"]);
        expect_eq(cs.num_constraints(), expect!["11025"]);
        assert_eq!(func.num_constraints(&store), cs.num_constraints());
    }
}
