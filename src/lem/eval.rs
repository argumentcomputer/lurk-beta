use crate::func;

use super::Func;

/// Lurk's step function
#[allow(dead_code)]
pub(crate) fn eval_step() -> Func {
    let reduce = reduce();
    let apply_cont = apply_cont();
    let make_thunk = make_thunk();

    func!((expr, env, cont): 3 => {
        let (expr, env, cont, ctrl) = reduce(expr, env, cont);
        let (expr, env, cont, ctrl) = apply_cont(expr, env, cont, ctrl);
        let (expr, env, cont, ctrl) = make_thunk(expr, env, cont, ctrl);
        return (expr, env, cont)
    })
}

fn uncons() -> Func {
    func!((xs): 2 => {
        match_tag xs {
            Nil => {
                return (xs, xs)
            },
            Cons => {
                let (car, cdr) = unhash2(xs);
                return (car, cdr)
            }
        }
    })
}

fn make_tail_continuation() -> Func {
    func!((env, continuation): 1 => {
        match_tag continuation {
            Tail => {
                return (continuation);
            }
        };
        let tail_continuation: Tail = hash2(env, continuation);
        return (tail_continuation);
    })
}

fn reduce() -> Func {
    // Auxiliary functions
    let uncons = uncons();
    let env_to_use = func!((smaller_env, smaller_rec_env): 1 => {
        match_tag smaller_rec_env {
            Nil => {
                // TODO better syntax for one sized returns
                return (smaller_env)
            }
        };
        let env: Cons = hash2(smaller_rec_env, smaller_env);
        return (env)
    });

    func!((expr, env, cont): 4 => {
        match_tag cont {
            Terminal | Error => {
                let ctrl: Return;
                return (expr, env, cont, ctrl)
            }
        };

        match_tag expr {
            Nil | Fun | Num | Str | Char | Comm | U64 | Key => {
                let ctrl: ApplyContinuation;
                return (expr, env, cont, ctrl)
            },
            Thunk => {
                let (thunk_expr, thunk_continuation) = unhash2(expr);
                let ctrl: MakeThunk;
                return (thunk_expr, env, thunk_continuation, ctrl)
            },
            Sym => {
                match_symbol expr {
                    "nil" | "t" => {
                        let ctrl: ApplyContinuation;
                        return (expr, env, cont, ctrl)
                    }
                };

                match_tag env {
                    Nil => {
                        let err: Error;
                        return (expr, env, err, err)
                    }
                };

                let (binding, smaller_env) = uncons(env);
                match_tag binding {
                    Nil => {
                        let err: Error;
                        return (expr, env, err, err)
                    }
                };

                let (var_or_rec_binding, val_or_more_rec_env) =
                    uncons(binding);
                match_tag var_or_rec_binding {
                    Sym => {
                        if var_or_rec_binding == expr {
                            let ctrl: ApplyContinuation;
                            return (val_or_more_rec_env, env, cont, ctrl)
                        }
                        match_tag cont {
                            Lookup => {
                                let ctrl: Return;
                                return (expr, smaller_env, cont, ctrl)
                            }
                        };
                        let ctrl: Return;
                        let cont: Lookup = hash2(env, cont);
                        return (expr, smaller_env, cont, ctrl)
                    },
                    Cons => {
                        let (v2, val2) = uncons(var_or_rec_binding);

                        if v2 == expr {
                            match_tag val2 {
                                Fun => {
                                    // if `val2` is a closure, then extend its environment
                                    let (arg, body, closed_env) = unhash3(val2);
                                    let extended: Cons = hash2(binding, closed_env);
                                    // and return the extended closure
                                    let fun: Fun = hash3(arg, body, extended);
                                    let ctrl: ApplyContinuation;
                                    return (fun, env, cont, ctrl)
                                }
                            };
                            // otherwise return `val2`
                            let ctrl: ApplyContinuation;
                            return (val2, env, cont, ctrl)
                        }
                        // TODO better syntax for calls with one sized returns
                        let (env_to_use) = env_to_use(smaller_env, val_or_more_rec_env);

                        match_tag cont {
                            Lookup => {
                                let ctrl: Return;
                                return (expr, env_to_use, cont, ctrl)
                            }
                        };
                        let ctrl: Return;
                        let cont: Lookup = hash2(env, cont);
                        return (expr, env_to_use, cont, ctrl)
                    }
                };

                let err: Error;
                return (expr, env, err, err)
            },
            Cons => {
                // TODO
                let err: Error;
                return (expr, env, err, err)
            }
        }
    })
}

fn apply_cont() -> Func {
    let make_tail_continuation = make_tail_continuation();
    func!((result, env, cont, ctrl): 4 => {
        match_tag ctrl {
            ApplyContinuation => {
                match_tag cont {
                    Terminal | Error => {
                        let ctrl: Return;
                        return (result, env, cont, ctrl)
                    },
                    Outermost => {
                        let ctrl: Return;
                        let cont: Terminal;
                        return (result, env, cont, ctrl)
                    },
                    Let => {
                        let (var, body, saved_env, cont) = unhash4(cont);
                        let binding: Cons = hash2(var, result);
                        let extended_env: Cons = hash2(binding, env);
                        let (cont) = make_tail_continuation(saved_env, cont);
                        let ctrl: Return;
                        return (result, env, cont, ctrl)
                    }
                }
            }
        };
        return (result, env, cont, ctrl)
    })
}

fn make_thunk() -> Func {
    func!((expr, env, cont, ctrl): 4 => {
        match_tag ctrl {
            MakeThunk => {
                match_tag cont {
                    Tail => {
                        let (saved_env, saved_cont) = unhash2(cont);
                        let thunk: Thunk = hash2(expr, saved_cont);
                        let cont: Dummy;
                        let ctrl: Return;
                        return (thunk, saved_env, cont, ctrl)
                    },
                    Outermost => {
                        let cont: Terminal;
                        let ctrl: Return;
                        return (expr, env, cont, ctrl)
                    }
                };
                let thunk: Thunk = hash2(expr, cont);
                let cont: Dummy;
                let ctrl: Return;
                return (thunk, env, cont, ctrl)
            }
        };
        return (expr, env, cont, ctrl)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::LurkField;
    use crate::lem::{
        circuit::SlotsCounter, pointers::Ptr, store::Store, symbol::Symbol, tag::Tag,
    };
    use bellperson::util_cs::{test_cs::TestConstraintSystem, Comparable};
    use blstrs::Scalar as Fr;

    // const NUM_INPUTS: usize = 1;
    // const NUM_AUX: usize = 111;
    // const NUM_CONSTRAINTS: usize = 258;
    // const NUM_SLOTS: SlotsCounter = SlotsCounter {
    //     hash2: 0,
    //     hash3: 0,
    //     hash4: 0,
    // };

    fn test_eval_and_constrain_aux(store: &mut Store<Fr>, pairs: Vec<(Ptr<Fr>, Ptr<Fr>)>) {
        let eval_step = eval_step();

        let slots_count = eval_step.body.count_slots();

        // assert_eq!(slots_count, NUM_SLOTS);
        eprintln!("SLOTS_COUNT: {:?}", slots_count);

        let computed_num_constraints = eval_step.num_constraints::<Fr>(&slots_count);

        // Assures that `MatchSymbol`s will work properly
        eval_step.intern_matched_symbols(store);

        let mut all_paths = vec![];

        // Auxiliary Lurk constants
        let outermost = Ptr::null(Tag::Outermost);
        let terminal = Ptr::null(Tag::Terminal);
        let error = Ptr::null(Tag::Error);
        let nil = store.intern_symbol(&Symbol::lurk_sym("nil"));

        // Stop condition: the continuation is either terminal or error
        let stop_cond = |output: &[Ptr<Fr>]| output[2] == terminal || output[2] == error;

        for (expr_in, expr_out) in pairs {
            let input = vec![expr_in, nil, outermost];
            let (frames, paths) = eval_step.call_until(input, store, stop_cond).unwrap();
            assert!(
                frames
                    .last()
                    .expect("eval should add at least one frame")
                    .output[0]
                    == expr_out
            );
            store.hydrate_z_cache();
            let mut cs = TestConstraintSystem::<Fr>::new();
            for frame in frames.iter() {
                eval_step
                    .synthesize(&mut cs, store, &slots_count, frame)
                    .unwrap();
                assert!(cs.is_satisfied());
                // assert_eq!(cs.num_inputs(), NUM_INPUTS);
                eprintln!("VARIABLES: {}", cs.aux().len());

                let num_constraints = cs.num_constraints();
                assert_eq!(computed_num_constraints, num_constraints);
                eprintln!("CONSTRAINTS: {}", num_constraints);
                // TODO: assert uniformity with `Delta` from bellperson
            }
            all_paths.extend(paths);
        }

        // TODO do we really need this?
        // eval_step.assert_all_paths_taken(&all_paths);
        assert!(false)
    }

    fn expr_in_expr_out_pairs(_store: &mut Store<Fr>) -> Vec<(Ptr<Fr>, Ptr<Fr>)> {
        let num = Ptr::num(Fr::from_u64(42));
        let nil = Ptr::null(Tag::Nil);
        let strnil = Ptr::null(Tag::Str);
        vec![(num, num), (nil, nil), (strnil, strnil)]
    }

    #[test]
    fn test_pairs() {
        let mut store = Store::default();
        let pairs = expr_in_expr_out_pairs(&mut store);
        store.hydrate_z_cache();
        test_eval_and_constrain_aux(&mut store, pairs);
    }
}
