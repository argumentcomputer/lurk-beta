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

fn reduce() -> Func {
    func!((expr, env, cont): 4 => {
        match_tag cont {
            Terminal | Error => {
                let ctrl: Return;
                return (expr, env, cont, ctrl)
            }
            _ => {
                match_tag expr {
                    Nil | Fun | Num | Str | Char | Comm | U64 | Key => {
                        let ctrl: ApplyContinuation;
                        return (expr, env, cont, ctrl);
                    },
                    Thunk => {
                        let (thunk_expr, thunk_continuation) = unhash2(expr);
                        let ctrl: MakeThunk;
                        return (thunk_expr, env, thunk_continuation, ctrl);
                    },
                    Sym => {
                        match_symbol expr {
                            "nil" | "t" => {
                                let ctrl: ApplyContinuation;
                                return (expr, env, cont, ctrl);
                            },
                            _ => {
                                match_tag env {
                                    Nil => {
                                        let err: Error;
                                        return (expr, env, err, err);
                                    },
                                    _ => {
                                        let (binding, smaller_env) = unhash2(env);
                                        match_tag binding {
                                            Nil => {
                                                let err: Error;
                                                return (expr, env, err, err);
                                            }
                                            _ => {
                                                let (var_or_rec_binding, val_or_more_rec_env) =
                                                    unhash2(binding);
                                                match_tag var_or_rec_binding {
                                                    Sym => {
                                                        // TODO
                                                        let err: Error;
                                                        return (expr, env, err, err);
                                                    },
                                                    Cons => {
                                                        // TODO
                                                        let err: Error;
                                                        return (expr, env, err, err);
                                                    },
                                                    _ => {
                                                        let err: Error;
                                                        return (expr, env, err, err);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    },
                    Cons => {
                        // TODO
                        let err: Error;
                        return (expr, env, err, err);
                    }
                };
            }
        };
    })
}

fn apply_cont() -> Func {
    func!((expr, env, cont, ctrl): 4 => {
        match_tag ctrl {
            ApplyContinuation => {
                match_tag cont {
                    Terminal | Error => {
                        let ctrl: Return;
                        return (expr, env, cont, ctrl)
                    },
                    Outermost => {
                        let ctrl: Return;
                        let cont: Terminal;
                        return (expr, env, cont, ctrl)
                    }
                }
            },
            _ => {
                return (expr, env, cont, ctrl)
            }
        };
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
                    },
                    _ => {
                        let thunk: Thunk = hash2(expr, cont);
                        let cont: Dummy;
                        let ctrl: Return;
                        return (thunk, env, cont, ctrl)
                    }
                }
            }
            _ => {
                return (expr, env, cont, ctrl)
            }
        };
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
