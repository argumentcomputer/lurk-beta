use bellpepper::util_cs::Comparable;
use bellpepper_core::{test_cs::TestConstraintSystem, Delta};
use pasta_curves::pallas::Scalar as Fr;

use crate::{
    eval::lang::{DummyCoprocessor, Lang},
    field::LurkField,
    func,
    lem::{pointers::Ptr, slot::SlotsCounter, store::Store, Func, Tag},
};

/// Helper function for testing circuit synthesis.
///   - `func` is the input LEM program.
///   - `exprs` is a set of input expressions that can exercise different LEM paths,
///   therefore this parameter can be used to test circuit uniformity among all the
///   provided expressions.
///   - `expected_slots` gives the number of expected slots for each type of hash.
fn synthesize_test_helper(func: &Func, inputs: Vec<Ptr<Fr>>, expected_num_slots: SlotsCounter) {
    use crate::tag::ContTag::Outermost;
    let store = &Store::default();
    let nil = store.intern_nil();
    let outermost = Ptr::null(Tag::Cont(Outermost));

    assert_eq!(func.slots_count, expected_num_slots);

    let computed_num_constraints = func.num_constraints::<Fr>(store);

    let lang: Lang<Fr, DummyCoprocessor<Fr>> = Lang::new();

    let mut cs_prev = None;
    for input in inputs {
        let input = [input, nil, outermost];
        let (frame, _) = func
            .call(&input, store, Default::default(), &mut vec![], &lang, 0)
            .unwrap();

        let mut cs = TestConstraintSystem::<Fr>::new();

        func.synthesize_frame_aux(&mut cs, store, &frame, &lang)
            .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(computed_num_constraints, cs.num_constraints());
        if let Some(cs_prev) = cs_prev {
            // Check for all input expresssions that all frames are uniform.
            assert_eq!(cs.delta(&cs_prev, true), Delta::Equal);
        }
        cs_prev = Some(cs);
    }
}

#[test]
fn accepts_virtual_nested_match_tag() {
    let lem = func!(foo(expr_in, env_in, cont_in): 3 => {
        match expr_in.tag {
            Expr::Num => {
                let cont_out_terminal: Cont::Terminal;
                return (expr_in, env_in, cont_out_terminal);
            }
            Expr::Char => {
                match expr_in.tag {
                    // This nested match excercises the need to pass on the
                    // information that we are on a virtual branch, because a
                    // constraint will be created for `cont_out_error` and it
                    // will need to be relaxed by an implication with a false
                    // premise.
                    Expr::Num => {
                        let cont_out_error: Cont::Error;
                        return (env_in, expr_in, cont_out_error);
                    }
                }
            }
            Expr::Sym => {
                match expr_in.tag {
                    // This nested match exercises the need to relax `popcount`
                    // because there is no match but it's on a virtual path, so
                    // we don't want to be too restrictive and demand that at
                    // least one path must be taken.
                    Expr::Char => {
                        return (cont_in, cont_in, cont_in);
                    }
                }
            }
        }
    });

    let inputs = vec![Ptr::num(Fr::from_u64(42))];
    synthesize_test_helper(&lem, inputs, SlotsCounter::default());
}

#[test]
fn resolves_conflicts_of_clashing_names_in_parallel_branches() {
    let lem = func!(foo(expr_in, env_in, _cont_in): 3 => {
        match expr_in.tag {
            // This match is creating `cont_out_terminal` on two different
            // branches, which, in theory, would cause troubles at allocation
            // time. We solve this problem by calling `LEMOP::deconflict`,
            // which turns one into `Num.cont_out_terminal` and the other into
            // `Char.cont_out_terminal`.
            Expr::Num => {
                let cont_out_terminal: Cont::Terminal;
                return (expr_in, env_in, cont_out_terminal);
            }
            Expr::Char => {
                let cont_out_terminal: Cont::Terminal;
                return (expr_in, env_in, cont_out_terminal);
            }
        }
    });

    let inputs = vec![Ptr::num(Fr::from_u64(42))];
    synthesize_test_helper(&lem, inputs, SlotsCounter::default());
}

#[test]
fn handles_non_ssa() {
    let func = func!(foo(expr_in, _env_in, _cont_in): 3 => {
        let x: Expr::Cons = cons2(expr_in, expr_in);
        // The next line rewrites `x` and it should move on smoothly, matching
        // the expected number of constraints accordingly
        let x: Expr::Cons = cons2(x, x);
        let cont_out_terminal: Cont::Terminal;
        return (x, x, cont_out_terminal);
    });

    let inputs = vec![Ptr::num(Fr::from_u64(42))];
    synthesize_test_helper(&func, inputs, SlotsCounter::new((2, 0, 0, 0, 0)));
}

#[test]
fn test_simple_all_paths_delta() {
    let lem = func!(foo(expr_in, env_in, _cont_in): 3 => {
        let cont_out_terminal: Cont::Terminal;
        return (expr_in, env_in, cont_out_terminal);
    });

    let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
    synthesize_test_helper(&lem, inputs, SlotsCounter::default());
}

#[test]
fn test_match_all_paths_delta() {
    let lem = func!(foo(expr_in, env_in, _cont_in): 3 => {
        match expr_in.tag {
            Expr::Num => {
                let cont_out_terminal: Cont::Terminal;
                return (expr_in, env_in, cont_out_terminal);
            }
            Expr::Char => {
                let cont_out_error: Cont::Error;
                return (expr_in, env_in, cont_out_error);
            }
        }
    });

    let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
    synthesize_test_helper(&lem, inputs, SlotsCounter::default());
}

#[test]
fn test_hash_slots() {
    let lem = func!(foo(expr_in, env_in, cont_in): 3 => {
        let _x: Expr::Cons = cons2(expr_in, env_in);
        let _y: Expr::Cons = cons3(expr_in, env_in, cont_in);
        let _z: Expr::Cons = cons4(expr_in, env_in, cont_in, cont_in);
        let t: Cont::Terminal;
        let p: Expr::Nil;
        match expr_in.tag {
            Expr::Num => {
                let m: Expr::Cons = cons2(env_in, expr_in);
                let n: Expr::Cons = cons3(cont_in, env_in, expr_in);
                let _k: Expr::Cons = cons4(expr_in, cont_in, env_in, expr_in);
                return (m, n, t);
            }
            Expr::Char => {
                return (p, p, t);
            }
            Expr::Cons => {
                return (p, p, t);
            }
            Expr::Nil => {
                return (p, p, t);
            }
        }
    });

    let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
    synthesize_test_helper(&lem, inputs, SlotsCounter::new((2, 2, 2, 0, 0)));
}

#[test]
fn test_unhash_slots() {
    let lem = func!(foo(expr_in, env_in, cont_in): 3 => {
        let _x: Expr::Cons = cons2(expr_in, env_in);
        let _y: Expr::Cons = cons3(expr_in, env_in, cont_in);
        let _z: Expr::Cons = cons4(expr_in, env_in, cont_in, cont_in);
        let t: Cont::Terminal;
        let p: Expr::Nil;
        match expr_in.tag {
            Expr::Num => {
                let m: Expr::Cons = cons2(env_in, expr_in);
                let n: Expr::Cons = cons3(cont_in, env_in, expr_in);
                let k: Expr::Cons = cons4(expr_in, cont_in, env_in, expr_in);
                let (_m1, _m2) = decons2(m);
                let (_n1, _n2, _n3) = decons3(n);
                let (_k1, _k2, _k3, _k4) = decons4(k);
                return (m, n, t);
            }
            Expr::Char => {
                return (p, p, t);
            }
            Expr::Cons => {
                return (p, p, p);
            }
            Expr::Nil => {
                return (p, p, p);
            }
        }
    });

    let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
    synthesize_test_helper(&lem, inputs, SlotsCounter::new((3, 3, 3, 0, 0)));
}

#[test]
fn test_unhash_nested_slots() {
    let lem = func!(foo(expr_in, env_in, cont_in): 3 => {
        let _x: Expr::Cons = cons2(expr_in, env_in);
        let _y: Expr::Cons = cons3(expr_in, env_in, cont_in);
        let _z: Expr::Cons = cons4(expr_in, env_in, cont_in, cont_in);
        let t: Cont::Terminal;
        let p: Expr::Nil;
        match expr_in.tag {
            Expr::Num => {
                let m: Expr::Cons = cons2(env_in, expr_in);
                let n: Expr::Cons = cons3(cont_in, env_in, expr_in);
                let k: Expr::Cons = cons4(expr_in, cont_in, env_in, expr_in);
                let (_m1, _m2) = decons2(m);
                let (_n1, _n2, _n3) = decons3(n);
                let (_k1, _k2, _k3, _k4) = decons4(k);
                match cont_in.tag {
                    Cont::Outermost => {
                        let _a: Expr::Cons = cons2(env_in, expr_in);
                        let _b: Expr::Cons = cons3(cont_in, env_in, expr_in);
                        let _c: Expr::Cons = cons4(expr_in, cont_in, env_in, expr_in);
                        return (m, n, t);
                    }
                    Cont::Terminal => {
                        let _d: Expr::Cons = cons2(env_in, expr_in);
                        let _e: Expr::Cons = cons3(cont_in, env_in, expr_in);
                        let _f: Expr::Cons = cons4(expr_in, cont_in, env_in, expr_in);
                        return (m, n, t);
                    }
                }
            }
            Expr::Char => {
                return (p, p, t);
            }
            Expr::Cons => {
                return (p, p, p);
            }
            Expr::Nil => {
                return (p, p, p);
            }
        }
    });

    let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
    synthesize_test_helper(&lem, inputs, SlotsCounter::new((4, 4, 4, 0, 0)));
}
