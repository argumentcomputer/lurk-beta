use crate::func;

use super::Func;

/// Lurk's step function
#[allow(dead_code)]
pub(crate) fn eval_step() -> Func {
    let reduce = reduce();
    let apply_cont = apply_cont();
    let make_thunk = make_thunk();

    func!((expr_in, env_in, cont_in): 3 => {
        let (expr, env, cont, ctrl) = reduce(expr_in, env_in, cont_in);
        let (expr, env, cont, ctrl) = apply_cont(expr, env, cont, ctrl);
        let (expr, env, cont, ctrl) = make_thunk(expr, env, cont, ctrl);
        return (expr, env, cont)
    })
    .unwrap()
}

fn reduce() -> Func {
    func!((expr_in, env_in, cont_in): 4 => {
        match_tag expr_in {
            Nil | Fun | Num | Str | Char | Comm | U64 | Key => {
                match_tag cont_in {
                    Outermost => {
                        let cont_out: Terminal;
                        let ctrl: Dummy;
                        return (expr_in, env_in, cont_out, ctrl);
                    }
                };
            }
        };
    })
    .unwrap()
}

fn apply_cont() -> Func {
    func!((expr_in, env_in, cont_in, ctrl): 4 => {
        return (expr_in, env_in, cont_in, ctrl)
    })
    .unwrap()
}

fn make_thunk() -> Func {
    func!((expr_in, env_in, cont_in, ctrl): 4 => {
        return (expr_in, env_in, cont_in, ctrl)
    })
    .unwrap()
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

    const NUM_INPUTS: usize = 1;
    const NUM_AUX: usize = 79;
    const NUM_CONSTRAINTS: usize = 154;
    const NUM_SLOTS: SlotsCounter = SlotsCounter {
        hash2: 0,
        hash3: 0,
        hash4: 0,
    };

    fn test_eval_and_constrain_aux(store: &mut Store<Fr>, pairs: Vec<(Ptr<Fr>, Ptr<Fr>)>) {
        let eval_step = eval_step();

        let slots_count = eval_step.body.count_slots();

        assert_eq!(slots_count, NUM_SLOTS);

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
