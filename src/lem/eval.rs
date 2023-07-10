use crate::func;

use super::Func;
use anyhow::Result;

/// Lurk's step function encoded as a LEM
#[allow(dead_code)]
pub(crate) fn step() -> Result<Func> {
    func!((expr_in, env_in, cont_in): 3 => {
        match_tag expr_in {
            Num => {
                match_tag cont_in {
                    Outermost => {
                        let cont_out: Terminal;
                        return (expr_in, env_in, cont_out);
                    }
                };
            }
        };
    })
}

/*
#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::LurkField;
    use crate::lem::circuit::SlotsCounter;
    use crate::lem::{pointers::Ptr, store::Store};
    use bellperson::util_cs::{test_cs::TestConstraintSystem, Comparable};
    use blstrs::Scalar as Fr;

    const NUM_INPUTS: usize = 1;
    const NUM_AUX: usize = 19;
    const NUM_CONSTRAINTS: usize = 17;
    const NUM_SLOTS: SlotsCounter = SlotsCounter {
        hash2: 0,
        hash3: 0,
        hash4: 0,
    };

    fn test_eval_and_constrain_aux(store: &mut Store<Fr>, pairs: Vec<(Ptr<Fr>, Ptr<Fr>)>) {
        let lem = step().unwrap();
        lem.check();

        let slots_count = lem.block.count_slots();

        assert_eq!(slots_count, NUM_SLOTS);

        let computed_num_constraints = lem.num_constraints::<Fr>(&slots_count);

        // Assures that `MatchSymbol`s will work properly
        lem.intern_matched_symbols(store);

        let mut all_paths = vec![];

        for (expr_in, expr_out) in pairs {
            let (frames, paths) = lem.eval(expr_in, store).unwrap();
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
                lem.synthesize(&mut cs, store, &slots_count, frame).unwrap();
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

        lem.assert_all_paths_taken(&all_paths);
    }

    fn expr_in_expr_out_pairs(_store: &mut Store<Fr>) -> Vec<(Ptr<Fr>, Ptr<Fr>)> {
        vec![(Ptr::num(Fr::from_u64(42)), Ptr::num(Fr::from_u64(42)))]
    }

    #[test]
    fn test_pairs() {
        let mut store = Store::default();
        let pairs = expr_in_expr_out_pairs(&mut store);
        store.hydrate_z_cache();
        test_eval_and_constrain_aux(&mut store, pairs);
    }
}
*/
