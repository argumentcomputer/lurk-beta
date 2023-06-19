use crate::lem;

use super::LEM;
use anyhow::Result;

/// Lurk's step function encoded as a LEM
#[allow(dead_code)]
pub(crate) fn step() -> Result<LEM> {
    lem!(expr_in env_in cont_in {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::LurkField;
    use crate::lem::constrainer::{AllocationManager, NumSlots};
    use crate::lem::{pointers::Ptr, store::Store};
    use bellperson::util_cs::{test_cs::TestConstraintSystem, Comparable};
    use blstrs::Scalar as Fr;

    const NUM_INPUTS: usize = 13;
    const NUM_AUX: usize = 20;
    const NUM_CONSTRAINTS: usize = 29;
    const NUM_HASH_SLOTS: NumSlots = NumSlots {
        hash2: 0,
        hash3: 0,
        hash4: 0,
    };

    fn test_eval_and_constrain_aux(store: &mut Store<Fr>, pairs: Vec<(Ptr<Fr>, Ptr<Fr>)>) {
        let lem = step().unwrap();
        lem.check();

        let slots_indices = lem.lem_op.slots_indices();

        let num_hash_slots = lem.lem_op.num_hash_slots();
        assert_eq!(num_hash_slots, NUM_HASH_SLOTS);

        // Assures that `MatchSymPath`s will work properly
        lem.intern_matched_sym_paths(store);

        let mut all_frames = Vec::default();

        for (expr_in, expr_out) in pairs {
            let frames = lem.eval(expr_in, store, &slots_indices).unwrap();
            assert!(
                frames
                    .last()
                    .expect("eval should add at least one frame")
                    .output[0]
                    == expr_out
            );
            store.hydrate_z_cache();
            let mut alloc_manager = AllocationManager::default();
            for frame in frames.clone() {
                let mut cs = TestConstraintSystem::<Fr>::new();
                lem.constrain(&mut cs, &mut alloc_manager, store, &frame, &slots_indices)
                    .unwrap();
                assert!(cs.is_satisfied());
                assert_eq!(cs.num_inputs(), NUM_INPUTS);
                assert_eq!(cs.aux().len(), NUM_AUX);
                assert_eq!(cs.num_constraints(), NUM_CONSTRAINTS);
                // TODO: assert uniformity
            }
            all_frames.extend(frames);
        }

        lem.assert_all_paths_taken(&all_frames, store);
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
