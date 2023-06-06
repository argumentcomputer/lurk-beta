use crate::lem;

use super::LEM;
use anyhow::Result;

/// This is Lurk's step function encoded as a LEM
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
    use crate::lem::constrainer::{AllocationManager, SlotsIndices};
    use crate::lem::{pointers::Ptr, store::Store};
    use bellperson::util_cs::{test_cs::TestConstraintSystem, Comparable};
    use blstrs::Scalar as Fr;

    const NUM_INPUTS: usize = 13;
    const NUM_AUX: usize = 22;
    const NUM_CONSTRAINTS: usize = 29;

    fn test_eval_and_constrain_aux(store: &mut Store<Fr>, pairs: Vec<(Ptr<Fr>, Ptr<Fr>)>) {
        let lem = step().unwrap();
        for (expr_in, expr_out) in pairs {
            let valuations = lem.eval(expr_in, store).unwrap();
            assert!(
                valuations
                    .last()
                    .expect("eval should add at least one step data")
                    .output[0]
                    == expr_out
            );
            store.hydrate_z_cache();
            let mut alloc_manager = AllocationManager::default();
            for valuation in valuations {
                let mut cs = TestConstraintSystem::<Fr>::new();
                lem.constrain_limited(
                    &mut cs,
                    &mut alloc_manager,
                    store,
                    &valuation,
                    &SlotsIndices::default(),
                )
                .unwrap();
                assert!(cs.is_satisfied());
                assert_eq!(cs.num_inputs(), NUM_INPUTS);
                assert_eq!(cs.aux().len(), NUM_AUX);
                assert_eq!(cs.num_constraints(), NUM_CONSTRAINTS);
            }
        }
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
