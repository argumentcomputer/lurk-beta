use crate::field::LurkField;

use super::{shortcuts::*, tag::Tag, LEM, LEMOP};

// TODO: remove name conflicts between branches automatically instead of putting
// this burden on the LEM programmer's shoulders
#[allow(dead_code)]
pub(crate) fn step<F: LurkField>() -> Result<LEM<F>, String> {
    let input = ["expr_in", "env_in", "cont_in"];
    let lem_op = match_tag(
        mptr("expr_in"),
        vec![(
            Tag::Num,
            match_tag(
                mptr("cont_in"),
                vec![(
                    Tag::Outermost,
                    LEMOP::Seq(vec![
                        LEMOP::MkNull(mptr("cont_out"), Tag::Terminal),
                        LEMOP::SetReturn([mptr("expr_in"), mptr("env_in"), mptr("cont_out")]),
                    ]),
                )],
            ),
        )],
    );
    LEM::new(input, lem_op)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lem::{pointers::Ptr, store::Store};
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;

    const NUM_INPUTS: usize = 13;
    const NUM_CONSTRAINTS: usize = 69;

    fn test_eval_and_constrain_aux(store: &mut Store<Fr>, pairs: Vec<(Ptr<Fr>, Ptr<Fr>)>) {
        let lem = step().unwrap();
        for (expr_in, expr_out) in pairs {
            let witnesses = lem.eval(expr_in, store).unwrap();
            assert!(
                witnesses
                    .last()
                    .expect("eval should add at least one step data")
                    .output[0]
                    == expr_out
            );
            for witness in witnesses {
                let mut cs = TestConstraintSystem::<Fr>::new();
                lem.constrain(&mut cs, store, &witness).unwrap();
                assert!(cs.is_satisfied());
                assert_eq!(cs.num_inputs(), NUM_INPUTS);
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
        store.deluge();
        test_eval_and_constrain_aux(&mut store, pairs);
    }
}
