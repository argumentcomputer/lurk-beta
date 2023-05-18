use crate::field::LurkField;

use super::{tag::Tag, MetaPtr, LEM, LEMOP};

// TODO: remove name conflicts between branches automatically instead of putting
// this burden on the LEM programmer's shoulders
pub fn step<F: LurkField>() -> LEM<'static, F> {
    let input = ["expr_in", "env_in", "cont_in"];
    let lem_op = LEMOP::mk_match_tag(
        MetaPtr("expr_in"),
        vec![(
            Tag::Num,
            LEMOP::mk_match_tag(
                MetaPtr("cont_in"),
                vec![(
                    Tag::Outermost,
                    LEMOP::Seq(vec![
                        LEMOP::MkNull(MetaPtr("cont_out_ret"), Tag::Terminal),
                        LEMOP::SetReturn([
                            MetaPtr("expr_in"),
                            MetaPtr("env_in"),
                            MetaPtr("cont_out_ret"),
                        ]),
                    ]),
                )],
            ),
        )],
    );
    LEM { input, lem_op }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lem::pointers::Ptr;
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;

    #[test]
    fn check_step() {
        step::<Fr>().check()
    }

    #[test]
    fn eval_42() {
        let expr = Ptr::num(Fr::from_u64(42));
        let (res, _) = step().eval_res(expr).unwrap();
        assert!(res == expr);
    }

    #[test]
    fn constrain_42() {
        let expr = Ptr::num(Fr::from_u64(42));
        let lem = step();
        let (res, mut store) = lem.eval(expr).unwrap();

        assert!(
            res.last()
                .expect("eval should add at least one step data")
                .output[0]
                == expr
        );

        for w in res.iter() {
            let mut cs = TestConstraintSystem::<Fr>::new();
            lem.constrain(&mut cs, &mut store, w).unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 69);
            assert_eq!(cs.num_inputs(), 13);
        }
    }
}
