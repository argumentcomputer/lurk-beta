use crate::field::LurkField;

use super::{shortcuts::*, tag::Tag, LEM, LEMOP};

// TODO: remove name conflicts between branches automatically instead of putting
// this burden on the LEM programmer's shoulders
pub fn step<F: LurkField>() -> Result<LEM<F>, String> {
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
                        LEMOP::MkNull(mptr("cont_out_ret"), Tag::Terminal),
                        LEMOP::SetReturn([mptr("expr_in"), mptr("env_in"), mptr("cont_out_ret")]),
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
    use crate::lem::pointers::Ptr;
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;

    #[test]
    fn check_step() {
        step::<Fr>().unwrap().check()
    }

    #[test]
    fn eval_42() {
        let expr = Ptr::num(Fr::from_u64(42));
        let (res, _) = step().unwrap().eval_res(expr).unwrap();
        assert!(res == expr);
    }

    #[test]
    fn constrain_42() {
        let expr = Ptr::num(Fr::from_u64(42));
        let lem = step().unwrap();
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
