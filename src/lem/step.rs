use std::collections::HashMap;

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
                        LEMOP::Copy(MetaPtr("expr_out_ret"), MetaPtr("expr_in")),
                        LEMOP::Copy(MetaPtr("env_out_ret"), MetaPtr("env_in")),
                        LEMOP::MkNull(MetaPtr("cont_out_ret"), Tag::Terminal),
                    ]),
                )],
                LEMOP::Seq(vec![
                    LEMOP::Copy(MetaPtr("expr_out_error_inner"), MetaPtr("expr_in")),
                    LEMOP::Copy(MetaPtr("env_out_error_inner"), MetaPtr("env_in")),
                    LEMOP::MkNull(MetaPtr("cont_out_error_inner"), Tag::Error),
                ]),
            ),
        )],
        LEMOP::Seq(vec![
            LEMOP::Copy(MetaPtr("expr_out_error_outer"), MetaPtr("expr_in")),
            LEMOP::Copy(MetaPtr("env_out_error_outer"), MetaPtr("env_in")),
            LEMOP::MkNull(MetaPtr("cont_out_error_outer"), Tag::Error),
        ]),
    );
    let to_copy = HashMap::from_iter(vec![
        ("expr_out_ret", "expr_out"),
        ("expr_out_error_inner", "expr_out"),
        ("expr_out_error_outer", "expr_out"),
        ("env_out_ret", "env_out"),
        ("env_out_error_inner", "env_out"),
        ("env_out_error_outer", "env_out"),
        ("cont_out_ret", "cont_out"),
        ("cont_out_error_inner", "cont_out"),
        ("cont_out_error_outer", "cont_out"),
    ]);
    let output = ["expr_out", "env_out", "cont_out"];
    LEM {
        input,
        lem_op,
        to_copy,
        output,
    }
}

#[cfg(test)]
mod tests {
    use crate::lem::{
        pointers::{Ptr, PtrVal},
        tag::Tag,
    };
    use blstrs::Scalar;

    #[test]
    fn check_step() {
        super::step::<Scalar>().check()
    }

    #[test]
    fn eval_42() {
        let expr = Ptr {
            tag: Tag::Num,
            val: PtrVal::Field(Scalar::from(42)),
        };
        let (res, _) = super::step().eval_res(expr).unwrap();
        assert!(res == expr);
    }
}
