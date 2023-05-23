use thiserror::Error;

mod de;
mod ser;

pub use de::from_z_data;
pub use ser::to_z_data;

#[derive(Error, Debug)]
pub enum SerdeError {
    #[error("Function error")]
    Function(String),
    #[error("Type error")]
    Type(String),
}

impl serde::ser::Error for SerdeError {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Function(msg.to_string())
    }
}

impl serde::de::Error for SerdeError {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Function(msg.to_string())
    }
}

#[cfg(test)]
mod tests {
    use crate::field::FWrap;
    use crate::tag::{ContTag, ExprTag};
    use crate::tag::{Op1, Op2};
    use crate::z_data::z_cont::ZCont;
    use crate::z_data::z_ptr::{ZContPtr, ZExprPtr};
    use crate::z_data::{from_z_data, to_z_data};
    use crate::z_expr::ZExpr;
    use crate::z_store::ZStore;
    use pasta_curves::pallas::Scalar;
    use serde::Deserialize;
    use serde::Serialize;
    use std::collections::BTreeMap;

    fn test_roundtrip<T>(zd: T)
    where
        T: Serialize + for<'de> Deserialize<'de> + PartialEq + std::fmt::Debug,
    {
        assert_eq!(zd, from_z_data(&to_z_data(&zd).unwrap()).unwrap());
    }
    fn zexpr_roundtrip(zd: ZExpr<Scalar>) {
        assert_eq!(zd, from_z_data(&to_z_data(&zd).unwrap()).unwrap());
    }

    fn zcont_roundtrip(zd: ZCont<Scalar>) {
        assert_eq!(zd, from_z_data(&to_z_data(&zd).unwrap()).unwrap());
    }

    #[test]
    fn serde_simple_roundtrip() {
        test_roundtrip((1u8, 2u8));
        test_roundtrip((1u32, 2u64));
        test_roundtrip(String::from("Hello world"));
        test_roundtrip(vec!['a', 'b', 'c']);
        test_roundtrip(vec![String::from("Hello"), String::from("World")]);
        test_roundtrip(BTreeMap::from([
            (String::from("Hello"), 0u8),
            (String::from("World"), 1u8),
        ]));
    }

    #[test]
    fn serde_zdata_roundtrip() {
        let f = Scalar::one();
        let fwrap = FWrap(pasta_curves::Fp::from(10u64));
        let zep = ZExprPtr::from_parts(ExprTag::Sym, f);
        let zcp = ZContPtr::from_parts(ContTag::Outermost, f);

        test_roundtrip(f);
        test_roundtrip(fwrap);
        test_roundtrip(zep);
        test_roundtrip(zcp);
        test_roundtrip(zcp);
        test_roundtrip(ZStore::<Scalar>::new());

        zexpr_roundtrip(ZExpr::Nil);
        zexpr_roundtrip(ZExpr::Cons(zep, zep));
        // Failing until custom ZExpr deserialization for F
        //zexpr_roundtrip(ZExpr::Comm(f, zep));
        zexpr_roundtrip(ZExpr::SymNil);
        zexpr_roundtrip(ZExpr::SymCons(zep, zep));
        zexpr_roundtrip(ZExpr::Key(zep));
        zexpr_roundtrip(ZExpr::Fun {
            arg: zep,
            body: zep,
            closed_env: zep,
        });
        // Failing until custom ZExpr deserialization for F
        //zexpr_roundtrip(ZExpr::Num(f));
        zexpr_roundtrip(ZExpr::StrNil);
        zexpr_roundtrip(ZExpr::StrCons(zep, zep));
        zexpr_roundtrip(ZExpr::Thunk(zep, zcp));
        zexpr_roundtrip(ZExpr::Char('a'));
        // Failing until custom ZExpr deserialization for UInt wrapper type
        //zexpr_roundtrip(ZExpr::Uint(UInt::U64(0)));

        zcont_roundtrip(ZCont::Outermost);
        zcont_roundtrip(ZCont::Call0 {
            saved_env: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Call {
            unevaled_arg: zep,
            saved_env: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Call2 {
            function: zep,
            saved_env: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Tail {
            saved_env: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Error);
        zcont_roundtrip(ZCont::Lookup {
            saved_env: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Unop {
            operator: Op1::Car,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Binop {
            operator: Op2::Sum,
            saved_env: zep,
            unevaled_args: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Binop2 {
            operator: Op2::Sum,
            evaled_arg: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::If {
            unevaled_args: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Let {
            var: zep,
            body: zep,
            saved_env: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::LetRec {
            var: zep,
            body: zep,
            saved_env: zep,
            continuation: zcp,
        });
        zcont_roundtrip(ZCont::Emit { continuation: zcp });
        zcont_roundtrip(ZCont::Dummy);
        zcont_roundtrip(ZCont::Terminal);
    }
}
