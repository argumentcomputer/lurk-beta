use crate::field::FWrap;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

use anyhow::anyhow;
use std::collections::BTreeMap;

use crate::scalar_store::ScalarExpression;
use crate::scalar_store::ScalarStore;
use crate::sym::Sym;
use crate::tag::ExprTag;
use crate::z_data::Encodable;
use crate::z_data::ZData;
use crate::z_data::{ZContPtr, ZExprPtr, ZPtr};

use crate::field::LurkField;

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
/// Enum to represent a z expression.
pub enum ZExpr<F: LurkField> {
    /// Analogous to ScalarExpression::Cons
    Cons(ZExprPtr<F>, ZExprPtr<F>),
    /// Replaces ScalarExpression::Str, contains a string and a pointer to the tail.
    StrCons(ZExprPtr<F>, ZExprPtr<F>),
    /// Replaces ScalarExpression::Sym, contains a symbol and a pointer to the tail.
    SymCons(ZExprPtr<F>, ZExprPtr<F>),
    /// Analogous to ScalarExpression::Comm
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(
            strategy = "any::<(FWrap<F>, ZExprPtr<F>)>().prop_map(|(x, y)| Self::Comm(x.0, y))"
        )
    )]
    Comm(F, ZExprPtr<F>),
    /// Analogous to ScalarExpression::Nil
    Nil,
}

impl<F: LurkField> std::fmt::Display for ZExpr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ZExpr::Cons(x, y) => write!(f, "({} . {})", x, y),
            ZExpr::StrCons(x, y) => write!(f, "('{}' str. {})", x, y),
            ZExpr::SymCons(x, y) => write!(f, "({} sym. {})", x, y),
            ZExpr::Comm(ff, x) => {
                write!(f, "({} comm. {})", ff.trimmed_hex_digits(), x)
            }
            ZExpr::Nil => write!(f, "nil"),
        }
    }
}

impl<F: LurkField> Encodable for ZExpr<F> {
    fn ser(&self) -> ZData {
        match self {
            ZExpr::Cons(x, y) => ZData::Cell(vec![ZData::Atom(vec![0u8]), x.ser(), y.ser()]),
            ZExpr::StrCons(x, y) => ZData::Cell(vec![ZData::Atom(vec![1u8]), x.ser(), y.ser()]),
            ZExpr::SymCons(x, y) => ZData::Cell(vec![ZData::Atom(vec![2u8]), x.ser(), y.ser()]),
            ZExpr::Comm(f, x) => {
                ZData::Cell(vec![ZData::Atom(vec![3u8]), FWrap(*f).ser(), x.ser()])
            }
            ZExpr::Nil => ZData::Atom(vec![]),
        }
    }
    fn de(ld: &ZData) -> anyhow::Result<Self> {
        match ld {
            ZData::Atom(v) => match v[..] {
                [] => Ok(ZExpr::Nil),
                _ => Err(anyhow!("ZExpr::Atom({:?})", v)),
            },
            ZData::Cell(v) => match &v[..] {
                [ZData::Atom(u), ref x, ref y] => match u[..] {
                    [0u8] => Ok(ZExpr::Cons(ZExprPtr::de(x)?, ZExprPtr::de(y)?)),
                    [1u8] => Ok(ZExpr::StrCons(ZExprPtr::de(x)?, ZExprPtr::de(y)?)),
                    [2u8] => Ok(ZExpr::SymCons(ZExprPtr::de(x)?, ZExprPtr::de(y)?)),
                    [3u8] => Ok(ZExpr::Comm(FWrap::de(x)?.0, ZExprPtr::de(y)?)),
                    _ => Err(anyhow!("ZExpr::Cell({:?})", v)),
                },
                _ => Err(anyhow!("ZExpr::Cell({:?})", v)),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pasta_curves::pallas::Scalar;
    use std::collections::BTreeMap;

    proptest! {
          #[test]
          fn prop_z_expr(x in any::<ZExpr<Scalar>>()) {
              let ser = x.ser();
              let de  = ZExpr::de(&ser).expect("read ZExpr");
              assert_eq!(x, de)
          }
    }
}
