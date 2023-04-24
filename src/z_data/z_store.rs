use crate::field::FWrap;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

use anyhow::anyhow;
use std::collections::BTreeMap;

use crate::z_data::ZExprPtr;
use crate::sym::Sym;
use crate::tag::ExprTag;
use crate::z_data::z_cont::ZCont;
use crate::z_data::z_expr::ZExpr;
use crate::z_data::Encodable;
use crate::z_data::ZData;

use crate::field::LurkField;

#[derive(Debug, PartialEq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
/// ZStore contains a fragment of the ScalarStore, but using the `ZExpr` type
pub struct ZStore<F: LurkField> {
    /// An analogous to the ScalarStore's scalar_map, but with `ZExpr` instead of `ScalarExpression`
    pub scalar_map: BTreeMap<ZExprPtr<F>, Option<ZExpr<F>>>,
}

#[derive(Debug, PartialEq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub enum ZEntry<F: LurkField> {
    Expr(ZExpr<F>),
    Cont(ZCont<F>),
    Opaque,
}

impl<F: LurkField> Encodable for ZStore<F> {
    fn ser(&self) -> ZData {
        // TODO: this clone is loathsome
        self.scalar_map
            .clone()
            .into_iter()
            .collect::<Vec<(ZExprPtr<F>, Option<ZExpr<F>>)>>()
            .ser()
    }
    fn de(ld: &ZData) -> anyhow::Result<Self> {
        let pairs = Vec::<(ZExprPtr<F>, Option<ZExpr<F>>)>::de(ld)?;
        Ok(ZStore {
            scalar_map: pairs.into_iter().collect(),
        })
    }
}

impl<F: LurkField> ZStore<F> {
    /// Leaf pointers are those whose values aren't hashes of any piece of data
    /// that's expected to be in the ZStore
    fn is_ptr_leaf(&self, ptr: ZExprPtr<F>) -> bool {
        match ptr.tag() {
            ExprTag::Num => true,
            ExprTag::Char => true,
            ExprTag::U64 => true,
            ExprTag::Str => *ptr.value() == F::zero(), // the empty string
            ExprTag::Sym => *ptr.value() == F::zero(), // the root symbol
            ExprTag::Key => *ptr.value() == F::zero(), // the root keyword
            _ => false,
        }
    }

    fn get(&self, ptr: &ZExprPtr<F>) -> Option<Option<ZExpr<F>>> {
        self.scalar_map.get(ptr).cloned()
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

        #[test]
        fn prop_z_store(s in any::<ZStore<Scalar>>()) {
            let ser = s.ser();
            let de  = ZStore::de(&ser).expect("read ZStore");
            assert_eq!(s, de)
        }
    }

}
