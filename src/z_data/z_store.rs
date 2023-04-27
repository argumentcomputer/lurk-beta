#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

// use anyhow::anyhow;
use std::collections::BTreeMap;

use crate::hash::PoseidonCache;

use crate::z_data::z_cont::ZCont;
use crate::z_data::z_expr::ZExpr;
use crate::z_data::Encodable;
use crate::z_data::ZContPtr;
use crate::z_data::ZData;
use crate::z_data::ZExprPtr;

use crate::field::LurkField;

#[derive(Debug, PartialEq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub struct ZStore<F: LurkField> {
    pub expr_map: BTreeMap<ZExprPtr<F>, Option<ZExpr<F>>>,
    pub cont_map: BTreeMap<ZContPtr<F>, Option<ZCont<F>>>,
}

impl<F: LurkField> Encodable for ZStore<F> {
    fn ser(&self) -> ZData {
        (self.expr_map.clone(), self.cont_map.clone()).ser()
    }
    fn de(zd: &ZData) -> anyhow::Result<Self> {
        let xs: (
            BTreeMap<ZExprPtr<F>, Option<ZExpr<F>>>,
            BTreeMap<ZContPtr<F>, Option<ZCont<F>>>,
        ) = Encodable::de(zd)?;
        Ok(ZStore {
            expr_map: xs.0,
            cont_map: xs.1,
        })
    }
}

impl<F: LurkField> ZStore<F> {
    pub fn get_expr(&self, ptr: &ZExprPtr<F>) -> Option<ZExpr<F>> {
        self.expr_map.get(ptr).cloned()?
    }
    pub fn insert_expr(
        &mut self,
        cache: &PoseidonCache<F>,
        ptr: ZExprPtr<F>,
        expr: Option<ZExpr<F>>,
    ) {
        // is that it?
        self.expr_map.insert(ptr, expr);
    }

    pub fn get_cont(&self, ptr: &ZExprPtr<F>) -> Option<ZExpr<F>> {
        self.expr_map.get(ptr).cloned()?
    }
    pub fn nil_z_ptr() -> ZExprPtr<F> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pasta_curves::pallas::Scalar;

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
