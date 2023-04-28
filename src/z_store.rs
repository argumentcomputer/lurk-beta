#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

use std::collections::BTreeMap;

use crate::hash::PoseidonCache;
use crate::sym::Sym;
use crate::tag::ExprTag;
use crate::z_cont::ZCont;
use crate::z_data::Encodable;
use crate::z_data::ZData;
use crate::z_expr::ZExpr;
use crate::z_ptr::ZContPtr;
use crate::z_ptr::ZExprPtr;
use crate::z_ptr::ZPtr;

use crate::field::LurkField;

#[derive(Debug, PartialEq, Clone, Default)]
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
    pub fn new() -> Self {
        ZStore {
            expr_map: BTreeMap::new(),
            cont_map: BTreeMap::new(),
        }
    }

    pub fn get_expr(&self, ptr: &ZExprPtr<F>) -> Option<ZExpr<F>> {
        self.expr_map.get(ptr).cloned()?
    }

    pub fn get_cont(&self, ptr: &ZContPtr<F>) -> Option<ZCont<F>> {
        self.cont_map.get(ptr).cloned()?
    }

    pub fn nil_z_ptr(&mut self) -> ZExprPtr<F> {
        self.put_symbol(
            Sym::new_from_path(false, vec!["".into(), "LURK".into(), "NIL".into()]),
            &PoseidonCache::default(),
        )
        .0
    }

    pub fn put_string(
        &mut self,
        string: String,
        poseidon_cache: &PoseidonCache<F>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut expr = ZExpr::StrNil;
        let mut ptr = expr.z_ptr(&poseidon_cache);
        for c in string.chars().rev() {
            expr = ZExpr::StrCons(ZPtr(ExprTag::Char, F::from_char(c)), ptr.clone());
            ptr = expr.z_ptr(&poseidon_cache);
        }
        (ptr, expr)
    }

    pub fn put_symbol(
        &mut self,
        sym: Sym,
        poseidon_cache: &PoseidonCache<F>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut expr = ZExpr::SymNil;
        let mut ptr = expr.z_ptr(&poseidon_cache);
        for s in sym.path().iter().rev() {
            let (str_ptr, _) = self.put_string(s.clone(), &poseidon_cache);
            expr = ZExpr::SymCons(str_ptr, ptr.clone());
            ptr = expr.z_ptr(&poseidon_cache);
        }
        (ptr, expr)
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
