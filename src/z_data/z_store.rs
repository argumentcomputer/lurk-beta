#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};

use std::collections::BTreeMap;

use crate::hash::PoseidonCache;
use crate::ptr::Ptr;
use crate::store::Store;
use crate::symbol::Symbol;
use crate::tag::ExprTag;
use crate::uint::UInt;
use crate::z_cont::ZCont;
use crate::z_expr::ZExpr;
use crate::z_ptr::ZContPtr;
use crate::z_ptr::ZExprPtr;
use crate::z_ptr::ZPtr;

use crate::field::LurkField;

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone, Default)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub struct ZStore<F: LurkField> {
    pub expr_map: BTreeMap<ZExprPtr<F>, Option<ZExpr<F>>>,
    pub cont_map: BTreeMap<ZContPtr<F>, Option<ZCont<F>>>,
}

impl<F: LurkField> ZStore<F> {
    pub fn new() -> Self {
        ZStore {
            expr_map: BTreeMap::new(),
            cont_map: BTreeMap::new(),
        }
    }

    // Convert entire store to ZStore
    pub fn to_z_store(store: &mut Store<F>) -> Self {
        store.hydrate_scalar_cache();
        let mut zstore = ZStore::new();
        for zptr in store.z_expr_ptr_map.keys_cloned() {
            let ptr = store.z_expr_ptr_map.get(&zptr).unwrap();
            let zexpr = store.to_z_expr(ptr);
            zstore.expr_map.insert(zptr, zexpr);
        }
        for zptr in store.z_cont_ptr_map.keys_cloned() {
            let ptr = store.z_cont_ptr_map.get(&zptr).unwrap();
            let zcont = store.to_z_cont(ptr);
            zstore.cont_map.insert(zptr, zcont);
        }
        zstore
    }

    // TODO: Change this back to only convert subtree of Store
    pub fn new_with_expr(store: &mut Store<F>, expr: &Ptr<F>) -> (Self, Option<ZExprPtr<F>>) {
        let mut new = Self::to_z_store(store);
        let z_ptr = store.hash_expr(expr).unwrap();
        let z_expr = ZExpr::from_ptr(store, expr);
        new.expr_map.insert(z_ptr, z_expr);
        (new, Some(z_ptr))
    }

    pub fn immediate_z_expr(ptr: &ZExprPtr<F>) -> Option<ZExpr<F>> {
        match ptr {
            ZPtr(ExprTag::U64, val) => {
                let x = F::to_u64(val)?;
                Some(ZExpr::UInt(UInt::U64(x)))
            }
            ZPtr(ExprTag::Char, val) => {
                let x = F::to_char(val)?;
                Some(ZExpr::Char(x))
            }
            ZPtr(ExprTag::Num, val) => Some(ZExpr::Num(*val)),
            ZPtr(ExprTag::Str, val) if *val == F::ZERO => Some(ZExpr::StrNil),
            ZPtr(ExprTag::Sym, val) if *val == F::ZERO => Some(ZExpr::SymNil),
            _ => None,
        }
    }

    pub fn get_expr(&self, ptr: &ZExprPtr<F>) -> Option<ZExpr<F>> {
        if let Some(expr) = ZStore::immediate_z_expr(ptr) {
            Some(expr)
        } else {
            self.expr_map.get(ptr).cloned()?
        }
    }

    /// if the entry is not present, or the pointer is immediate, return None,
    /// otherwise update the value and return the old value. If the
    pub fn insert_expr(
        &mut self,
        ptr: &ZExprPtr<F>,
        expr: Option<ZExpr<F>>,
    ) -> Option<Option<ZExpr<F>>> {
        if ZStore::immediate_z_expr(ptr).is_some() {
            None
        } else {
            self.expr_map.insert(*ptr, expr)
        }
    }

    pub fn get_cont(&self, ptr: &ZContPtr<F>) -> Option<ZCont<F>> {
        self.cont_map.get(ptr).cloned()?
    }

    pub fn nil_z_ptr(&mut self, poseidon_cache: &PoseidonCache<F>) -> ZExprPtr<F> {
        let z_ptr = self.put_symbol(Symbol::nil(), poseidon_cache).0;
        ZPtr(ExprTag::Nil, z_ptr.1)
    }

    pub fn put_string(
        &mut self,
        string: String,
        poseidon_cache: &PoseidonCache<F>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut expr = ZExpr::StrNil;
        let mut ptr = expr.z_ptr(poseidon_cache);
        for c in string.chars().rev() {
            expr = ZExpr::StrCons(ZPtr(ExprTag::Char, F::from_char(c)), ptr);
            ptr = expr.z_ptr(poseidon_cache);
        }
        (ptr, expr)
    }

    pub fn put_symbol(
        &mut self,
        sym: Symbol,
        poseidon_cache: &PoseidonCache<F>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut expr = ZExpr::SymNil;
        let mut ptr = expr.z_ptr(poseidon_cache);
        for s in sym.path().iter().rev() {
            let (str_ptr, _) = self.put_string(s.clone(), poseidon_cache);
            expr = ZExpr::SymCons(str_ptr, ptr);
            ptr = expr.z_ptr(poseidon_cache);
        }
        (ptr, expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::z_data::{from_z_data, to_z_data};
    use pasta_curves::pallas::Scalar;

    proptest! {
        #[test]
        fn prop_z_store(s in any::<ZStore<Scalar>>()) {
            let ser = to_z_data(&s).expect("write ZStore");
            let de: ZStore<Scalar> = from_z_data(&ser).expect("read ZStore");
            assert_eq!(s, de);

      let ser: Vec<u8> = bincode::serialize(&s).expect("write ZStore");
      let de: ZStore<Scalar> = bincode::deserialize(&ser).expect("read ZStore");
      assert_eq!(s, de);
        }
    }
}
