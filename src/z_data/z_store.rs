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
/// A `ZStore` is a content-addressed, serializable representation of a Lurk store
///
/// Whereas a `Store` contains caches of each type of Lurk data, a `ZStore`
/// contains a generic map of pointers to expressions and a map of pointers to
/// continuations that can each be retrieved by traversing their `ZPtr` DAG
pub struct ZStore<F: LurkField> {
    pub expr_map: BTreeMap<ZExprPtr<F>, Option<ZExpr<F>>>,
    pub cont_map: BTreeMap<ZContPtr<F>, Option<ZCont<F>>>,
}

impl<F: LurkField> ZStore<F> {
    /// Creates a new, empty `ZStore`
    pub fn new() -> Self {
        ZStore {
            expr_map: BTreeMap::new(),
            cont_map: BTreeMap::new(),
        }
    }

    /// Converts an entire store to a `ZStore`
    /// WARNING: This will leak secrets used for opaque data in
    /// `Store::comm_store`. Not for use with hiding commitments
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

    /// Creates a new `ZStore` and adds all `ZExprPtrs` reachable from the hashed `expr`
    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> (Self, Option<ZExprPtr<F>>) {
        let (mut new, z_ptr) = match store.to_z_store_with_ptr(expr) {
            Ok((new, z_ptr)) => (new, z_ptr),
            _ => return (ZStore::new(), None),
        };
        let z_expr = ZExpr::from_ptr(store, expr);
        new.expr_map.insert(z_ptr, z_expr);
        (new, Some(z_ptr))
    }

    /// Converts a Lurk expression to a `ZExpr` and stores it in the `ZStore`, returning
    /// the resulting `ZExprPtr`
    pub fn insert_expr(&mut self, store: &Store<F>, expr: &Ptr<F>) -> Option<ZExprPtr<F>> {
        let z_ptr = store.hash_expr(expr)?;
        let z_expr = ZExpr::from_ptr(store, expr);
        self.expr_map.insert(z_ptr, z_expr);
        Some(z_ptr)
    }

    /// Returns the `ZExpr` immediately corresponding to the `ZExprPtr`, where "immediate" means
    /// that the `ZExprPtr`'s field element contains the literal value associated with the tag,
    /// so we can return the value without needing to retrieve it from the ZStore.
    ///
    /// E.g. in `ZExprPtr { ExprTag::U64, F::zero() }`, the `F::zero()` is the field representation
    /// of the number 0, displayed as `0x000000<...>`. Because we know the value's type is `ExprTag::U64`,
    /// we can infer that this pointer refers to a `ZExpr::UInt(UInt::U64(0u64)))` and return it.
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
            ZPtr(ExprTag::Str, val) if *val == F::ZERO => Some(ZExpr::EmptyStr),
            ZPtr(ExprTag::Sym, val) if *val == F::ZERO => Some(ZExpr::RootSym),
            _ => None,
        }
    }

    /// Returns the owned `ZExpr` corresponding to `ptr` if the former exists
    pub fn get_expr(&self, ptr: &ZExprPtr<F>) -> Option<ZExpr<F>> {
        ZStore::immediate_z_expr(ptr).or_else(|| self.expr_map.get(ptr).cloned()?)
    }

    /// If the entry is not present, or the pointer is immediate, returns `None`,
    /// otherwise updates the value in the `ZStore` and returns the old value.
    pub fn insert_z_expr(
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

    /// Returns the owned `ZCont` corresponding to `ptr` if the former exists
    pub fn get_cont(&self, ptr: &ZContPtr<F>) -> Option<ZCont<F>> {
        self.cont_map.get(ptr).cloned()?
    }

    /// Stores a null symbol in the `ZStore` and returns the resulting pointer
    pub fn nil_z_ptr(&mut self, poseidon_cache: &PoseidonCache<F>) -> ZExprPtr<F> {
        let z_ptr = self.put_symbol(Symbol::nil(), poseidon_cache).0;
        ZPtr(ExprTag::Nil, z_ptr.1)
    }

    /// Stores a string in the `ZStore` and returns the resulting pointer and `ZExpr`
    pub fn put_string(
        &mut self,
        string: String,
        poseidon_cache: &PoseidonCache<F>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut expr = ZExpr::EmptyStr;
        let mut ptr = expr.z_ptr(poseidon_cache);
        for c in string.chars().rev() {
            expr = ZExpr::Str(ZPtr(ExprTag::Char, F::from_char(c)), ptr);
            ptr = expr.z_ptr(poseidon_cache);
        }
        self.insert_z_expr(&ptr, Some(expr.clone()));
        (ptr, expr)
    }

    /// Stores a symbol in the `ZStore` and returns the resulting pointer and `ZExpr`
    pub fn put_symbol(
        &mut self,
        sym: Symbol,
        poseidon_cache: &PoseidonCache<F>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut expr = ZExpr::RootSym;
        let mut ptr = expr.z_ptr(poseidon_cache);
        for s in sym.path().iter().rev() {
            let (str_ptr, _) = self.put_string(s.clone(), poseidon_cache);
            expr = ZExpr::Sym(str_ptr, ptr);
            ptr = expr.z_ptr(poseidon_cache);
        }
        self.insert_z_expr(&ptr, Some(expr.clone()));
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
