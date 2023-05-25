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

    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> (Self, Option<ZExprPtr<F>>) {
        let mut new = Self::new();
        let z_ptr = store.hash_expr(expr).unwrap();
        let z_expr = ZExpr::from_ptr(store, expr);
        new.expr_map.insert(z_ptr, z_expr);
        (new, Some(z_ptr))
    }

    ///// Create a new `ZStore` and add all `ZPtr`s reachable in the ZData representation of `expr`.
    //pub fn new_with_expr(
    //  store: &Store<F>,
    //  expr: &Ptr<F>,
    //) -> (Self, Option<ZExprPtr<F>>) {
    //  let mut new = Self::new();
    //  let z_ptr = new.add_one_ptr(store, expr);
    //  (new, z_ptr)
    //}

    ///// Add all ZPtrs representing and reachable from expr.
    //pub fn add_one_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) -> Option<ZExprPtr<F>> {
    //  let z_ptr = self.add_ptr(store, expr);
    //  self.finalize(store);
    //  z_ptr
    //}

    //  /// Add the `ZPtr` representing `expr`, and queue it for proceessing.
    //  pub fn add_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) -> Option<ZExprPtr<F>> {
    //      // Find the z_ptr representing ptr.
    //      if let Some(z_ptr) = store.get_expr_hash(expr) {
    //          self.add(store, expr, z_ptr);
    //          Some(z_ptr)
    //      } else {
    //          None
    //      }
    //  }

    ///// Add the `ZPtr` and `ZExpr` associated with `ptr`. The relationship between `ptr` and
    ///// `z_ptr` is not checked here, so `add` should only be called by `add_ptr` and `add_z_ptr`, which
    ///// enforce this relationship.
    //  fn add(&mut self, store: &Store<F>, ptr: &Ptr<F>, z_ptr: ZExprPtr<F>) {
    //      let mut new_pending_z_ptrs: Vec<ZPtr<F>> = Default::default();

    //      // If `z_ptr` is not already in the map, queue its children for processing.
    //      self.expr_map.entry(z_ptr).or_insert_with(|| {
    //          let z_expr = ZExpr::from_ptr(store, ptr)?;
    //          if let Some(more_z_ptrs) = Self::child_z_ptrs(&z_expr) {
    //              new_pending_z_ptrs.extend(more_z_ptrs);
    //          }
    //          Some(z_expr)
    //      });

    //      self.pending_z_ptrs.extend(new_pending_z_ptrs);
    //  }

    //  /// All the `ScalarPtr`s directly reachable from `scalar_expression`, if any.
    //  fn child_z_ptrs(z_expr: &ZExpr<F>) -> Option<Vec<ZExprPtr<F>>> {
    //      match z_expr {
    //          ZExpr::Cons(car, cdr) => Some([*car, *cdr].into()),
    //          ZExpr::Comm(_, payload) => Some([*payload].into()),
    //          ZExpr::Fun {
    //              arg,
    //              body,
    //              closed_env,
    //          } => Some([*arg, *body, *closed_env].into()),
    //	  _ => None,
    //      }
    //  }
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

use crate::z_data::{from_z_data, to_z_data, ZData};
use pasta_curves::pallas::Scalar;
use tap::TapOptional;

fn test_zstore<F: LurkField + serde::Serialize + for<'de> serde::Deserialize<'de>>() -> Store<F> {
    let zs = ZStore::<F>::default();
    let bytes = Some(ZData::to_bytes(&to_z_data(&zs).unwrap()));
    let mut s = bytes
        .and_then(|bytes| ZData::from_bytes(&bytes).ok())
        .and_then(|zd| from_z_data(&zd).ok())
        .map(|zs: ZStore<F>| ZStore::to_store(&zs))
        .tap_none(|| eprintln!("Fail"))
        .unwrap_or_default();
    s
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
            assert_eq!(s, de)
        }
    }
}
