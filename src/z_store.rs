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
use crate::z_cont::ZCont;
use crate::z_data::Encodable;
use crate::z_data::ZData;
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

    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> (Self, Option<ZExprPtr<F>>) {
        let mut new = Self::new();
        let z_ptr = store.get_expr_hash(expr).unwrap();
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

    pub fn get_expr(&self, ptr: &ZExprPtr<F>) -> Option<ZExpr<F>> {
        self.expr_map.get(ptr).cloned()?
    }

    pub fn get_cont(&self, ptr: &ZContPtr<F>) -> Option<ZCont<F>> {
        self.cont_map.get(ptr).cloned()?
    }

    pub fn nil_z_ptr(&mut self, poseidon_cache: &PoseidonCache<F>) -> ZExprPtr<F> {
        self.put_symbol(Symbol::sym(vec!["lurk", "nil"]), poseidon_cache)
            .0
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

// TODO: Fix the stack overflow issue
// #[cfg(test)]
// mod tests {
//     use super::*;
//     use pasta_curves::pallas::Scalar;

//     proptest! {
//         #[test]
//         fn prop_z_store(s in any::<ZStore<Scalar>>()) {
//             let ser = s.ser();
//             let de  = ZStore::de(&ser).expect("read ZStore");
//             assert_eq!(s, de)
//         }
//     }
// }
