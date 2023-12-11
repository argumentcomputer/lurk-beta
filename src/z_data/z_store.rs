#[cfg(not(target_arch = "wasm32"))]
use lurk_macros::serde_test;
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};

use std::collections::BTreeMap;

use crate::hash::PoseidonCache;
use crate::symbol::Symbol;
use crate::tag::ExprTag;
use crate::uint::UInt;
use crate::z_cont::ZCont;
use crate::z_expr::ZExpr;
use crate::z_ptr::ZContPtr;
use crate::z_ptr::ZExprPtr;
use crate::z_ptr::ZPtr;

use crate::field::LurkField;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Default)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
#[cfg_attr(
    not(target_arch = "wasm32"),
    serde_test(types(pasta_curves::pallas::Scalar), zdata(true))
)]
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
            ZPtr(ExprTag::Key, val) if *val == F::ZERO => Some(ZExpr::RootSym),
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
        let z_ptr = self
            .put_symbol(&crate::state::lurk_sym("nil"), poseidon_cache)
            .0;
        ZPtr(ExprTag::Nil, z_ptr.1)
    }

    /// Stores a string in the `ZStore` and returns the resulting pointer and `ZExpr`
    pub fn put_string(
        &mut self,
        string: &str,
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
        sym: &Symbol,
        poseidon_cache: &PoseidonCache<F>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut expr = ZExpr::RootSym;
        let mut ptr = expr.z_ptr(poseidon_cache);
        for s in sym.path() {
            let (str_ptr, _) = self.put_string(s, poseidon_cache);
            expr = ZExpr::Sym(str_ptr, ptr);
            ptr = expr.z_ptr(poseidon_cache);
        }
        self.insert_z_expr(&ptr, Some(expr.clone()));
        (ptr, expr)
    }
}
