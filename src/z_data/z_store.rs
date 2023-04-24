use crate::field::FWrap;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

use anyhow::anyhow;
use std::collections::BTreeMap;

use crate::z_data::ZExprPtr;
use crate::scalar_store::ScalarExpression;
use crate::scalar_store::ScalarStore;
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

    fn insert_scalar_string(
        &self,
        ptr0: ZExprPtr<F>,
        store: &mut ScalarStore<F>,
    ) -> anyhow::Result<String> {
        let mut s = String::new();
        let mut tail_ptrs = vec![];
        let mut ptr = ptr0;
        let strnil_ptr = ZExprPtr::from_parts(ExprTag::Str, F::zero());

        // TODO: this needs to bail on encountering an opaque pointer
        while let Some(ZExpr::StrCons(c, cs)) = self.get(&ptr).flatten() {
            let chr = c
                .value()
                .to_char()
                .ok_or_else(|| anyhow!("Non-char head in ZExpr::StrCons"))?;
            store.insert_scalar_expression(c, Some(ScalarExpression::Char(chr)));
            s.push(chr);
            if cs != strnil_ptr {
                tail_ptrs.push(cs);
            }
            ptr = cs
        }
        // Useful when called from insert_scalar_symbol
        if s.is_empty() {
            return Err(anyhow!(
                "encountered no StrCons in ZStore::insert_scalar_string, is this a string pointer?"
            ));
        }

        // If we've already inserted this string, no need to go through suffixes again
        if let Some(ScalarExpression::Str(old_value)) = store
            .insert_scalar_expression(ptr0, Some(ScalarExpression::Str(s.clone())))
            .flatten()
        {
            if old_value == s {
                return Ok(s);
            }
        }
        store.insert_scalar_expression(strnil_ptr, Some(ScalarExpression::Str(String::from(""))));

        let mut tail = String::new();
        for (ptr, c) in tail_ptrs.iter().rev().zip(s.chars().rev()) {
            tail = format!("{}{}", c, tail);
            store.insert_scalar_expression(*ptr, Some(ScalarExpression::Str(tail.clone())));
        }
        Ok(s)
    }

    fn insert_scalar_symbol(
        &self,
        ptr0: ZExprPtr<F>,
        store: &mut ScalarStore<F>,
    ) -> anyhow::Result<Sym> {
        let mut path = Sym::root();
        let mut tail_ptrs = vec![ptr0];
        let mut ptr = ptr0;
        let symnil_ptr = ZExprPtr::from_parts(ExprTag::Sym, F::zero());

        // TODO: this needs to bail on encountering an opaque pointer
        while let Some(ZExpr::SymCons(s, ss)) = self.get(&ptr).flatten() {
            let string = if s == ZExprPtr::from_parts(ExprTag::Str, F::zero()) {
                Ok(String::new())
            } else {
                self.insert_scalar_string(s, store)
            }?;
            path = path.child(string);
            if ss != symnil_ptr {
                tail_ptrs.push(ss);
            }
            ptr = ss
        }

        // If we've already inserted this symbol, no need to go through suffixes again
        if let Some(old_value) =
            store.insert_scalar_expression(ptr0, Some(ScalarExpression::Sym(path.clone())))
        {
            if old_value == Some(ScalarExpression::Sym(path.clone())) {
                return Ok(path);
            }
        }
        store.insert_scalar_expression(symnil_ptr, Some(ScalarExpression::Sym(Sym::root())));

        let mut tail = Sym::root();
        for (ptr, string) in tail_ptrs.iter().rev().zip(path.path().iter().rev()) {
            tail = tail.child(string.clone());
            store.insert_scalar_expression(*ptr, Some(ScalarExpression::Sym(tail.clone())));
        }
        Ok(path)
    }

    fn intern_leaf(&self, ptr: ZExprPtr<F>, store: &mut ScalarStore<F>) -> anyhow::Result<()> {
        match ptr.tag() {
            ExprTag::Num => {
                store.insert_scalar_expression(ptr, Some(ScalarExpression::Num(*ptr.value())));
            }
            ExprTag::Char => {
                let c = ptr
                    .value()
                    .to_char()
                    .ok_or_else(|| anyhow!("Invalid char pointer: {ptr}"))?;
                store.insert_scalar_expression(ptr, Some(ScalarExpression::Char(c)));
            }
            ExprTag::U64 => {
                let u = ptr
                    .value()
                    .to_u64()
                    .ok_or_else(|| anyhow!("Invalid u64 pointer: {ptr}"))?;
                store.insert_scalar_expression(ptr, Some(ScalarExpression::UInt(u.into())));
            }
            ExprTag::Str => {
                store.insert_scalar_expression(ptr, Some(ScalarExpression::Str(String::new())));
            }
            ExprTag::Sym => {
                store.insert_scalar_expression(ptr, Some(ScalarExpression::Sym(Sym::root())));
            }
            _ => return Err(anyhow!("Invalid leaf pointer: {ptr}")),
        };
        Ok(())
    }

    fn intern_non_leaf(
        &self,
        ptr: ZExprPtr<F>,
        store: &mut ScalarStore<F>,
        stack: &mut Vec<ZExprPtr<F>>,
    ) -> anyhow::Result<()> {
        match self.get(&ptr) {
            None => return Err(anyhow!("ZExpr not found for pointer {ptr}")),
            Some(None) => {
                // opaque data
                store.insert_scalar_expression(ptr, None);
            }
            Some(Some(expr)) => match (ptr.tag(), expr.clone()) {
                (ExprTag::Nil, ZExpr::Nil) => {
                    // We also need to intern the `.LURK.NIL` symbol
                    stack.push(ZExprPtr::from_parts(ExprTag::Sym, *ptr.value()));
                    store.insert_scalar_expression(ptr, Some(ScalarExpression::Nil));
                }
                (ExprTag::Cons, ZExpr::Cons(x, y)) => {
                    stack.push(x);
                    stack.push(y);
                    store.insert_scalar_expression(ptr, Some(ScalarExpression::Cons(x, y)));
                }
                (ExprTag::Comm, ZExpr::Comm(f, x)) => {
                    stack.push(x);
                    store.insert_scalar_expression(ptr, Some(ScalarExpression::Comm(f, x)));
                }
                (ExprTag::Sym, ZExpr::SymCons(_, _)) => {
                    self.insert_scalar_symbol(ptr, store)?;
                }
                (ExprTag::Str, ZExpr::StrCons(_, _)) => {
                    self.insert_scalar_string(ptr, store)?;
                }
                (tag, _) => {
                    return Err(anyhow!(
                        "Unsupported pair of tag and ZExpr: ({tag}, {expr})"
                    ))
                }
            },
        };
        Ok(())
    }

    /// Eagerly traverses the ZStore starting out from a ZExprPtr, adding
    /// pointers and their respective expressions to a target ScalarStore. When
    /// handling non-leaf pointers, their corresponding expressions might
    /// add more pointers to be visited to a stack.
    ///
    /// TODO: add a cycle detection logic
    fn intern_ptr_data(
        &self,
        ptr0: ZExprPtr<F>,
        store: &mut ScalarStore<F>,
    ) -> anyhow::Result<()> {
        let mut stack = Vec::new();
        stack.push(ptr0);
        while let Some(ptr) = stack.pop() {
            if store.get_expr(&ptr).is_some() {
                continue;
            }
            if self.is_ptr_leaf(ptr) {
                self.intern_leaf(ptr, store)?;
            } else {
                self.intern_non_leaf(ptr, store, &mut stack)?;
            }
        }
        Ok(())
    }

    /// Convert ZStore to ScalarStore.
    fn to_scalar_store(&self) -> anyhow::Result<ScalarStore<F>> {
        let mut store = ScalarStore::default();
        for ptr in self.scalar_map.keys() {
            if self.is_ptr_leaf(*ptr) {
                return Err(anyhow!("Leaf pointer found in ZStore: {ptr}"));
            }
            self.intern_ptr_data(*ptr, &mut store)?;
        }
        Ok(store)
    }

    fn get(&self, ptr: &ZExprPtr<F>) -> Option<Option<ZExpr<F>>> {
        self.scalar_map.get(ptr).cloned()
    }
}

impl<F: LurkField> TryFrom<ZStore<F>> for ScalarStore<F> {
    type Error = anyhow::Error;

    fn try_from(store: ZStore<F>) -> Result<Self, Self::Error> {
        store.to_scalar_store()
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

    #[test]
    fn test_convert_z_store_with_strings_and_symbols() {
        // inserts the strings "hi" and "yo", then the symbols `.hi` and `.hi.yo`
        let (str1_c1, str1_c2) = ('h', 'i');
        let (str2_c1, str2_c2) = ('y', 'o');
        let str1_c1_ptr = ZExprPtr::from_parts(ExprTag::Char, Scalar::from_char(str1_c1));
        let str1_c2_ptr = ZExprPtr::from_parts(ExprTag::Char, Scalar::from_char(str1_c2));
        let str2_c1_ptr = ZExprPtr::from_parts(ExprTag::Char, Scalar::from_char(str2_c1));
        let str2_c2_ptr = ZExprPtr::from_parts(ExprTag::Char, Scalar::from_char(str2_c2));

        let str_nil = ZExprPtr::from_parts(ExprTag::Str, Scalar::zero());
        let sym_nil = ZExprPtr::from_parts(ExprTag::Sym, Scalar::zero());

        // placeholder hashes
        let str1_ptr_half = ZExprPtr::from_parts(ExprTag::Str, Scalar::from_u64(1));
        let str1_ptr_full = ZExprPtr::from_parts(ExprTag::Str, Scalar::from_u64(2));
        let str2_ptr_half = ZExprPtr::from_parts(ExprTag::Str, Scalar::from_u64(3));
        let str2_ptr_full = ZExprPtr::from_parts(ExprTag::Str, Scalar::from_u64(4));

        let sym_ptr_half = ZExprPtr::from_parts(ExprTag::Sym, Scalar::from_u64(5));
        let sym_ptr_full = ZExprPtr::from_parts(ExprTag::Sym, Scalar::from_u64(6));

        let mut store = BTreeMap::new();
        store.insert(str1_ptr_half, Some(ZExpr::StrCons(str1_c2_ptr, str_nil)));
        store.insert(
            str1_ptr_full,
            Some(ZExpr::StrCons(str1_c1_ptr, str1_ptr_half)),
        );
        store.insert(str2_ptr_half, Some(ZExpr::StrCons(str2_c2_ptr, str_nil)));
        store.insert(
            str2_ptr_full,
            Some(ZExpr::StrCons(str2_c1_ptr, str2_ptr_half)),
        );

        store.insert(sym_ptr_half, Some(ZExpr::SymCons(str1_ptr_full, sym_nil)));
        store.insert(
            sym_ptr_full,
            Some(ZExpr::SymCons(str2_ptr_full, sym_ptr_half)),
        );

        let expected_output = {
            let mut output = ScalarStore::default();

            output.insert_scalar_expression(str1_c1_ptr, Some(ScalarExpression::Char(str1_c1)));
            output.insert_scalar_expression(str1_c2_ptr, Some(ScalarExpression::Char(str1_c2)));
            output.insert_scalar_expression(str2_c1_ptr, Some(ScalarExpression::Char(str2_c1)));
            output.insert_scalar_expression(str2_c2_ptr, Some(ScalarExpression::Char(str2_c2)));

            output.insert_scalar_expression(str_nil, Some(ScalarExpression::Str(String::new())));

            let str1 = str1_c1.to_string() + &str1_c2.to_string();
            let str2 = str2_c1.to_string() + &str2_c2.to_string();
            output.insert_scalar_expression(
                str1_ptr_half,
                Some(ScalarExpression::Str(str1_c2.to_string())),
            );
            output
                .insert_scalar_expression(str1_ptr_full, Some(ScalarExpression::Str(str1.clone())));
            output.insert_scalar_expression(
                str2_ptr_half,
                Some(ScalarExpression::Str(str2_c2.to_string())),
            );

            let sym_root = Sym::root();
            output.insert_scalar_expression(sym_nil, Some(ScalarExpression::Sym(sym_root.clone())));
            output
                .insert_scalar_expression(str2_ptr_full, Some(ScalarExpression::Str(str2.clone())));
            let sym_half = sym_root.child(str1);
            let sym_full = sym_half.child(str2);
            output.insert_scalar_expression(sym_ptr_half, Some(ScalarExpression::Sym(sym_half)));
            output.insert_scalar_expression(sym_ptr_full, Some(ScalarExpression::Sym(sym_full)));

            output
        };

        assert_eq!(
            ZStore::to_scalar_store(&ZStore { scalar_map: store }).unwrap(),
            expected_output
        );
    }
}
