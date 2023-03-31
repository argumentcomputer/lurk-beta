// This is a temporary shim which should be merged with scalar_store
// Currently it only exists for reading store-dumps

use crate::field::FWrap;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

use anyhow::anyhow;
use std::collections::BTreeMap;

use crate::light_data::Encodable;
use crate::light_data::LightData;
use crate::scalar_store::ScalarExpression;
use crate::scalar_store::ScalarStore;
use crate::store::ScalarPtr;
use crate::sym::Sym;
use crate::tag::ExprTag;

use crate::field::LurkField;

mod light_store {
    //! This module is a prototype for a future version of scalar_store. For now,
    //! its main role is to serve as an intermediate format between a store encoded
    //! in LightData and the ScalarStore itself. Thus we call it LightStore.
    //!
    //! The expressions of a LightStore are deliberately unable to represent "immediate
    //! values", which is data that's directly encoded in the pointers themselves:
    //! * `Num` pointers
    //! * `U64` pointers
    //! * `Char` pointers
    //! * `Str` pointers with value 0 represent the empty string
    //! * `Sym` pointers with value 0 represent the root symbol
    //!
    //! As a consequence, we expect a LightStore map not to contain immediate pointers
    //! in its keys. Such data is added to the ScalarStore as the LightStore is traversed.
}

#[derive(Debug, PartialEq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
/// LightStore contains a fragment of the ScalarStore, but using the `LightExpr` type
pub struct LightStore<F: LurkField> {
    /// An analogous to the ScalarStore's scalar_map, but with `LightExpr` instead of `ScalarExpression`
    pub scalar_map: BTreeMap<ScalarPtr<F>, Option<LightExpr<F>>>,
}

impl<F: LurkField> Encodable for LightStore<F> {
    fn ser(&self) -> LightData {
        // TODO: this clone is loathsome
        self.scalar_map
            .clone()
            .into_iter()
            .collect::<Vec<(ScalarPtr<F>, Option<LightExpr<F>>)>>()
            .ser()
    }
    fn de(ld: &LightData) -> anyhow::Result<Self> {
        let pairs = Vec::<(ScalarPtr<F>, Option<LightExpr<F>>)>::de(ld)?;
        Ok(LightStore {
            scalar_map: pairs.into_iter().collect(),
        })
    }
}

impl<F: LurkField> LightStore<F> {
    fn insert_scalar_string(
        &self,
        ptr0: ScalarPtr<F>,
        store: &mut ScalarStore<F>,
    ) -> anyhow::Result<String> {
        let mut s = String::new();
        let mut tail_ptrs = vec![];
        let mut ptr = ptr0;
        let strnil_ptr = ScalarPtr::from_parts(ExprTag::Str, F::zero());

        // TODO: this needs to bail on encountering an opaque pointer
        while let Some(LightExpr::StrCons(c, cs)) = self.get(&ptr).flatten() {
            let chr = c
                .value()
                .to_char()
                .ok_or_else(|| anyhow!("Non-char head in LightExpr::StrCons"))?;
            store.insert_scalar_expression(c, Some(ScalarExpression::Char(chr)));
            s.push(chr);
            if cs != strnil_ptr {
                tail_ptrs.push(cs);
            }
            ptr = cs
        }
        // Useful when called from insert_scalar_symbol
        if s.is_empty() {
            return Err(anyhow!("encountered no StrCons in LightStore::insert_scalar_string, is this a string pointer?"));
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
        ptr0: ScalarPtr<F>,
        store: &mut ScalarStore<F>,
    ) -> anyhow::Result<Sym> {
        let mut path = Sym::root();
        let mut tail_ptrs = vec![ptr0];
        let mut ptr = ptr0;
        let symnil_ptr = ScalarPtr::from_parts(ExprTag::Sym, F::zero());

        // TODO: this needs to bail on encountering an opaque pointer
        while let Some(LightExpr::SymCons(s, ss)) = self.get(&ptr).flatten() {
            let string = if s == ScalarPtr::from_parts(ExprTag::Str, F::zero()) {
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

    fn intern_immediate(
        &self,
        ptr: ScalarPtr<F>,
        store: &mut ScalarStore<F>,
    ) -> anyhow::Result<()> {
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
            _ => return Err(anyhow!("Invalid immediate pointer: {ptr}")),
        };
        Ok(())
    }

    fn intern_non_immediate(
        &self,
        ptr: ScalarPtr<F>,
        store: &mut ScalarStore<F>,
        stack: &mut Vec<ScalarPtr<F>>,
    ) -> anyhow::Result<()> {
        match self.get(&ptr) {
            None => return Err(anyhow!("LightExpr not found for pointer {ptr}")),
            Some(None) => {
                // opaque data
                store.insert_scalar_expression(ptr, None);
            }
            Some(Some(expr)) => match (ptr.tag(), expr.clone()) {
                (ExprTag::Nil, LightExpr::Nil) => {
                    stack.push(ScalarPtr::from_parts(ExprTag::Sym, *ptr.value()));
                    store.insert_scalar_expression(ptr, Some(ScalarExpression::Nil));
                }
                (ExprTag::Cons, LightExpr::Cons(x, y)) => {
                    stack.push(x);
                    stack.push(y);
                    store.insert_scalar_expression(ptr, Some(ScalarExpression::Cons(x, y)));
                }
                (ExprTag::Comm, LightExpr::Comm(f, x)) => {
                    stack.push(x);
                    store.insert_scalar_expression(ptr, Some(ScalarExpression::Comm(f, x)));
                }
                (ExprTag::Sym, LightExpr::SymCons(_, _)) => {
                    self.insert_scalar_symbol(ptr, store)?;
                }
                (ExprTag::Str, LightExpr::StrCons(_, _)) => {
                    self.insert_scalar_string(ptr, store)?;
                }
                (tag, _) => {
                    return Err(anyhow!(
                        "Invalid pair of tag and LightExpr: ({tag}, {expr})"
                    ))
                }
            },
        };
        Ok(())
    }

    /// Eagerly traverses the LightStore starting out from a ScalarPtr, adding
    /// pointers and their respective expressions to a target ScalarStore. When
    /// handling non-immediate pointers, their corresponding expressions might
    /// add more pointers to be visited to a stack.
    ///
    /// TODO: add a cycle detection logic
    fn intern_ptr_data(
        &self,
        ptr0: ScalarPtr<F>,
        store: &mut ScalarStore<F>,
    ) -> anyhow::Result<()> {
        let mut stack = Vec::new();
        stack.push(ptr0);
        while let Some(ptr) = stack.pop() {
            if store.get_expr(&ptr).is_some() {
                continue;
            }
            if ptr.is_immediate() {
                self.intern_immediate(ptr, store)?;
            } else {
                self.intern_non_immediate(ptr, store, &mut stack)?;
            }
        }
        Ok(())
    }

    /// Convert LightStore to ScalarStore.
    fn to_scalar_store(&self) -> anyhow::Result<ScalarStore<F>> {
        let mut store = ScalarStore::default();
        for ptr in self.scalar_map.keys() {
            if ptr.is_immediate() {
                return Err(anyhow!("Immediate pointer found in LightStore: {ptr}"));
            }
            self.intern_ptr_data(*ptr, &mut store)?;
        }
        Ok(store)
    }

    fn get(&self, ptr: &ScalarPtr<F>) -> Option<Option<LightExpr<F>>> {
        self.scalar_map.get(ptr).cloned()
    }
}

impl<F: LurkField> TryFrom<LightStore<F>> for ScalarStore<F> {
    type Error = anyhow::Error;

    fn try_from(store: LightStore<F>) -> Result<Self, Self::Error> {
        store.to_scalar_store()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
/// Enum to represent a light expression.
pub enum LightExpr<F: LurkField> {
    /// Analogous to ScalarExpression::Cons
    Cons(ScalarPtr<F>, ScalarPtr<F>),
    /// Replaces ScalarExpression::Str, contains a string and a pointer to the tail.
    StrCons(ScalarPtr<F>, ScalarPtr<F>),
    /// Replaces ScalarExpression::Sym, contains a symbol and a pointer to the tail.
    SymCons(ScalarPtr<F>, ScalarPtr<F>),
    /// Analogous to ScalarExpression::Comm
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(
            strategy = "any::<(FWrap<F>, ScalarPtr<F>)>().prop_map(|(x, y)| Self::Comm(x.0, y))"
        )
    )]
    Comm(F, ScalarPtr<F>),
    /// Analogous to ScalarExpression::Nil
    Nil,
}

impl<F: LurkField> std::fmt::Display for LightExpr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LightExpr::Cons(x, y) => write!(f, "({} . {})", x, y),
            LightExpr::StrCons(x, y) => write!(f, "('{}' str. {})", x, y),
            LightExpr::SymCons(x, y) => write!(f, "({} sym. {})", x, y),
            LightExpr::Comm(ff, x) => {
                write!(f, "({} comm. {})", ff.trimmed_hex_digits(), x)
            }
            LightExpr::Nil => write!(f, "nil"),
        }
    }
}

impl<F: LurkField> Encodable for LightExpr<F> {
    fn ser(&self) -> LightData {
        match self {
            LightExpr::Cons(x, y) => {
                LightData::Cell(vec![LightData::Atom(vec![0u8]), x.ser(), y.ser()])
            }
            LightExpr::StrCons(x, y) => {
                LightData::Cell(vec![LightData::Atom(vec![1u8]), x.ser(), y.ser()])
            }
            LightExpr::SymCons(x, y) => {
                LightData::Cell(vec![LightData::Atom(vec![2u8]), x.ser(), y.ser()])
            }
            LightExpr::Comm(f, x) => {
                LightData::Cell(vec![LightData::Atom(vec![3u8]), FWrap(*f).ser(), x.ser()])
            }
            LightExpr::Nil => LightData::Atom(vec![]),
        }
    }
    fn de(ld: &LightData) -> anyhow::Result<Self> {
        match ld {
            LightData::Atom(v) => match v[..] {
                [] => Ok(LightExpr::Nil),
                _ => Err(anyhow!("LightExpr::Atom({:?})", v)),
            },
            LightData::Cell(v) => match &v[..] {
                [LightData::Atom(u), ref x, ref y] => match u[..] {
                    [0u8] => Ok(LightExpr::Cons(ScalarPtr::de(x)?, ScalarPtr::de(y)?)),
                    [1u8] => Ok(LightExpr::StrCons(ScalarPtr::de(x)?, ScalarPtr::de(y)?)),
                    [2u8] => Ok(LightExpr::SymCons(ScalarPtr::de(x)?, ScalarPtr::de(y)?)),
                    [3u8] => Ok(LightExpr::Comm(FWrap::de(x)?.0, ScalarPtr::de(y)?)),
                    _ => Err(anyhow!("LightExpr::Cell({:?})", v)),
                },
                _ => Err(anyhow!("LightExpr::Cell({:?})", v)),
            },
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use pasta_curves::pallas::Scalar;
    use std::collections::BTreeMap;

    proptest! {
        #[test]
        fn prop_light_expr(x in any::<LightExpr<Scalar>>()) {
            let ser = x.ser();
            let de  = LightExpr::de(&ser).expect("read LightExpr");
            assert_eq!(x, de)
        }

        #[test]
        fn prop_light_store(s in any::<LightStore<Scalar>>()) {
            let ser = s.ser();
            let de  = LightStore::de(&ser).expect("read LightStore");
            assert_eq!(s, de)
        }
    }

    #[test]
    fn test_convert_light_store_with_strings_and_symbols() {
        // inserts the strings "hi" and "yo", then the symbols `.hi` and `.hi.yo`
        let (str1_c1, str1_c2) = ('h', 'i');
        let (str2_c1, str2_c2) = ('y', 'o');
        let str1_c1_ptr = ScalarPtr::from_parts(ExprTag::Char, Scalar::from_char(str1_c1));
        let str1_c2_ptr = ScalarPtr::from_parts(ExprTag::Char, Scalar::from_char(str1_c2));
        let str2_c1_ptr = ScalarPtr::from_parts(ExprTag::Char, Scalar::from_char(str2_c1));
        let str2_c2_ptr = ScalarPtr::from_parts(ExprTag::Char, Scalar::from_char(str2_c2));

        let str_nil = ScalarPtr::from_parts(ExprTag::Str, Scalar::zero());
        let sym_nil = ScalarPtr::from_parts(ExprTag::Sym, Scalar::zero());

        // placeholder hashes
        let str1_ptr_half = ScalarPtr::from_parts(ExprTag::Str, Scalar::from_u64(1));
        let str1_ptr_full = ScalarPtr::from_parts(ExprTag::Str, Scalar::from_u64(2));
        let str2_ptr_half = ScalarPtr::from_parts(ExprTag::Str, Scalar::from_u64(3));
        let str2_ptr_full = ScalarPtr::from_parts(ExprTag::Str, Scalar::from_u64(4));

        let sym_ptr_half = ScalarPtr::from_parts(ExprTag::Sym, Scalar::from_u64(5));
        let sym_ptr_full = ScalarPtr::from_parts(ExprTag::Sym, Scalar::from_u64(6));

        let mut store = BTreeMap::new();
        store.insert(
            str1_ptr_half,
            Some(LightExpr::StrCons(str1_c2_ptr, str_nil)),
        );
        store.insert(
            str1_ptr_full,
            Some(LightExpr::StrCons(str1_c1_ptr, str1_ptr_half)),
        );
        store.insert(
            str2_ptr_half,
            Some(LightExpr::StrCons(str2_c2_ptr, str_nil)),
        );
        store.insert(
            str2_ptr_full,
            Some(LightExpr::StrCons(str2_c1_ptr, str2_ptr_half)),
        );

        store.insert(
            sym_ptr_half,
            Some(LightExpr::SymCons(str1_ptr_full, sym_nil)),
        );
        store.insert(
            sym_ptr_full,
            Some(LightExpr::SymCons(str2_ptr_full, sym_ptr_half)),
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
            LightStore::to_scalar_store(&LightStore { scalar_map: store }).unwrap(),
            expected_output
        );
    }
}
