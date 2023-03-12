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
use crate::store::ScalarPointer;
use crate::store::ScalarPtr;
use crate::sym::Sym;
use crate::tag::ExprTag;

use crate::field::LurkField;

#[derive(Debug)]
pub struct LightStore<F: LurkField> {
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
    pub fn insert_scalar_string(&self, ptr: ScalarPtr<F>, store: &mut ScalarStore<F>) -> String {
        let mut s = String::new();
        let mut tail_ptrs = vec![];
        let mut ptr = ptr;
        while let Some(Some(LightExpr::StrCons(c, cs))) = self.get(&ptr) {
            let chr = c.value().to_char().unwrap();
            store.insert_scalar_expression(c, Some(ScalarExpression::Char(chr)));
            s.push(chr);
            tail_ptrs.push(cs);
            ptr = cs
        }
        let mut tail = String::new();
        store.insert_scalar_expression(
            ScalarPtr::from_parts(ExprTag::Str.as_field(), F::zero()),
            Some(ScalarExpression::Str(String::from(""))),
        );
        for (ptr, c) in tail_ptrs.iter().rev().zip(s.chars().rev()) {
            tail = format!("{}{}", c, tail);
            store.insert_scalar_expression(*ptr, Some(ScalarExpression::Str(tail.clone())));
        }
        store.insert_scalar_expression(ptr, Some(ScalarExpression::Str(s.clone())));
        s
    }

    pub fn insert_scalar_symbol(&self, ptr: ScalarPtr<F>, store: &mut ScalarStore<F>) -> Sym {
        let mut path = vec![];
        let mut tail_ptrs = vec![];
        let mut ptr = ptr;
        while let Some(Some(LightExpr::SymCons(s, ss))) = self.get(&ptr) {
            let string = self.insert_scalar_string(s, store);
            path.push(string);
            tail_ptrs.push(ss);
            ptr = ss
        }
        let mut tail = Sym::root();
        store.insert_scalar_expression(
            ScalarPtr::from_parts(ExprTag::Sym.as_field(), F::zero()),
            Some(ScalarExpression::Sym(Sym::root())),
        );
        for (ptr, string) in tail_ptrs.iter().rev().zip(path.iter().rev()) {
            tail = tail.extend(&[string.clone()]);
            store.insert_scalar_expression(*ptr, Some(ScalarExpression::Sym(tail.clone())));
        }
        let sym = Sym::new_from_path(false, path);
        store.insert_scalar_expression(ptr, Some(ScalarExpression::Sym(sym.clone())));
        sym
    }

    pub fn to_scalar_store(self) -> ScalarStore<F> {
        let mut store = ScalarStore::default();
        for (ptr, le) in self.scalar_map.iter() {
            match le {
                None => {
                    store.insert_scalar_expression(*ptr, None);
                }
                Some(LightExpr::Cons(x, y)) => {
                    store.insert_scalar_expression(*ptr, Some(ScalarExpression::Cons(*x, *y)));
                }
                Some(LightExpr::Comm(f, x)) => {
                    store.insert_scalar_expression(*ptr, Some(ScalarExpression::Comm(*f, *x)));
                }
                Some(LightExpr::Num(f)) => {
                    store.insert_scalar_expression(*ptr, Some(ScalarExpression::Num(*f)));
                }
                // TODO: malformed non-unicode Chars breaks this
                Some(LightExpr::Char(f)) => {
                    store.insert_scalar_expression(
                        *ptr,
                        Some(ScalarExpression::Char(f.to_char().unwrap())),
                    );
                }
                Some(LightExpr::Nil) => {
                    store.insert_scalar_expression(*ptr, Some(ScalarExpression::Nil));
                }
                Some(LightExpr::StrNil) => {
                    store.insert_scalar_expression(
                        *ptr,
                        Some(ScalarExpression::Str(String::from(""))),
                    );
                }
                // TODO: StrCons with non-char heads, opaque contents breaks this
                Some(LightExpr::StrCons(_, _)) => {
                    self.insert_scalar_string(*ptr, &mut store);
                }
                Some(LightExpr::SymNil) => {
                    store.insert_scalar_expression(*ptr, Some(ScalarExpression::Sym(Sym::root())));
                }
                // TODO: SymCons with non-string heads, opaque contents breaks this
                Some(LightExpr::SymCons(_, _)) => {
                    self.insert_scalar_symbol(*ptr, &mut store);
                }
            }
        }
        store
    }

    pub fn get(&self, ptr: &ScalarPtr<F>) -> Option<Option<LightExpr<F>>> {
        self.scalar_map.get(ptr).cloned()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub enum LightExpr<F: LurkField> {
    Cons(ScalarPtr<F>, ScalarPtr<F>),
    StrCons(ScalarPtr<F>, ScalarPtr<F>),
    SymCons(ScalarPtr<F>, ScalarPtr<F>),
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(
            strategy = "any::<(FWrap<F>, ScalarPtr<F>)>().prop_map(|(x, y)| Self::Comm(x.0, y))"
        )
    )]
    Comm(F, ScalarPtr<F>),
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| Self::Num(x.0))")
    )]
    Num(F),
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| Self::Char(x.0))")
    )]
    Char(F),
    Nil,
    StrNil,
    SymNil,
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
            LightExpr::Num(f) => LightData::Cell(vec![LightData::Atom(vec![]), FWrap(*f).ser()]),
            LightExpr::Char(f) => LightData::Cell(vec![LightData::Cell(vec![]), FWrap(*f).ser()]),
            LightExpr::Nil => LightData::Atom(vec![0u8]),
            LightExpr::StrNil => LightData::Atom(vec![1u8]),
            LightExpr::SymNil => LightData::Atom(vec![2u8]),
        }
    }
    fn de(ld: &LightData) -> anyhow::Result<Self> {
        match ld {
            LightData::Atom(v) => match v[..] {
                [0u8] => Ok(LightExpr::Nil),
                [1u8] => Ok(LightExpr::StrNil),
                [2u8] => Ok(LightExpr::SymNil),
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
                [LightData::Cell(u), ref x] => match u[..] {
                    [] => Ok(LightExpr::Char(FWrap::de(x)?.0)),
                    _ => Err(anyhow!("LightExpr::Cell({:?})", v)),
                },
                [LightData::Atom(u), ref x] => match u[..] {
                    [] => Ok(LightExpr::Num(FWrap::de(x)?.0)),
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

    proptest! {
        #[test]
        fn prop_light_data(x in any::<LightExpr<Scalar>>()) {
            let ser = x.ser();
            let de  = LightExpr::de(&ser).expect("read LightExpr");
            assert_eq!(x, de)
        }

    }
}
