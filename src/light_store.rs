// This is a temporary shim which should be merged with scalar_store
// Currently it only exists for reading store-dumps

#[cfg(not(target_arch = "wasm32"))]
use crate::field::FWrap;
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

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

pub struct LightStore<F: LurkField> {
    pub scalar_map: BTreeMap<ScalarPtr<F>, Option<LightExpr<F>>>,
}

impl<F: LurkField> Encodable for LightStore<F> {
    fn ser(&self) -> LightData {
        todo!()
    }
    fn de(_ld: &LightData) -> Result<Self, String> {
        todo!()
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
                    store.insert_scalar_expression(*ptr, Some(ScalarExpression::Num((*f).into())));
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
        match self.scalar_map.get(&ptr) {
            None => None,
            Some(x) => Some(x.clone()),
        }
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
        todo!()
    }
    fn de(_ld: &LightData) -> Result<Self, String> {
        todo!()
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
        println!("x {:?}", x);
        println!("ser {:?}", ser);
        assert_eq!(x, de)
    }
    }
}
