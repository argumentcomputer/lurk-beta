use crate::field::FWrap;
use serde::{Deserialize, Serialize};

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

use crate::hash::PoseidonCache;
use crate::num::Num;
use crate::ptr::Ptr;
use crate::store::Store;
use crate::tag::{ExprTag, Tag};
use crate::z_ptr::{ZContPtr, ZExprPtr, ZPtr};
use crate::z_store::ZStore;
use crate::UInt;

use crate::field::ser_f;
use crate::field::LurkField;

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
/// Enum to represent a z expression.
pub enum ZExpr<F: LurkField> {
    Nil,
    Cons(ZExprPtr<F>, ZExprPtr<F>),
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(
            strategy = "any::<(FWrap<F>, ZExprPtr<F>)>().prop_map(|(x, y)| Self::Comm(x.0, y))"
        )
    )]
    Comm(#[serde(serialize_with = "ser_f")] F, ZExprPtr<F>),
    SymNil,
    SymCons(ZExprPtr<F>, ZExprPtr<F>),
    Key(ZExprPtr<F>),
    Fun {
        arg: ZExprPtr<F>,
        body: ZExprPtr<F>,
        closed_env: ZExprPtr<F>,
    },
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| Self::Num(x.0))")
    )]
    #[serde(serialize_with = "ser_f")]
    Num(F),
    StrNil,
    /// Contains a string and a pointer to the tail.
    StrCons(ZExprPtr<F>, ZExprPtr<F>),
    Thunk(ZExprPtr<F>, ZContPtr<F>),
    Char(char),
    #[serde(with = "serde_uint")]
    UInt(UInt),
}

impl<F: LurkField> std::fmt::Display for ZExpr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ZExpr::Cons(x, y) => write!(f, "({} . {})", x, y),
            ZExpr::StrCons(x, y) => write!(f, "('{}' str. {})", x, y),
            ZExpr::SymCons(x, y) => write!(f, "({} sym. {})", x, y),
            ZExpr::Comm(ff, x) => {
                write!(f, "({} comm. {})", ff.trimmed_hex_digits(), x)
            }
            ZExpr::Nil => write!(f, "nil"),
            ZExpr::StrNil => write!(f, "strnil"),
            ZExpr::SymNil => write!(f, "symnil"),
            _ => todo!(),
        }
    }
}

impl<F: LurkField> ZExpr<F> {
    pub fn z_ptr(&self, cache: &PoseidonCache<F>) -> ZExprPtr<F> {
        match self {
            ZExpr::Nil => ZPtr(ExprTag::Nil, ZStore::new().nil_z_ptr(cache).1),
            ZExpr::Cons(x, y) => ZPtr(
                ExprTag::Cons,
                cache.hash4(&[x.0.to_field(), x.1, y.0.to_field(), y.1]),
            ),
            ZExpr::Comm(f, x) => ZPtr(ExprTag::Comm, cache.hash3(&[*f, x.0.to_field(), x.1])),
            ZExpr::SymNil => ZPtr(ExprTag::Sym, F::ZERO),
            ZExpr::SymCons(x, y) => ZPtr(
                ExprTag::Sym,
                cache.hash4(&[x.0.to_field(), x.1, y.0.to_field(), y.1]),
            ),
            ZExpr::Key(sym) => ZPtr(ExprTag::Key, sym.1),
            ZExpr::Fun {
                arg,
                body,
                closed_env,
            } => ZPtr(
                ExprTag::Fun,
                cache.hash6(&[
                    arg.0.to_field(),
                    arg.1,
                    body.0.to_field(),
                    body.1,
                    closed_env.0.to_field(),
                    closed_env.1,
                ]),
            ),
            ZExpr::Num(f) => ZPtr(ExprTag::Num, *f),
            ZExpr::StrNil => ZPtr(ExprTag::Str, F::ZERO),
            ZExpr::StrCons(x, y) => ZPtr(
                ExprTag::Str,
                cache.hash4(&[x.0.to_field(), x.1, y.0.to_field(), y.1]),
            ),
            ZExpr::Thunk(x, y) => ZPtr(
                ExprTag::Thunk,
                cache.hash4(&[x.0.to_field(), x.1, y.0.to_field(), y.1]),
            ),
            ZExpr::Char(f) => ZPtr(ExprTag::Char, F::from_char(*f)),
            ZExpr::UInt(x) => match x {
                UInt::U64(x) => ZPtr(ExprTag::U64, F::from_u64(*x)),
            },
        }
    }

    pub fn from_ptr(store: &Store<F>, ptr: &Ptr<F>) -> Option<Self> {
        match ptr.tag {
            ExprTag::Nil => Some(ZExpr::Nil),
            ExprTag::Cons => store.fetch_cons(ptr).and_then(|(car, cdr)| {
                if let (Some(car), Some(cdr)) = (store.hash_expr(car), store.hash_expr(cdr)) {
                    Some(ZExpr::Cons(car, cdr))
                } else {
                    None
                }
            }),
            ExprTag::Comm => store.fetch_comm(ptr).and_then(|(secret, payload)| {
                store
                    .hash_expr(payload)
                    .map(|payload| ZExpr::Comm(secret.0, payload))
            }),
            ExprTag::Sym => store.fetch_symcons(ptr).and_then(|(tag, val)| {
                if let (Some(tag), Some(val)) = (store.hash_expr(&tag), store.hash_expr(&val)) {
                    Some(ZExpr::SymCons(tag, val))
                } else {
                    None
                }
            }),
            ExprTag::Key => store.hash_expr(ptr).map(ZExpr::Key),
            ExprTag::Fun => store.fetch_fun(ptr).and_then(|(arg, body, closed_env)| {
                if let (Some(arg), Some(body), Some(closed_env)) = (
                    store.hash_expr(arg),
                    store.hash_expr(body),
                    store.hash_expr(closed_env),
                ) {
                    Some(ZExpr::Fun {
                        arg,
                        body,
                        closed_env,
                    })
                } else {
                    None
                }
            }),
            ExprTag::Num => store.fetch_num(ptr).map(|num| match num {
                Num::U64(x) => ZExpr::Num((*x).into()),
                Num::Scalar(x) => ZExpr::Num(*x),
            }),
            ExprTag::Str => store.fetch_strcons(ptr).and_then(|(tag, val)| {
                if let (Some(tag), Some(val)) = (store.hash_expr(&tag), store.hash_expr(&val)) {
                    Some(ZExpr::StrCons(tag, val))
                } else {
                    None
                }
            }),
            ExprTag::Char => store.fetch_char(ptr).map(ZExpr::Char),
            ExprTag::U64 => store.fetch_uint(ptr).map(ZExpr::UInt),
            ExprTag::Thunk => unimplemented!(),
        }
    }
}

mod serde_uint {
    use super::*;

    pub(crate) fn serialize<S>(uint: &UInt, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match uint {
            UInt::U64(u) => u.serialize(serializer),
        }
    }

    pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<UInt, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let uint = u64::deserialize(deserializer)?;
        Ok(UInt::U64(uint))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::z_data::{from_z_data, to_z_data};
    use pasta_curves::pallas::Scalar;

    proptest! {
          #[test]
          fn prop_z_expr(x in any::<ZExpr<Scalar>>()) {
              let ser = to_z_data(&x).expect("write ZExpr");
              let de: ZExpr<Scalar> = from_z_data(&ser).expect("read ZExpr");
              assert_eq!(x, de)
          }
    }
}
