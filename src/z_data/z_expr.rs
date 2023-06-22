use serde::{Deserialize, Serialize};

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

#[cfg(not(target_arch = "wasm32"))]
use crate::field::FWrap;
use crate::hash::PoseidonCache;
use crate::num::Num;
use crate::ptr::Ptr;
use crate::store::Store;
use crate::tag::{ExprTag, Tag};
use crate::z_ptr::{ZContPtr, ZExprPtr, ZPtr};
use crate::z_store::ZStore;
use crate::UInt;

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
    Comm(F, ZExprPtr<F>),
    RootSym,
    Sym(ZExprPtr<F>, ZExprPtr<F>),
    RootKey,
    Key(ZExprPtr<F>, ZExprPtr<F>),
    Fun {
        arg: ZExprPtr<F>,
        body: ZExprPtr<F>,
        closed_env: ZExprPtr<F>,
    },
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| Self::Num(x.0))")
    )]
    Num(F),
    EmptyStr,
    /// Contains a string and a pointer to the tail.
    Str(ZExprPtr<F>, ZExprPtr<F>),
    Thunk(ZExprPtr<F>, ZContPtr<F>),
    Char(char),
    UInt(UInt),
}

impl<F: LurkField> std::fmt::Display for ZExpr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ZExpr::Cons(x, y) => write!(f, "({} . {})", x, y),
            ZExpr::Str(x, y) => write!(f, "(str {} {})", x, y),
            ZExpr::Sym(x, y) => write!(f, "(sym {} {})", x, y),
            ZExpr::Key(x, y) => write!(f, "(key {} {})", x, y),
            ZExpr::Comm(ff, x) => {
                write!(f, "(comm {} {})", ff.trimmed_hex_digits(), x)
            }
            ZExpr::Nil => write!(f, "nil"),
            ZExpr::EmptyStr => write!(f, "emptystr"),
            ZExpr::RootSym => write!(f, "rootsym"),
            ZExpr::RootKey => write!(f, "rootkey"),
            ZExpr::Thunk(val, cont) => write!(f, "(thunk {} {})", val, cont),
            ZExpr::Fun {
                arg,
                body,
                closed_env,
            } => write!(f, "(fun {} {} {})", arg, body, closed_env),
            ZExpr::Char(x) => write!(f, "(char {})", x),
            ZExpr::Num(x) => write!(f, "(num  {:?})", x),
            ZExpr::UInt(x) => write!(f, "(uint {})", x),
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
            ZExpr::RootSym => ZPtr(ExprTag::Sym, F::ZERO),
            ZExpr::RootKey => ZPtr(ExprTag::Key, F::ZERO),
            ZExpr::Sym(x, y) => ZPtr(
                ExprTag::Sym,
                cache.hash4(&[x.0.to_field(), x.1, y.0.to_field(), y.1]),
            ),
            ZExpr::Key(x, y) => ZPtr(
                ExprTag::Key,
                cache.hash4(&[x.0.to_field(), x.1, y.0.to_field(), y.1]),
            ),
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
            ZExpr::EmptyStr => ZPtr(ExprTag::Str, F::ZERO),
            ZExpr::Str(x, y) => ZPtr(
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
                    Some(ZExpr::Sym(tag, val))
                } else {
                    None
                }
            }),
            ExprTag::Key => store.fetch_symcons(ptr).and_then(|(tag, val)| {
                if let (Some(tag), Some(val)) = (store.hash_expr(&tag), store.hash_expr(&val)) {
                    Some(ZExpr::Key(tag, val))
                } else {
                    None
                }
            }),
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
                    Some(ZExpr::Str(tag, val))
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
              assert_eq!(x, de);

      let ser: Vec<u8> = bincode::serialize(&x).expect("write ZExpr");
      let de: ZExpr<Scalar> = bincode::deserialize(&ser).expect("read ZExpr");
      assert_eq!(x, de);
          }
    }
}
