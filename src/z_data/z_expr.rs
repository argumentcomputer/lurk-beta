#[cfg(not(target_arch = "wasm32"))]
use lurk_macros::serde_test;
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
use serde::{Deserialize, Serialize};

#[cfg(not(target_arch = "wasm32"))]
use crate::field::FWrap;
use crate::field::LurkField;
use crate::hash::PoseidonCache;
use crate::tag::{ExprTag, Tag};
use crate::z_ptr::{ZContPtr, ZExprPtr, ZPtr};
use crate::z_store::ZStore;
use crate::UInt;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[cfg_attr(
    not(target_arch = "wasm32"),
    serde_test(types(pasta_curves::pallas::Scalar), zdata(true))
)]
/// A `ZExpr` is the content-addressed representation of a Lurk expression, which enables
/// efficient serialization and sharing of hashed Lurk data via associated `ZExprPtr`s.
pub enum ZExpr<F: LurkField> {
    /// A null expression
    Nil,
    /// A cons list of `ZExprPtr`s
    Cons(ZExprPtr<F>, ZExprPtr<F>),
    /// A commitment, which contains an opaque value and a pointer to the hidden data in the `ZStore`
    Comm(F, ZExprPtr<F>),
    RootSym,
    RootKey,
    /// Contains a symbol (a list of strings) and a pointer to the tail.
    Sym(ZExprPtr<F>, ZExprPtr<F>),
    Key(ZExprPtr<F>, ZExprPtr<F>),
    Fun {
        arg: ZExprPtr<F>,
        body: ZExprPtr<F>,
        closed_env: ZExprPtr<F>,
    },
    /// A field element representing a number
    Num(F),
    EmptyStr,
    /// Contains a string and a pointer to the tail.
    Str(ZExprPtr<F>, ZExprPtr<F>),
    /// An unevaluated expression and continuation
    Thunk(ZExprPtr<F>, ZContPtr<F>),
    Char(char),
    UInt(UInt),
}

impl<F: LurkField> std::fmt::Display for ZExpr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ZExpr::Nil => write!(f, "nil"),
            ZExpr::Cons(x, y) => write!(f, "({x} . {y})"),
            ZExpr::Str(x, y) => write!(f, "(str {x} {y})"),
            ZExpr::Sym(x, y) => write!(f, "(sym {x} {y})"),
            ZExpr::Key(x, y) => write!(f, "(key {x} {y})"),
            ZExpr::Comm(ff, x) => {
                write!(f, "(comm {} {})", ff.trimmed_hex_digits(), x)
            }
            ZExpr::EmptyStr => write!(f, "emptystr"),
            ZExpr::RootSym => write!(f, "rootsym"),
            ZExpr::RootKey => write!(f, "rootkey"),
            ZExpr::Thunk(val, cont) => write!(f, "(thunk {val} {cont})"),
            ZExpr::Fun {
                arg,
                body,
                closed_env,
            } => write!(f, "(fun {arg} {body} {closed_env})"),
            ZExpr::Char(x) => write!(f, "(char {x})"),
            ZExpr::Num(x) => write!(f, "(num  {x:?})"),
            ZExpr::UInt(x) => write!(f, "(uint {x})"),
        }
    }
}

impl<F: LurkField> ZExpr<F> {
    /// Constructs a `ZExprPtr` from a `ZExpr`, creating a Poseidon hash
    /// from the consituent elements if needed
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
}

#[cfg(not(target_arch = "wasm32"))]
impl<F: LurkField> Arbitrary for ZExpr<F> {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            Just(ZExpr::Nil),
            any::<(ZExprPtr<F>, ZExprPtr<F>)>().prop_map(|(x, y)| ZExpr::Cons(x, y)),
            any::<(FWrap<F>, ZExprPtr<F>)>().prop_map(|(x, y)| Self::Comm(x.0, y)),
            Just(ZExpr::RootSym),
            any::<(ZExprPtr<F>, ZExprPtr<F>)>().prop_map(|(x, y)| ZExpr::Sym(x, y)),
            any::<(ZExprPtr<F>, ZExprPtr<F>)>().prop_map(|(x, y)| ZExpr::Key(x, y)),
            any::<(ZExprPtr<F>, ZExprPtr<F>, ZExprPtr<F>)>().prop_map(|(arg, body, closed_env)| {
                ZExpr::Fun {
                    arg,
                    body,
                    closed_env,
                }
            }),
            any::<FWrap<F>>().prop_map(|x| Self::Num(x.0)),
            Just(ZExpr::EmptyStr),
            any::<(ZExprPtr<F>, ZExprPtr<F>)>().prop_map(|(x, y)| ZExpr::Str(x, y)),
            any::<(ZExprPtr<F>, ZContPtr<F>)>().prop_map(|(x, y)| ZExpr::Thunk(x, y)),
            any::<char>().prop_map(|x| Self::Char(x)),
            any::<u64>().prop_map(|x| Self::UInt(UInt::U64(x))),
        ]
        .boxed()
    }
}
