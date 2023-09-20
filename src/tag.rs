use lurk_macros::TryFromRepr;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde_repr::{Deserialize_repr, Serialize_repr};
use std::{convert::TryFrom, fmt};

use crate::field::LurkField;
use crate::ptr::TypePredicates;

pub trait Tag:
    Into<u16> + TryFrom<u16, Error = anyhow::Error> + Copy + Sized + std::hash::Hash + Eq + fmt::Debug
{
    fn from_field<F: LurkField>(f: &F) -> Option<Self>;
    fn to_field<F: LurkField>(&self) -> F;

    /// This explicitly defines a shortcut to access the canonical
    /// byte representation of the field element associated to a
    /// tag. We expect some tag types to be able to improve upon it.
    fn to_field_bytes<F: LurkField>(&self) -> F::Repr {
        self.to_field::<F>().to_repr()
    }
}

/// A tag for expressions. Note that ExprTag, ContTag, Op1, Op2 all live in the same u16 namespace
#[derive(
    Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize_repr, Deserialize_repr, TryFromRepr,
)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[repr(u16)]
pub enum ExprTag {
    Nil = 0b0000_0000_0000_0000,
    Cons,
    Sym,
    Fun,
    Num,
    Thunk,
    Str,
    Char,
    Comm,
    U64,
    Key,
}

impl From<ExprTag> for u16 {
    fn from(val: ExprTag) -> Self {
        val as u16
    }
}

impl From<ExprTag> for u64 {
    fn from(val: ExprTag) -> Self {
        val as u64
    }
}

impl fmt::Display for ExprTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprTag::Nil => write!(f, "nil#"),
            ExprTag::Cons => write!(f, "cons#"),
            ExprTag::Sym => write!(f, "sym#"),
            ExprTag::Fun => write!(f, "fun#"),
            ExprTag::Num => write!(f, "num#"),
            ExprTag::Thunk => write!(f, "thunk#"),
            ExprTag::Str => write!(f, "str#"),
            ExprTag::Key => write!(f, "key#"),
            ExprTag::Char => write!(f, "char#"),
            ExprTag::Comm => write!(f, "comm#"),
            ExprTag::U64 => write!(f, "u64#"),
        }
    }
}

impl TypePredicates for ExprTag {
    fn is_fun(&self) -> bool {
        matches!(self, ExprTag::Fun)
    }
    fn is_self_evaluating(&self) -> bool {
        match self {
            Self::Cons | Self::Thunk | Self::Sym => false,
            Self::Nil
            | Self::Fun
            | Self::Num
            | Self::Str
            | Self::Char
            | Self::Comm
            | Self::U64
            | Self::Key => true,
        }
    }

    fn is_potentially(&self, tag: Self) -> bool {
        self == &tag || !self.is_self_evaluating()
    }
}

impl Tag for ExprTag {
    fn from_field<F: LurkField>(f: &F) -> Option<Self> {
        Self::try_from(f.to_u16()?).ok()
    }

    fn to_field<F: LurkField>(&self) -> F {
        F::from(*self as u64)
    }

    fn to_field_bytes<F: LurkField>(&self) -> F::Repr {
        let mut res = F::Repr::default();
        let u: u16 = (*self).into();
        res.as_mut()[..2].copy_from_slice(&u.to_le_bytes());
        res
    }
}

/// A tag for continuations. Note that ExprTag, ContTag, Op1, Op2 all live in the same u16 namespace
#[derive(
    Serialize_repr, Deserialize_repr, Debug, Copy, Clone, PartialEq, Eq, Hash, TryFromRepr,
)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[repr(u16)]
pub enum ContTag {
    Outermost = 0b0001_0000_0000_0000,
    Call0,
    Call,
    Call2,
    Tail,
    Error,
    Lookup,
    Unop,
    Binop,
    Binop2,
    If,
    Let,
    LetRec,
    Dummy,
    Terminal,
    Emit,
    Cproc,
}

impl From<ContTag> for u16 {
    fn from(val: ContTag) -> Self {
        val as u16
    }
}

impl From<ContTag> for u64 {
    fn from(val: ContTag) -> Self {
        val as u64
    }
}

impl Tag for ContTag {
    fn from_field<F: LurkField>(f: &F) -> Option<Self> {
        Self::try_from(f.to_u16()?).ok()
    }

    fn to_field<F: LurkField>(&self) -> F {
        F::from(*self as u64)
    }

    fn to_field_bytes<F: LurkField>(&self) -> F::Repr {
        let mut res = F::Repr::default();
        let u: u16 = (*self).into();
        res.as_mut()[..2].copy_from_slice(&u.to_le_bytes());
        res
    }
}

impl fmt::Display for ContTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ContTag::Outermost => write!(f, "outermost#"),
            ContTag::Call0 => write!(f, "call0#"),
            ContTag::Call => write!(f, "call#"),
            ContTag::Call2 => write!(f, "call2#"),
            ContTag::Tail => write!(f, "tail#"),
            ContTag::Error => write!(f, "error#"),
            ContTag::Lookup => write!(f, "lookup#"),
            ContTag::Unop => write!(f, "unop#"),
            ContTag::Binop => write!(f, "binop#"),
            ContTag::Binop2 => write!(f, "binop2#"),
            ContTag::If => write!(f, "if#"),
            ContTag::Let => write!(f, "let#"),
            ContTag::LetRec => write!(f, "letrec#"),
            ContTag::Dummy => write!(f, "dummy#"),
            ContTag::Terminal => write!(f, "terminal#"),
            ContTag::Emit => write!(f, "emit#"),
            ContTag::Cproc => write!(f, "cproc#"),
        }
    }
}

#[derive(
    Copy,
    Clone,
    Debug,
    PartialEq,
    PartialOrd,
    Eq,
    Hash,
    Serialize_repr,
    Deserialize_repr,
    TryFromRepr,
)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[repr(u16)]
pub enum Op1 {
    Car = 0b0010_0000_0000_0000,
    Cdr,
    Atom,
    Emit,
    Open,
    Secret,
    Commit,
    Num,
    Comm,
    Char,
    Eval,
    U64,
}

impl From<Op1> for u16 {
    fn from(val: Op1) -> Self {
        val as u16
    }
}

impl From<Op1> for u64 {
    fn from(val: Op1) -> Self {
        val as u64
    }
}

pub trait Op
where
    Self: 'static,
{
    fn symbol_name(&self) -> &'static str;
    fn all() -> Vec<&'static Self>;
    fn supports_arity(&self, n: usize) -> bool;
    fn all_symbol_names() -> Vec<&'static str> {
        Self::all().iter().map(|x| Self::symbol_name(*x)).collect()
    }
}

impl Tag for Op1 {
    fn from_field<F: LurkField>(f: &F) -> Option<Self> {
        Self::try_from(f.to_u16()?).ok()
    }

    fn to_field<F: LurkField>(&self) -> F {
        F::from(*self as u64)
    }

    fn to_field_bytes<F: LurkField>(&self) -> F::Repr {
        let mut res = F::Repr::default();
        let u: u16 = (*self).into();
        res.as_mut()[..2].copy_from_slice(&u.to_le_bytes());
        res
    }
}

impl Op for Op1 {
    fn symbol_name(&self) -> &'static str {
        match self {
            Op1::Car => "car",
            Op1::Cdr => "cdr",
            Op1::Atom => "atom",
            Op1::Emit => "emit",
            Op1::Open => "open",
            Op1::Secret => "secret",
            Op1::Commit => "commit",
            Op1::Num => "num",
            Op1::Comm => "comm",
            Op1::Char => "char",
            Op1::Eval => "eval",
            Op1::U64 => "u64",
        }
    }

    fn all() -> Vec<&'static Self> {
        vec![
            &Op1::Car,
            &Op1::Cdr,
            &Op1::Atom,
            &Op1::Emit,
            &Op1::Open,
            &Op1::Secret,
            &Op1::Commit,
            &Op1::Num,
            &Op1::Comm,
            &Op1::Char,
            &Op1::Eval,
            &Op1::U64,
        ]
    }

    fn supports_arity(&self, n: usize) -> bool {
        matches!((self, n), (Op1::Eval, 1 | 2) | (_, 1))
    }
}

impl fmt::Display for Op1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op1::Car => write!(f, "car#"),
            Op1::Cdr => write!(f, "cdr#"),
            Op1::Atom => write!(f, "atom#"),
            Op1::Emit => write!(f, "emit#"),
            Op1::Open => write!(f, "open#"),
            Op1::Secret => write!(f, "secret#"),
            Op1::Commit => write!(f, "commit#"),
            Op1::Num => write!(f, "num#"),
            Op1::Comm => write!(f, "comm#"),
            Op1::Char => write!(f, "char#"),
            Op1::Eval => write!(f, "eval#"),
            Op1::U64 => write!(f, "u64#"),
        }
    }
}

#[derive(
    Copy,
    Clone,
    Debug,
    PartialEq,
    PartialOrd,
    Eq,
    Hash,
    Serialize_repr,
    Deserialize_repr,
    TryFromRepr,
)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[repr(u16)]
pub enum Op2 {
    Sum = 0b0011_0000_0000_0000,
    Diff,
    Product,
    Quotient,
    Equal,
    NumEqual,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Cons,
    StrCons,
    Begin,
    Hide,
    Modulo,
    Eval,
}

impl From<Op2> for u16 {
    fn from(val: Op2) -> Self {
        val as u16
    }
}

impl From<Op2> for u64 {
    fn from(val: Op2) -> Self {
        val as u64
    }
}

impl Tag for Op2 {
    fn from_field<F: LurkField>(f: &F) -> Option<Self> {
        Self::try_from(f.to_u16()?).ok()
    }

    fn to_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(*self as u64)
    }

    fn to_field_bytes<F: LurkField>(&self) -> F::Repr {
        let mut res = F::Repr::default();
        let u: u16 = (*self).into();
        res.as_mut()[..2].copy_from_slice(&u.to_le_bytes());
        res
    }
}

impl Op2 {
    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
            Op2::Sum
                | Op2::Diff
                | Op2::Product
                | Op2::Quotient
                | Op2::Less
                | Op2::Greater
                | Op2::LessEqual
                | Op2::GreaterEqual
                | Op2::NumEqual
                | Op2::Modulo
        )
    }
}

impl Op for Op2 {
    fn symbol_name(&self) -> &'static str {
        match self {
            Op2::Sum => "+",
            Op2::Diff => "-",
            Op2::Product => "*",
            Op2::Quotient => "/",
            Op2::Equal => "eq",
            Op2::NumEqual => "=",
            Op2::Less => "<",
            Op2::Greater => ">",
            Op2::LessEqual => "<=",
            Op2::GreaterEqual => ">=",
            Op2::Cons => "cons",
            Op2::StrCons => "strcons",
            Op2::Begin => "begin",
            Op2::Hide => "hide",
            Op2::Modulo => "%",
            Op2::Eval => "eval",
        }
    }

    fn all() -> Vec<&'static Self> {
        vec![
            &Op2::Sum,
            &Op2::Diff,
            &Op2::Product,
            &Op2::Quotient,
            &Op2::Equal,
            &Op2::NumEqual,
            &Op2::Less,
            &Op2::Greater,
            &Op2::LessEqual,
            &Op2::GreaterEqual,
            &Op2::Cons,
            &Op2::StrCons,
            &Op2::Begin,
            &Op2::Hide,
            &Op2::Modulo,
            &Op2::Eval,
        ]
    }

    fn supports_arity(&self, n: usize) -> bool {
        matches!((self, n), (Op2::Begin, _) | (Op2::Eval, 1 | 2) | (_, 2))
    }
}

impl fmt::Display for Op2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op2::Sum => write!(f, "sum#"),
            Op2::Diff => write!(f, "diff#"),
            Op2::Product => write!(f, "product#"),
            Op2::Quotient => write!(f, "quotient#"),
            Op2::Equal => write!(f, "equal#"),
            Op2::NumEqual => write!(f, "numequal#"),
            Op2::Less => write!(f, "less#"),
            Op2::Greater => write!(f, "greater"),
            Op2::LessEqual => write!(f, "lessequal#"),
            Op2::GreaterEqual => write!(f, "greaterequal#"),
            Op2::Cons => write!(f, "cons"),
            Op2::StrCons => write!(f, "strcons#"),
            Op2::Begin => write!(f, "begin"),
            Op2::Hide => write!(f, "hide"),
            Op2::Modulo => write!(f, "modulo"),
            Op2::Eval => write!(f, "eval#"),
        }
    }
}

#[cfg(test)]
pub mod tests {

    use super::*;
    use proptest::prelude::*;

    proptest! {
    #[test]
    fn prop_expr_tag_u16(x in any::<ExprTag>()) {
        let x_u16: u16 = x.into();
        let x2 = ExprTag::try_from(x_u16).expect("read ExprTag from u16");
        assert_eq!(x, x2);
    }
    }

    proptest! {
    #[test]
    fn prop_cont_tag_u16(x in any::<ContTag>()) {
        let x_u16: u16 = x.into();
        let x2 = ContTag::try_from(x_u16).expect("read ContTag from u16");
        assert_eq!(x, x2)
    }
    }

    proptest! {
    #[test]
    fn prop_op1_u16(x in any::<Op1>()) {
        let x_u16: u16 = x.into();
        let x2 = Op1::try_from(x_u16).expect("read Op1 from u16");
        assert_eq!(x, x2)
    }
    }

    proptest! {
    #[test]
    fn prop_op2_u16(x in any::<Op2>()) {
        let x_u16: u16 = x.into();
        let x2 = Op2::try_from(x_u16).expect("read Op2 from u16");
        assert_eq!(x, x2)
    }
    }
}
