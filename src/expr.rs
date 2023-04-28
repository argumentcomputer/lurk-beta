use std::hash::Hash;

use crate::field::LurkField;
use crate::ptr::{ContPtr, Ptr};
use crate::sym::Sym;
use crate::{Num, UInt};

// Expressions, Continuations, Op1, Op2 occupy the same namespace in
// their encoding.
// As a 16bit integer their representation is as follows
//    [typ] [value       ]
// 0b 0000_ 0000_0000_0000
//
// where typ is
// - `0b0000` for ExprTag
// - `0b0001` for ContTag
// - `0b0010` for Op1
// - `0b0011` for Op2

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression<F: LurkField> {
    Nil,
    Cons(Ptr<F>, Ptr<F>),
    Comm(F, Ptr<F>),
    /// arg, body, closed env
    Fun(Ptr<F>, Ptr<F>, Ptr<F>),
    Num(Num<F>),
    StrNil,
    StrCons(Ptr<F>, Ptr<F>),
    Thunk(Thunk<F>),
    SymNil,
    SymCons(Ptr<F>, Ptr<F>),
    Key(Ptr<F>),
    Char(char),
    UInt(UInt),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Thunk<F: LurkField> {
    pub value: Ptr<F>,
    pub continuation: ContPtr<F>,
}

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField> Hash for Thunk<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
        self.continuation.hash(state);
    }
}
