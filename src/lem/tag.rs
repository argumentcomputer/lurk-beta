use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};

use crate::{
    field::LurkField,
    tag::{ContTag, ExprTag, Op1, Op2, Tag as TagTrait},
};

/// The LEM `Tag` is a wrapper around other types that are used as tags
#[derive(Copy, Debug, PartialEq, Clone, Eq, Hash, Serialize, Deserialize)]
pub enum Tag {
    Expr(ExprTag),
    Cont(ContTag),
    Op1(Op1),
    Op2(Op2),
}

impl TryFrom<u16> for Tag {
    type Error = anyhow::Error;

    fn try_from(val: u16) -> Result<Self, Self::Error> {
        if let Ok(tag) = ExprTag::try_from(val) {
            Ok(Tag::Expr(tag))
        } else if let Ok(tag) = ContTag::try_from(val) {
            Ok(Tag::Cont(tag))
        } else if let Ok(tag) = Op1::try_from(val) {
            Ok(Tag::Op1(tag))
        } else if let Ok(tag) = Op2::try_from(val) {
            Ok(Tag::Op2(tag))
        } else {
            bail!("Invalid u16 for Tag: {val}")
        }
    }
}

impl From<Tag> for u16 {
    fn from(val: Tag) -> Self {
        match val {
            Tag::Expr(tag) => tag.into(),
            Tag::Cont(tag) => tag.into(),
            Tag::Op1(tag) => tag.into(),
            Tag::Op2(tag) => tag.into(),
        }
    }
}

impl TagTrait for Tag {
    fn from_field<F: LurkField>(f: &F) -> Option<Self> {
        Self::try_from(f.to_u16()?).ok()
    }

    fn to_field<F: LurkField>(&self) -> F {
        Tag::to_field(self)
    }
}

impl Tag {
    #[inline]
    pub fn to_field<F: LurkField>(&self) -> F {
        match self {
            Self::Expr(tag) => tag.to_field(),
            Self::Cont(tag) => tag.to_field(),
            Self::Op1(tag) => tag.to_field(),
            Self::Op2(tag) => tag.to_field(),
        }
    }

    pub fn pos(i: usize) -> Option<Self> {
        match i {
            0 => Some(Self::Expr(ExprTag::Nil)),
            1 => Some(Self::Expr(ExprTag::Cons)),
            2 => Some(Self::Expr(ExprTag::Sym)),
            3 => Some(Self::Expr(ExprTag::Fun)),
            4 => Some(Self::Expr(ExprTag::Num)),
            5 => Some(Self::Expr(ExprTag::Thunk)),
            6 => Some(Self::Expr(ExprTag::Str)),
            7 => Some(Self::Expr(ExprTag::Char)),
            8 => Some(Self::Expr(ExprTag::Comm)),
            9 => Some(Self::Expr(ExprTag::U64)),
            10 => Some(Self::Expr(ExprTag::Key)),
            11 => Some(Self::Expr(ExprTag::Cproc)),
            12 => Some(Self::Cont(ContTag::Outermost)),
            13 => Some(Self::Cont(ContTag::Call0)),
            14 => Some(Self::Cont(ContTag::Call)),
            15 => Some(Self::Cont(ContTag::Call2)),
            16 => Some(Self::Cont(ContTag::Tail)),
            17 => Some(Self::Cont(ContTag::Error)),
            18 => Some(Self::Cont(ContTag::Lookup)),
            19 => Some(Self::Cont(ContTag::Unop)),
            20 => Some(Self::Cont(ContTag::Binop)),
            21 => Some(Self::Cont(ContTag::Binop2)),
            22 => Some(Self::Cont(ContTag::If)),
            23 => Some(Self::Cont(ContTag::Let)),
            24 => Some(Self::Cont(ContTag::LetRec)),
            25 => Some(Self::Cont(ContTag::Dummy)),
            26 => Some(Self::Cont(ContTag::Terminal)),
            27 => Some(Self::Cont(ContTag::Emit)),
            28 => Some(Self::Cont(ContTag::Cproc)),
            29 => Some(Self::Op1(Op1::Car)),
            30 => Some(Self::Op1(Op1::Cdr)),
            31 => Some(Self::Op1(Op1::Atom)),
            32 => Some(Self::Op1(Op1::Emit)),
            33 => Some(Self::Op1(Op1::Open)),
            34 => Some(Self::Op1(Op1::Secret)),
            35 => Some(Self::Op1(Op1::Commit)),
            36 => Some(Self::Op1(Op1::Num)),
            37 => Some(Self::Op1(Op1::Comm)),
            38 => Some(Self::Op1(Op1::Char)),
            39 => Some(Self::Op1(Op1::Eval)),
            40 => Some(Self::Op1(Op1::U64)),
            41 => Some(Self::Op2(Op2::Sum)),
            42 => Some(Self::Op2(Op2::Diff)),
            43 => Some(Self::Op2(Op2::Product)),
            44 => Some(Self::Op2(Op2::Quotient)),
            45 => Some(Self::Op2(Op2::Equal)),
            46 => Some(Self::Op2(Op2::NumEqual)),
            47 => Some(Self::Op2(Op2::Less)),
            48 => Some(Self::Op2(Op2::Greater)),
            49 => Some(Self::Op2(Op2::LessEqual)),
            50 => Some(Self::Op2(Op2::GreaterEqual)),
            51 => Some(Self::Op2(Op2::Cons)),
            52 => Some(Self::Op2(Op2::StrCons)),
            53 => Some(Self::Op2(Op2::Begin)),
            54 => Some(Self::Op2(Op2::Hide)),
            55 => Some(Self::Op2(Op2::Modulo)),
            56 => Some(Self::Op2(Op2::Eval)),
            _ => None,
        }
    }

    pub fn index(&self) -> usize {
        match self {
            Self::Expr(ExprTag::Nil) => 0,
            Self::Expr(ExprTag::Cons) => 1,
            Self::Expr(ExprTag::Sym) => 2,
            Self::Expr(ExprTag::Fun) => 3,
            Self::Expr(ExprTag::Num) => 4,
            Self::Expr(ExprTag::Thunk) => 5,
            Self::Expr(ExprTag::Str) => 6,
            Self::Expr(ExprTag::Char) => 7,
            Self::Expr(ExprTag::Comm) => 8,
            Self::Expr(ExprTag::U64) => 9,
            Self::Expr(ExprTag::Key) => 10,
            Self::Expr(ExprTag::Cproc) => 11,
            Self::Cont(ContTag::Outermost) => 12,
            Self::Cont(ContTag::Call0) => 13,
            Self::Cont(ContTag::Call) => 14,
            Self::Cont(ContTag::Call2) => 15,
            Self::Cont(ContTag::Tail) => 16,
            Self::Cont(ContTag::Error) => 17,
            Self::Cont(ContTag::Lookup) => 18,
            Self::Cont(ContTag::Unop) => 19,
            Self::Cont(ContTag::Binop) => 20,
            Self::Cont(ContTag::Binop2) => 21,
            Self::Cont(ContTag::If) => 22,
            Self::Cont(ContTag::Let) => 23,
            Self::Cont(ContTag::LetRec) => 24,
            Self::Cont(ContTag::Dummy) => 25,
            Self::Cont(ContTag::Terminal) => 26,
            Self::Cont(ContTag::Emit) => 27,
            Self::Cont(ContTag::Cproc) => 28,
            Self::Op1(Op1::Car) => 29,
            Self::Op1(Op1::Cdr) => 30,
            Self::Op1(Op1::Atom) => 31,
            Self::Op1(Op1::Emit) => 32,
            Self::Op1(Op1::Open) => 33,
            Self::Op1(Op1::Secret) => 34,
            Self::Op1(Op1::Commit) => 35,
            Self::Op1(Op1::Num) => 36,
            Self::Op1(Op1::Comm) => 37,
            Self::Op1(Op1::Char) => 38,
            Self::Op1(Op1::Eval) => 39,
            Self::Op1(Op1::U64) => 40,
            Self::Op2(Op2::Sum) => 41,
            Self::Op2(Op2::Diff) => 42,
            Self::Op2(Op2::Product) => 43,
            Self::Op2(Op2::Quotient) => 44,
            Self::Op2(Op2::Equal) => 45,
            Self::Op2(Op2::NumEqual) => 46,
            Self::Op2(Op2::Less) => 47,
            Self::Op2(Op2::Greater) => 48,
            Self::Op2(Op2::LessEqual) => 49,
            Self::Op2(Op2::GreaterEqual) => 50,
            Self::Op2(Op2::Cons) => 51,
            Self::Op2(Op2::StrCons) => 52,
            Self::Op2(Op2::Begin) => 53,
            Self::Op2(Op2::Hide) => 54,
            Self::Op2(Op2::Modulo) => 55,
            Self::Op2(Op2::Eval) => 56,
        }
    }
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Tag::{Cont, Expr, Op1, Op2};
        match self {
            Expr(tag) => write!(f, "expr.{}", tag),
            Cont(tag) => write!(f, "cont.{}", tag),
            Op1(tag) => write!(f, "op1.{}", tag),
            Op2(tag) => write!(f, "op2.{}", tag),
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::tag::{CONT_TAG_INIT, EXPR_TAG_INIT, OP1_TAG_INIT, OP2_TAG_INIT};

    #[test]
    fn pos_index_roundtrip() {
        let mut i = 0;
        while let Some(tag) = Tag::pos(i) {
            let j = tag.index();
            assert_eq!(i, j);
            i += 1;
        }

        let mut i = EXPR_TAG_INIT;
        while let Ok(expr_tag) = ExprTag::try_from(i) {
            let tag = Tag::Expr(expr_tag);
            let tag_2 = Tag::pos(tag.index()).unwrap();
            assert_eq!(tag, tag_2);
            i += 1;
        }

        let mut i = CONT_TAG_INIT;
        while let Ok(cont_tag) = ContTag::try_from(i) {
            let tag = Tag::Cont(cont_tag);
            let tag_2 = Tag::pos(tag.index()).unwrap();
            assert_eq!(tag, tag_2);
            i += 1;
        }

        let mut i = OP1_TAG_INIT;
        while let Ok(op1_tag) = Op1::try_from(i) {
            let tag = Tag::Op1(op1_tag);
            let tag_2 = Tag::pos(tag.index()).unwrap();
            assert_eq!(tag, tag_2);
            i += 1;
        }

        let mut i = OP2_TAG_INIT;
        while let Ok(op2_tag) = Op2::try_from(i) {
            let tag = Tag::Op2(op2_tag);
            let tag_2 = Tag::pos(tag.index()).unwrap();
            assert_eq!(tag, tag_2);
            i += 1;
        }
    }
}
