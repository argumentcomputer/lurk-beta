use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};

use crate::{
    field::LurkField,
    tag::{ContTag, ExprTag, Op1, Op2, Tag as TagTrait},
};

/// The LEM `Tag` is a wrapper around other types that are used as tags
#[derive(Copy, Debug, PartialEq, Clone, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
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
