use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use strum::EnumCount;

use crate::{
    field::LurkField,
    tag::{
        ContTag, ExprTag, Op1, Op2, Tag as TagTrait, CONT_TAG_INIT, EXPR_TAG_INIT, OP1_TAG_INIT,
        OP2_TAG_INIT,
    },
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
        let mut last = 0;
        if (last..last + ExprTag::COUNT).contains(&i) {
            let j = i + EXPR_TAG_INIT as usize - last;
            let expr_tag = (j as u16).try_into().expect("unreachable");
            return Some(Tag::Expr(expr_tag));
        }
        last += ExprTag::COUNT;
        if (last..last + ContTag::COUNT).contains(&i) {
            let j = i + CONT_TAG_INIT as usize - last;
            let cont_tag = (j as u16).try_into().expect("unreachable");
            return Some(Tag::Cont(cont_tag));
        }
        last += ContTag::COUNT;
        if (last..last + Op1::COUNT).contains(&i) {
            let j = i + OP1_TAG_INIT as usize - last;
            let op1_tag = (j as u16).try_into().expect("unreachable");
            return Some(Tag::Op1(op1_tag));
        }
        last += Op1::COUNT;
        if (last..last + Op2::COUNT).contains(&i) {
            let j = i + OP2_TAG_INIT as usize - last;
            let op2_tag = (j as u16).try_into().expect("unreachable");
            return Some(Tag::Op2(op2_tag));
        }
        None
    }

    pub fn index(&self) -> usize {
        match self {
            Self::Expr(tag) => *tag as usize - EXPR_TAG_INIT as usize,
            Self::Cont(tag) => *tag as usize - CONT_TAG_INIT as usize + ExprTag::COUNT,
            Self::Op1(tag) => {
                *tag as usize - OP1_TAG_INIT as usize + ExprTag::COUNT + ContTag::COUNT
            }
            Self::Op2(tag) => {
                *tag as usize - OP2_TAG_INIT as usize + ExprTag::COUNT + ContTag::COUNT + Op1::COUNT
            }
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
    use strum::IntoEnumIterator;

    #[test]
    fn pos_index_roundtrip() {
        for i in 0.. {
            if let Some(tag) = Tag::pos(i) {
                let j = tag.index();
                assert_eq!(i, j);
            } else {
                break;
            }
        }

        for expr_tag in ExprTag::iter() {
            let tag = Tag::Expr(expr_tag);
            let tag_2 = Tag::pos(tag.index()).unwrap();
            assert_eq!(tag, tag_2);
        }

        for cont_tag in ContTag::iter() {
            let tag = Tag::Cont(cont_tag);
            let tag_2 = Tag::pos(tag.index()).unwrap();
            assert_eq!(tag, tag_2);
        }

        for op1_tag in Op1::iter() {
            let tag = Tag::Op1(op1_tag);
            let tag_2 = Tag::pos(tag.index()).unwrap();
            assert_eq!(tag, tag_2);
        }

        for op2_tag in Op2::iter() {
            let tag = Tag::Op2(op2_tag);
            let tag_2 = Tag::pos(tag.index()).unwrap();
            assert_eq!(tag, tag_2);
        }
    }
}
