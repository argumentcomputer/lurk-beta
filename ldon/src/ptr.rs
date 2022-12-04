use std::fmt;

use lurk_ff::{
  field::LurkField,
  tag::{
    ContTag,
    ExprTag,
    Tag,
    TagKind,
  },
};

use crate::{
  expr::{
    Cont,
    Expr,
  },
  store::Entry,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ptr<F: LurkField> {
  pub tag: Tag,
  pub val: F,
}

impl<F: LurkField> Ptr<F> {
  pub fn immediate(self) -> Option<Entry<F>> {
    match self.tag.kind {
      TagKind::Expr(ExprTag::Num) => Some(Entry::Expr(Expr::Num(self.val))),
      TagKind::Expr(ExprTag::Char) => Some(Entry::Expr(Expr::Char(self.val))),
      TagKind::Expr(ExprTag::U64) => Some(Entry::Expr(Expr::U64(self.val))),
      TagKind::Expr(ExprTag::Str) if self.val == F::zero() => {
        Some(Entry::Expr(Expr::StrNil))
      },
      TagKind::Expr(ExprTag::Cons) if self.val == F::zero() => {
        Some(Entry::Expr(Expr::ConsNil))
      },
      TagKind::Expr(ExprTag::Sym) if self.val == F::zero() => {
        Some(Entry::Expr(Expr::SymNil))
      },
      TagKind::Cont(ContTag::Outermost) => Some(Entry::Cont(Cont::Outermost)),
      TagKind::Cont(ContTag::Error) => Some(Entry::Cont(Cont::Error)),
      TagKind::Cont(ContTag::Dummy) => Some(Entry::Cont(Cont::Dummy)),
      TagKind::Cont(ContTag::Terminal) => Some(Entry::Cont(Cont::Terminal)),
      _ => None,
    }
  }

  pub fn is_immediate(self) -> bool {
    self.immediate().is_some()
      || matches!(self.tag.kind, TagKind::Op1(_) | TagKind::Op2(_))
  }
}

impl<F: LurkField> PartialOrd for Ptr<F> {
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    (
      F::from_tag_unchecked(self.tag).to_repr().as_ref(),
      self.val.to_repr().as_ref(),
    )
      .partial_cmp(&(
        F::from_tag_unchecked(other.tag).to_repr().as_ref(),
        other.val.to_repr().as_ref(),
      ))
  }
}

impl<F: LurkField> Ord for Ptr<F> {
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    (
      F::from_tag_unchecked(self.tag).to_repr().as_ref(),
      self.val.to_repr().as_ref(),
    )
      .cmp(&(
        F::from_tag_unchecked(other.tag).to_repr().as_ref(),
        other.val.to_repr().as_ref(),
      ))
  }
}

impl<'a, F: LurkField> fmt::Display for Ptr<F> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ExprTag::*;
    use TagKind::*;
    match self.tag.kind {
      Expr(Cons) => write!(f, "cons#{}", self.val.hex_digits()),
      Expr(Sym) => write!(f, "sym#{}", self.val.hex_digits()),
      Expr(Fun) => write!(f, "fun#{}", self.val.hex_digits()),
      Expr(Num) => write!(f, "num#{}", self.val.hex_digits()),
      Expr(Thunk) => write!(f, "thunk#{}", self.val.hex_digits()),
      Expr(Str) => write!(f, "str#{}", self.val.hex_digits()),
      Expr(Char) => write!(f, "char#{}", self.val.hex_digits()),
      Expr(Comm) => write!(f, "comm#{}", self.val.hex_digits()),
      Expr(U64) => write!(f, "u64#{}", self.val.hex_digits()),
      Expr(Key) => write!(f, "key#{}", self.val.hex_digits()),
      Expr(Map) => write!(f, "map#{}", self.val.hex_digits()),
      Expr(Link) => write!(f, "link#{}", self.val.hex_digits()),
      // TODO, fill in cases
      Cont(_) => write!(f, "cont..#{}", self.val.hex_digits()),
      Op1(_) => write!(f, "op1..#{}", self.val.hex_digits()),
      Op2(_) => write!(f, "op2..#{}", self.val.hex_digits()),
    }
  }
}
