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
  cont::Cont,
  expr::Expr,
  serde_f::{
    SerdeF,
    SerdeFError,
  },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ptr<F: LurkField> {
  pub tag: Tag,
  pub val: F,
}

impl<F: LurkField> Ptr<F> {
  pub fn immediate_expr(self) -> Option<Expr<F>> {
    match self.tag.kind {
      TagKind::Expr(ExprTag::Num) => Some(Expr::Num(self.val)),
      TagKind::Expr(ExprTag::Char) => Some(Expr::Char(self.val)),
      TagKind::Expr(ExprTag::U64) => Some(Expr::U64(self.val)),
      TagKind::Expr(ExprTag::Str) if self.val == F::zero() => {
        Some(Expr::StrNil)
      },
      TagKind::Expr(ExprTag::Cons) if self.val == F::zero() => {
        Some(Expr::ConsNil)
      },
      TagKind::Expr(ExprTag::Sym) if self.val == F::zero() => {
        Some(Expr::SymNil)
      },
      _ => None,
    }
  }

  pub fn immediate_cont(self) -> Option<Cont<F>> {
    match self.tag.kind {
      TagKind::Cont(ContTag::Outermost) => Some(Cont::Outermost),
      TagKind::Cont(ContTag::Error) => Some(Cont::Error),
      TagKind::Cont(ContTag::Dummy) => Some(Cont::Dummy),
      TagKind::Cont(ContTag::Terminal) => Some(Cont::Terminal),
      _ => None,
    }
  }

  pub fn is_immediate(self) -> bool {
    self.immediate_expr().is_some()
      || self.immediate_cont().is_some()
      || matches!(self.tag.kind, TagKind::Op1(_) | TagKind::Op2(_))
  }

  pub fn child_ptr_arity(self) -> usize {
    if self.immediate_expr().is_some() {
      0
    }
    else {
      match self.tag.kind {
        TagKind::Expr(ExprTag::Cons) => 2,
        TagKind::Expr(ExprTag::Sym) => 2,
        TagKind::Expr(ExprTag::Fun) => 3,
        TagKind::Expr(ExprTag::Thunk) => 2,
        TagKind::Expr(ExprTag::Str) => 2,
        TagKind::Expr(ExprTag::Comm) => 2,
        TagKind::Expr(ExprTag::Key) => 1,
        TagKind::Expr(ExprTag::Map) => 1,
        TagKind::Expr(ExprTag::Link) => 2,
        _ => 0,
      }
    }
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

impl<F: LurkField> fmt::Display for Ptr<F> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.tag.kind)?;
    write!(f, "{}", self.val.hex_digits())
  }
}

impl<F: LurkField> SerdeF<F> for Ptr<F> {
  fn ser_f(&self) -> Vec<F> { vec![F::from_tag_unchecked(self.tag), self.val] }

  fn de_f(fs: &[F]) -> Result<Ptr<F>, SerdeFError<F>> {
    match fs {
      &[tag, val, ..] => {
        let tag =
          F::to_tag(&tag).ok_or_else(|| SerdeFError::UnknownTag(tag))?;
        Ok(Ptr { tag, val })
      },
      _ => Err(SerdeFError::Expected("Ptr".to_string())),
    }
  }
}

#[cfg(feature = "test-utils")]
pub mod test_utils {
  use blstrs::Scalar as Fr;
  use lurk_ff::field::test_utils::*;
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;
  impl Arbitrary for Ptr<Fr> {
    fn arbitrary(g: &mut Gen) -> Self {
      Ptr { tag: Arbitrary::arbitrary(g), val: FWrap::arbitrary(g).0 }
    }
  }
}

#[cfg(all(test, feature = "test-utils"))]
pub mod tests {
  use blstrs::Scalar as Fr;
  use lurk_ff::test_utils::frequency;
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::{
    test_utils::*,
    *,
  };

  #[quickcheck]
  fn prop_ptr_serdef(ptr: Ptr<Fr>) -> bool {
    match Ptr::de_f(&ptr.ser_f()) {
      Ok(ptr2) => ptr == ptr2,
      Err(e) => {
        println!("{:?}", e);
        false
      },
    }
  }

  #[quickcheck]
  fn prop_ptr_serde(ptr: Ptr<Fr>) -> bool {
    match Ptr::de(&ptr.ser()) {
      Ok(ptr2) => ptr == ptr2,
      Err(e) => {
        println!("{:?}", e);
        false
      },
    }
  }
}
