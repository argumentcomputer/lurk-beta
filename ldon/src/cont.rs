use lurk_ff::{
  field::LurkField,
  tag::{
    Op1,
    Op2,
  },
};

use crate::ptr::Ptr;
// use crate::{
//  hash::PoseidonCache,
//  ptr::Ptr,
//  serde_f::{
//    SerdeF,
//    SerdeFError,
//  },
//};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cont<F: LurkField> {
  Outermost,
  Call(Ptr<F>, Ptr<F>, Ptr<F>),  // arg, env, cont
  Call0(Ptr<F>, Ptr<F>),         // env, cont
  Call2(Ptr<F>, Ptr<F>, Ptr<F>), // fun, env, cont
  Tail(Ptr<F>, Ptr<F>),          // env, cont
  Error,
  Lookup(Ptr<F>, Ptr<F>),                 // env, cont
  Unop(Op1, Ptr<F>),                      // op, cont
  Binop(Op2, Ptr<F>, Ptr<F>, Ptr<F>),     // op, env, args cont
  Binop2(Op2, Ptr<F>, Ptr<F>),            // op, arg, cont
  If(Ptr<F>, Ptr<F>),                     // args, cont
  Let(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>),    // var, body, env, cont
  LetRec(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>), // var, body, env, cont
  Emit(Ptr<F>),                           // cont
  Dummy,
  Terminal,
}

#[cfg(feature = "test-utils")]
pub mod test_utils {
  use blstrs::Scalar as Fr;
  use lurk_ff::test_utils::frequency;
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;

  // These continuationsare not necessarily well-formed
  impl Arbitrary for Cont<Fr> {
    fn arbitrary(g: &mut Gen) -> Self {
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Cont<Fr>>)> = vec![
        (100, Box::new(|_| Self::Outermost)),
        (
          100,
          Box::new(|g| {
            Self::Call(Ptr::arbitrary(g), Ptr::arbitrary(g), Ptr::arbitrary(g))
          }),
        ),
        (
          100,
          Box::new(|g| {
            Self::Call2(Ptr::arbitrary(g), Ptr::arbitrary(g), Ptr::arbitrary(g))
          }),
        ),
        (100, Box::new(|g| Self::Tail(Ptr::arbitrary(g), Ptr::arbitrary(g)))),
        (100, Box::new(|_| Self::Error)),
        (100, Box::new(|g| Self::Lookup(Ptr::arbitrary(g), Ptr::arbitrary(g)))),
        (100, Box::new(|g| Self::Unop(Op1::arbitrary(g), Ptr::arbitrary(g)))),
        (
          100,
          Box::new(|g| {
            Self::Binop(
              Op2::arbitrary(g),
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
            )
          }),
        ),
        (
          100,
          Box::new(|g| {
            Self::Binop2(
              Op2::arbitrary(g),
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
            )
          }),
        ),
        (100, Box::new(|g| Self::If(Ptr::arbitrary(g), Ptr::arbitrary(g)))),
        (
          100,
          Box::new(|g| {
            Self::Let(
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
            )
          }),
        ),
        (
          100,
          Box::new(|g| {
            Self::LetRec(
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
              Ptr::arbitrary(g),
            )
          }),
        ),
        (100, Box::new(|_| Self::Dummy)),
        (100, Box::new(|_| Self::Terminal)),
      ];
      frequency(g, input)
    }
  }
}
