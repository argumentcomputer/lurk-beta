use std::fmt;

use lurk_ff::{
  field::LurkField,
  tag::{
    ContTag,
    Op1,
    Op2,
    TagKind,
  },
};

use crate::{
  hash::PoseidonCache,
  ptr::Ptr,
  serde_f::{
    SerdeF,
    SerdeFError,
  },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cont<F: LurkField> {
  Outermost,
  Call(Ptr<F>, Ptr<F>, Ptr<F>),  // arg, env, cont
  Call0(Ptr<F>, Ptr<F>),         // env, cont
  Call2(Ptr<F>, Ptr<F>, Ptr<F>), // fun, env, cont
  Tail(Ptr<F>, Ptr<F>),          // env, cont
  Error,
  Lookup(Ptr<F>, Ptr<F>),                 // env, cont
  Unop(Ptr<F>, Ptr<F>),                   // op, cont
  Binop(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>),  // op, env, args, cont
  Binop2(Ptr<F>, Ptr<F>, Ptr<F>),         // op, arg, cont
  If(Ptr<F>, Ptr<F>),                     // args, cont
  Let(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>),    // var, body, env, cont
  LetRec(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>), // var, body, env, cont
  Emit(Ptr<F>),                           // cont
  Dummy,
  Terminal,
}

impl<F: LurkField> Cont<F> {
  pub fn child_ptrs(&self) -> Vec<Ptr<F>> {
    match self {
      Cont::Call(arg, env, cont) => vec![*arg, *env, *cont],
      Cont::Call0(env, cont) => vec![*env, *cont],
      Cont::Call2(fun, env, cont) => vec![*fun, *env, *cont],
      Cont::Tail(env, cont) => vec![*env, *cont],
      Cont::Lookup(env, cont) => vec![*env, *cont],
      Cont::Unop(op1, cont) => vec![*op1, *cont],
      Cont::Binop(op2, env, args, cont) => vec![*op2, *env, *args, *cont],
      Cont::Binop2(op2, arg, cont) => vec![*op2, *arg, *cont],
      Cont::If(args, cont) => vec![*args, *cont],
      Cont::Let(var, body, env, cont) => vec![*var, *body, *env, *cont],
      Cont::LetRec(var, body, env, cont) => vec![*var, *body, *env, *cont],
      Cont::Emit(cont) => vec![*cont],
      _ => vec![],
    }
  }

  // TODO: Investigate why `hash_cont` in lurk-rs::store uses hash8 for every
  // continuation, as opposed to the expression hashing which uses hash arity
  // corresponding the expression contents. This implementation follows the
  // latter model, but could be easily adapted to the former if necessary
  pub fn ptr(&self, cache: &PoseidonCache<F>) -> Ptr<F> {
    match self {
      Cont::Outermost => {
        Ptr { tag: F::make_cont_tag(ContTag::Outermost), val: F::zero() }
      },
      Cont::Call(arg, env, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Call),
        val: cache.hash6(&[
          F::from_tag_unchecked(arg.tag),
          arg.val,
          F::from_tag_unchecked(env.tag),
          env.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Call0(env, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Call0),
        val: cache.hash4(&[
          F::from_tag_unchecked(env.tag),
          env.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Call2(fun, env, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Call2),
        val: cache.hash6(&[
          F::from_tag_unchecked(fun.tag),
          fun.val,
          F::from_tag_unchecked(env.tag),
          env.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Tail(env, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Tail),
        val: cache.hash4(&[
          F::from_tag_unchecked(env.tag),
          env.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Error => {
        Ptr { tag: F::make_cont_tag(ContTag::Error), val: F::zero() }
      },
      Cont::Lookup(env, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Lookup),
        val: cache.hash4(&[
          F::from_tag_unchecked(env.tag),
          env.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Unop(op1, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Unop),
        val: cache.hash4(&[
          F::from_tag_unchecked(op1.tag),
          op1.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Binop(op2, env, args, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Binop),
        val: cache.hash8(&[
          F::from_tag_unchecked(op2.tag),
          op2.val,
          F::from_tag_unchecked(env.tag),
          env.val,
          F::from_tag_unchecked(args.tag),
          args.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Binop2(op2, arg, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Binop2),
        val: cache.hash6(&[
          F::from_tag_unchecked(op2.tag),
          op2.val,
          F::from_tag_unchecked(arg.tag),
          arg.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::If(args, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::If),
        val: cache.hash4(&[
          F::from_tag_unchecked(args.tag),
          args.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Let(var, body, env, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Let),
        val: cache.hash8(&[
          F::from_tag_unchecked(var.tag),
          var.val,
          F::from_tag_unchecked(body.tag),
          body.val,
          F::from_tag_unchecked(env.tag),
          env.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::LetRec(var, body, env, cont) => Ptr {
        tag: F::make_cont_tag(ContTag::LetRec),
        val: cache.hash8(&[
          F::from_tag_unchecked(var.tag),
          var.val,
          F::from_tag_unchecked(body.tag),
          body.val,
          F::from_tag_unchecked(env.tag),
          env.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Cont::Emit(cont) => Ptr {
        tag: F::make_cont_tag(ContTag::Emit),
        val: cache.hash4(&[
          F::from_tag_unchecked(cont.tag),
          cont.val,
          F::zero(),
          F::zero(),
        ]),
      },
      Cont::Dummy => {
        Ptr { tag: F::make_cont_tag(ContTag::Dummy), val: F::zero() }
      },
      Cont::Terminal => {
        Ptr { tag: F::make_cont_tag(ContTag::Terminal), val: F::zero() }
      },
    }
  }
}

impl<F: LurkField> SerdeF<F> for Cont<F> {
  fn ser_f(&self) -> Vec<F> {
    let mut res = self.ptr(&PoseidonCache::default()).ser_f();
    for ptr in self.child_ptrs() {
      res.append(&mut ptr.ser_f());
    }
    res
  }

  fn de_f(fs: &[F]) -> Result<Cont<F>, SerdeFError<F>> {
    let ptr = Ptr::de_f(&fs[0..])?;
    if fs.len() < ptr.child_ptr_arity() * 2 {
      return Err(SerdeFError::UnexpectedEnd);
    }
    if let Some(cont) = ptr.immediate_cont() {
      Ok(cont)
    }
    else {
      match ptr.tag.kind {
        TagKind::Cont(ContTag::Call) => {
          let arg = Ptr::de_f(&fs[2..])?;
          let env = Ptr::de_f(&fs[4..])?;
          let cont = Ptr::de_f(&fs[6..])?;
          Ok(Cont::Call(arg, env, cont))
        },
        TagKind::Cont(ContTag::Call0) => {
          let env = Ptr::de_f(&fs[2..])?;
          let cont = Ptr::de_f(&fs[4..])?;
          Ok(Cont::Call0(env, cont))
        },
        TagKind::Cont(ContTag::Call2) => {
          let fun = Ptr::de_f(&fs[2..])?;
          let env = Ptr::de_f(&fs[4..])?;
          let cont = Ptr::de_f(&fs[6..])?;
          Ok(Cont::Call2(fun, env, cont))
        },
        TagKind::Cont(ContTag::Tail) => {
          let env = Ptr::de_f(&fs[2..])?;
          let cont = Ptr::de_f(&fs[4..])?;
          Ok(Cont::Tail(env, cont))
        },
        TagKind::Cont(ContTag::Lookup) => {
          let env = Ptr::de_f(&fs[2..])?;
          let cont = Ptr::de_f(&fs[4..])?;
          Ok(Cont::Lookup(env, cont))
        },
        TagKind::Cont(ContTag::Unop) => {
          let op1 = Ptr::de_f(&fs[2..])?;
          let cont = Ptr::de_f(&fs[4..])?;
          Ok(Cont::Unop(op1, cont))
        },
        TagKind::Cont(ContTag::Binop) => {
          let op2 = Ptr::de_f(&fs[2..])?;
          let env = Ptr::de_f(&fs[4..])?;
          let args = Ptr::de_f(&fs[6..])?;
          let cont = Ptr::de_f(&fs[8..])?;
          Ok(Cont::Binop(op2, env, args, cont))
        },
        TagKind::Cont(ContTag::Binop2) => {
          let op2 = Ptr::de_f(&fs[2..])?;
          let arg = Ptr::de_f(&fs[4..])?;
          let cont = Ptr::de_f(&fs[6..])?;
          Ok(Cont::Binop2(op2, arg, cont))
        },
        TagKind::Cont(ContTag::If) => {
          let args = Ptr::de_f(&fs[2..])?;
          let cont = Ptr::de_f(&fs[4..])?;
          Ok(Cont::If(args, cont))
        },
        TagKind::Cont(ContTag::Let) => {
          let var = Ptr::de_f(&fs[2..])?;
          let body = Ptr::de_f(&fs[4..])?;
          let env = Ptr::de_f(&fs[6..])?;
          let cont = Ptr::de_f(&fs[8..])?;
          Ok(Cont::Let(var, body, env, cont))
        },
        TagKind::Cont(ContTag::LetRec) => {
          let var = Ptr::de_f(&fs[2..])?;
          let body = Ptr::de_f(&fs[4..])?;
          let env = Ptr::de_f(&fs[6..])?;
          let cont = Ptr::de_f(&fs[8..])?;
          Ok(Cont::LetRec(var, body, env, cont))
        },
        TagKind::Cont(ContTag::Emit) => {
          let cont = Ptr::de_f(&fs[2..])?;
          Ok(Cont::Emit(cont))
        },
        TagKind::Cont(x) => {
          Err(SerdeFError::Custom(format!("Unknown ContTag {:?}", x)))
        },
        _ => Err(SerdeFError::Expected("Cont".to_string())),
      }
    }
  }
}

impl<F: LurkField> fmt::Display for Cont<F> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let ptr = self.ptr(&PoseidonCache::default());
    let child_ptrs = self.child_ptrs();
    write!(f, "{}", ptr.tag.kind)?;
    write!(f, "(")?;
    for child in child_ptrs {
      write!(f, " {},", child)?;
    }
    write!(f, ")")
  }
}

#[cfg(feature = "test-utils")]
pub mod test_utils {
  use blstrs::Scalar as Fr;
  use ff::Field;
  use lurk_ff::{
    field::LurkField,
    test_utils::frequency,
  };
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;

  // These continuationsare not necessarily well-formed
  impl Arbitrary for Cont<Fr> {
    fn arbitrary(g: &mut Gen) -> Self {
      #[allow(clippy::type_complexity)]
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
        (
          100,
          Box::new(|g| {
            Self::Unop(
              Ptr { tag: Fr::make_op1_tag(Op1::arbitrary(g)), val: Fr::zero() },
              Ptr::arbitrary(g),
            )
          }),
        ),
        (
          100,
          Box::new(|g| {
            Self::Binop(
              Ptr { tag: Fr::make_op2_tag(Op2::arbitrary(g)), val: Fr::zero() },
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
              Ptr { tag: Fr::make_op2_tag(Op2::arbitrary(g)), val: Fr::zero() },
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

#[cfg(all(test, feature = "test-utils"))]
pub mod tests {
  use blstrs::Scalar as Fr;

  use super::*;

  #[quickcheck]
  fn prop_cont_serdef(cont1: Cont<Fr>) -> bool {
    println!("===============================");
    let vec = &cont1.ser_f();
    println!("{:?}", vec);
    match Cont::de_f(&vec) {
      Ok(cont2) => {
        println!("cont1: {}", cont1);
        println!("cont2: {}", cont2);
        cont1 == cont2
      },
      Err(e) => {
        println!("{:?}", e);
        false
      },
    }
  }

  #[quickcheck]
  fn prop_cont_serde(cont1: Cont<Fr>) -> bool {
    println!("===============================");
    let vec = &cont1.ser();
    println!("{:?}", vec);
    match Cont::de(&vec) {
      Ok(cont2) => {
        println!("cont1: {}", cont1);
        println!("cont2: {}", cont2);
        cont1 == cont2
      },
      Err(e) => {
        println!("{:?}", e);
        false
      },
    }
  }
}
