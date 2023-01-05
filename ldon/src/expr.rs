use std::fmt;

use lurk_ff::{
  field::LurkField,
  tag::{
    ExprTag,
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

// user-level expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<F: LurkField> {
  ConsNil,
  Cons(Ptr<F>, Ptr<F>),        // car, cdr
  Comm(Ptr<F>, Ptr<F>),        // secret, val
  SymNil,                      //
  SymCons(Ptr<F>, Ptr<F>),     // head, tail
  Keyword(Ptr<F>),             // symbol
  StrNil,                      //
  StrCons(Ptr<F>, Ptr<F>),     // head, tail
  Thunk(Ptr<F>, Ptr<F>),       // val, cont
  Fun(Ptr<F>, Ptr<F>, Ptr<F>), // arg, body, env
  Num(F),                      //
  Char(F),                     //
  U64(F),                      //
  Map(Ptr<F>),                 // symbol
  Link(Ptr<F>, Ptr<F>),        // ctx, data
}

impl<F: LurkField> Expr<F> {
  /// All the `Ptr`s directly reachable from `expr`, if any.
  pub fn child_ptrs(&self) -> Vec<Ptr<F>> {
    match self {
      Expr::ConsNil => vec![],
      Expr::Cons(car, cdr) => vec![*car, *cdr],
      Expr::Comm(secret, payload) => vec![*secret, *payload],
      Expr::SymNil => vec![],
      Expr::SymCons(head, tail) => vec![*head, *tail],
      Expr::Keyword(symbol) => vec![*symbol],
      Expr::Fun(arg, body, closed_env) => vec![*arg, *body, *closed_env],
      Expr::Num(_) => vec![],
      Expr::StrNil => vec![],
      Expr::StrCons(head, tail) => vec![*head, *tail],
      Expr::Thunk(val, cont) => vec![*val, *cont],
      Expr::Char(_) => vec![],
      Expr::U64(_) => vec![],
      Expr::Map(map) => vec![*map],
      Expr::Link(ctx, data) => vec![*ctx, *data],
    }
  }

  pub fn ptr(&self, cache: &PoseidonCache<F>) -> Ptr<F> {
    match self {
      Expr::ConsNil => {
        Ptr { tag: F::make_expr_tag(ExprTag::Cons), val: F::zero() }
      },
      Expr::Cons(car, cdr) => Ptr {
        tag: F::make_expr_tag(ExprTag::Cons),
        val: cache.hash4(&[
          F::from_tag_unchecked(car.tag),
          car.val,
          F::from_tag_unchecked(cdr.tag),
          cdr.val,
        ]),
      },
      Expr::Comm(secret, val) => Ptr {
        tag: F::make_expr_tag(ExprTag::Comm),
        val: cache.hash4(&[
          F::from_tag_unchecked(secret.tag),
          secret.val,
          F::from_tag_unchecked(val.tag),
          val.val,
        ]),
      },
      Expr::SymNil => {
        Ptr { tag: F::make_expr_tag(ExprTag::Sym), val: F::zero() }
      },
      Expr::SymCons(head, tail) => Ptr {
        tag: F::make_expr_tag(ExprTag::Sym),
        val: cache.hash4(&[
          F::from_tag_unchecked(head.tag),
          head.val,
          F::from_tag_unchecked(tail.tag),
          tail.val,
        ]),
      },
      Expr::Keyword(symbol) => {
        Ptr { tag: F::make_expr_tag(ExprTag::Key), val: symbol.val }
      },
      Expr::Fun(arg, body, env) => Ptr {
        tag: F::make_expr_tag(ExprTag::Fun),
        val: cache.hash6(&[
          F::from_tag_unchecked(arg.tag),
          arg.val,
          F::from_tag_unchecked(body.tag),
          body.val,
          F::from_tag_unchecked(env.tag),
          env.val,
        ]),
      },
      Expr::Num(f) => Ptr { tag: F::make_expr_tag(ExprTag::Num), val: *f },
      Expr::StrNil => {
        Ptr { tag: F::make_expr_tag(ExprTag::Str), val: F::zero() }
      },
      Expr::StrCons(head, tail) => Ptr {
        tag: F::make_expr_tag(ExprTag::Str),
        val: cache.hash4(&[
          F::from_tag_unchecked(head.tag),
          head.val,
          F::from_tag_unchecked(tail.tag),
          tail.val,
        ]),
      },
      Expr::Char(f) => Ptr { tag: F::make_expr_tag(ExprTag::Char), val: *f },
      Expr::U64(f) => Ptr { tag: F::make_expr_tag(ExprTag::U64), val: *f },
      Expr::Thunk(val, cont) => Ptr {
        tag: F::make_expr_tag(ExprTag::Thunk),
        val: cache.hash4(&[
          F::from_tag_unchecked(val.tag),
          val.val,
          F::from_tag_unchecked(cont.tag),
          cont.val,
        ]),
      },
      Expr::Map(map) => {
        Ptr { tag: F::make_expr_tag(ExprTag::Map), val: map.val }
      },
      Expr::Link(ctx, data) => Ptr {
        tag: F::make_expr_tag(ExprTag::Link),
        val: cache.hash4(&[
          F::from_tag_unchecked(ctx.tag),
          ctx.val,
          F::from_tag_unchecked(data.tag),
          data.val,
        ]),
      },
    }
  }
}

impl<F: LurkField> SerdeF<F> for Expr<F> {
  fn ser_f(&self) -> Vec<F> {
    let mut res = self.ptr(&PoseidonCache::default()).ser_f();
    for ptr in self.child_ptrs() {
      res.append(&mut ptr.ser_f());
    }
    res
  }

  fn de_f(fs: &[F]) -> Result<Expr<F>, SerdeFError<F>> {
    let ptr = Ptr::de_f(&fs[0..])?;
    if fs.len() < ptr.child_ptr_arity() * 2 {
      return Err(SerdeFError::UnexpectedEnd);
    }
    if let Some(expr) = ptr.immediate_expr() {
      Ok(expr)
    }
    else {
      match ptr.tag.kind {
        TagKind::Expr(ExprTag::Fun) => {
          let arg = Ptr::de_f(&fs[2..])?;
          let bod = Ptr::de_f(&fs[4..])?;
          let env = Ptr::de_f(&fs[6..])?;
          Ok(Expr::Fun(arg, bod, env))
        },
        TagKind::Expr(ExprTag::Cons) => {
          let car = Ptr::de_f(&fs[2..])?;
          let cdr = Ptr::de_f(&fs[4..])?;
          Ok(Expr::Cons(car, cdr))
        },
        TagKind::Expr(ExprTag::Str) => {
          let car = Ptr::de_f(&fs[2..])?;
          let cdr = Ptr::de_f(&fs[4..])?;
          Ok(Expr::StrCons(car, cdr))
        },
        TagKind::Expr(ExprTag::Sym) => {
          let car = Ptr::de_f(&fs[2..])?;
          let cdr = Ptr::de_f(&fs[4..])?;
          Ok(Expr::SymCons(car, cdr))
        },
        TagKind::Expr(ExprTag::Comm) => {
          let sec = Ptr::de_f(&fs[2..])?;
          let val = Ptr::de_f(&fs[4..])?;
          Ok(Expr::Comm(sec, val))
        },
        TagKind::Expr(ExprTag::Link) => {
          let ctx = Ptr::de_f(&fs[2..])?;
          let val = Ptr::de_f(&fs[4..])?;
          Ok(Expr::Link(ctx, val))
        },
        TagKind::Expr(ExprTag::Thunk) => {
          let val = Ptr::de_f(&fs[2..])?;
          let cont = Ptr::de_f(&fs[4..])?;
          Ok(Expr::Thunk(val, cont))
        },
        TagKind::Expr(ExprTag::Map) => {
          let map = Ptr::de_f(&fs[2..])?;
          Ok(Expr::Map(map))
        },
        TagKind::Expr(ExprTag::Key) => {
          let sym = Ptr::de_f(&fs[2..])?;
          Ok(Expr::Keyword(sym))
        },
        TagKind::Expr(x) => {
          Err(SerdeFError::Custom(format!("Unknown ExprTag {:?}", x)))
        },
        _ => Err(SerdeFError::Expected("Expr".to_string())),
      }
    }
  }
}

impl<F: LurkField> fmt::Display for Expr<F> {
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
  use lurk_ff::{
    field::test_utils::*,
    test_utils::frequency,
  };
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;

  // These expressions are not necessarily well-formed
  impl Arbitrary for Expr<Fr> {
    fn arbitrary(g: &mut Gen) -> Self {
      #[allow(clippy::type_complexity)]
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Expr<Fr>>)> = vec![
        (100, Box::new(|_| Self::ConsNil)),
        (100, Box::new(|g| Self::Cons(Ptr::arbitrary(g), Ptr::arbitrary(g)))),
        (100, Box::new(|g| Self::Comm(Ptr::arbitrary(g), Ptr::arbitrary(g)))),
        (100, Box::new(|_| Self::StrNil)),
        (
          100,
          Box::new(|g| Self::StrCons(Ptr::arbitrary(g), Ptr::arbitrary(g))),
        ),
        (100, Box::new(|_| Self::SymNil)),
        (
          100,
          Box::new(|g| Self::SymCons(Ptr::arbitrary(g), Ptr::arbitrary(g))),
        ),
        (100, Box::new(|g| Self::Keyword(Ptr::arbitrary(g)))),
        (100, Box::new(|g| Self::Num(FWrap::arbitrary(g).0))),
        (100, Box::new(|g| Self::Char(FWrap::arbitrary(g).0))),
        (100, Box::new(|g| Self::U64(FWrap::arbitrary(g).0))),
        (
          100,
          Box::new(|g| {
            Self::Fun(Ptr::arbitrary(g), Ptr::arbitrary(g), Ptr::arbitrary(g))
          }),
        ),
        (100, Box::new(|g| Self::Thunk(Ptr::arbitrary(g), Ptr::arbitrary(g)))),
        (100, Box::new(|g| Self::Map(Ptr::arbitrary(g)))),
        (100, Box::new(|g| Self::Link(Ptr::arbitrary(g), Ptr::arbitrary(g)))),
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
  fn prop_expr_serdef(expr1: Expr<Fr>) -> bool {
    println!("===============================");
    let vec = &expr1.ser_f();
    println!("{:?}", vec);
    match Expr::de_f(&vec) {
      Ok(expr2) => {
        println!("expr1: {}", expr1);
        println!("expr2: {}", expr2);
        expr1 == expr2
      },
      Err(e) => {
        println!("{:?}", e);
        false
      },
    }
  }

  #[quickcheck]
  fn prop_expr_serde(expr1: Expr<Fr>) -> bool {
    println!("===============================");
    let vec = &expr1.ser();
    println!("{:?}", vec);
    match Expr::de(&vec) {
      Ok(expr2) => {
        println!("expr1: {}", expr1);
        println!("expr2: {}", expr2);
        expr1 == expr2
      },
      Err(e) => {
        println!("{:?}", e);
        false
      },
    }
  }
}
