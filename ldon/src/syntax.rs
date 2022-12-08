use std::{
  collections::BTreeMap,
  fmt,
};

use lurk_ff::field::LurkField;

use crate::{
  hash::PoseidonCache,
  parser::position::Pos,
  store::Store,
};

// LDON syntax
#[derive(Clone, Debug)]
pub enum Syn<F: LurkField> {
  Num(Pos, F),               // 1, 0xff
  U64(Pos, u64),             // 1u64, 0xffu64
  Symbol(Pos, Vec<String>),  // _, foo, foo.bar.baz,
  Keyword(Pos, Vec<String>), // :_ :lambda, :lurk.lambda
  String(Pos, String),       // "foobar", "foo\nbar"
  Char(Pos, char),           // 'a'
  // The end term of an improper list is not allowed to be a list
  List(Pos, Vec<Syn<F>>, Option<Box<Syn<F>>>), // (1 2 3) (1, 2, 3)
  Map(Pos, Vec<(Syn<F>, Syn<F>)>),             // { foo: 1, blue: true }
  Link(Pos, Box<Syn<F>>, Vec<u64>),            // [sha256 0xff 0xff 0xff]
}

impl<F: LurkField> Syn<F> {
  // Syn's Ord impl has bad asymptotics since it generates a fresh poseidon
  // cache. In those cases, `cached_cmp` allows for cache preserving
  // comparisons
  pub fn cached_cmp(
    &self,
    other: &Self,
    cache: &PoseidonCache<F>,
  ) -> core::cmp::Ordering {
    let mut store = Store::new();
    let self_ptr = store.intern_syn(&cache, self);
    let other_ptr = store.intern_syn(&cache, other);
    self_ptr.cmp(&other_ptr)
  }

  // see https://github.com/sg16-unicode/sg16/issues/69
  pub fn whitespace() -> Vec<char> {
    vec![
      '\u{0009}', '\u{000A}', '\u{000B}', '\u{000C}', '\u{000D}', '\u{0020}',
      '\u{0085}', '\u{200E}', '\u{200F}', '\u{2028}', '\u{2029}', '\u{20A0}',
      '\u{1680}', '\u{2000}', '\u{2001}', '\u{2002}', '\u{2003}', '\u{2004}',
      '\u{2005}', '\u{2006}', '\u{2007}', '\u{2008}', '\u{2009}', '\u{200A}',
      '\u{202F}', '\u{205F}', '\u{3000}',
    ]
  }

  pub fn is_whitespace(c: char) -> bool {
    Self::whitespace().iter().any(|x| *x == c)
  }

  pub fn escape_symbol(xs: &String) -> String {
    let mut res = String::new();
    for x in xs.chars() {
      if "(){}[]=,.:".chars().any(|c| c == x) {
        res.push_str(&format!("\\{}", x));
      }
      else if Self::is_whitespace(x) {
        res.push_str(&format!("{}", x.escape_unicode()));
      }
      else {
        res.push(x)
      }
    }
    res
  }

  pub fn sym_needs_leading_dot(xs: &Vec<String>) -> bool {
    if xs.len() == 0 || xs[0] == "" || xs[0] == "_" || xs[0] == "_." {
      return true;
    };
    let c = xs[0].chars().nth(0).unwrap();
    "1234567890.:'[](){}=,\"\\".chars().any(|x| x == c)
      || char::is_whitespace(c)
      || char::is_control(c)
  }
}

impl<F: LurkField> PartialOrd for Syn<F> {
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    Some(self.cached_cmp(other, &PoseidonCache::default()))
  }
}

impl<F: LurkField> Ord for Syn<F> {
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self.cached_cmp(other, &PoseidonCache::default())
  }
}

impl<F: LurkField> fmt::Display for Syn<F> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Num(_, x) => {
        write!(f, "0x{}", x.hex_digits())?;
        Ok(())
      },
      Self::U64(_, x) => write!(f, "{}u64", x),
      Self::Symbol(_, xs) if xs.is_empty() => write!(f, "_."),
      Self::Symbol(_, xs) => {
        if !Self::sym_needs_leading_dot(&xs) {
          write!(f, "{}", Self::escape_symbol(&xs[0]))?;
          for x in xs[1..].iter() {
            write!(f, ".{}", Self::escape_symbol(x))?;
          }
        }
        else {
          for x in xs {
            write!(f, ".{}", Self::escape_symbol(x))?;
          }
        }
        Ok(())
      },
      Self::Keyword(_, xs) if xs.is_empty() => write!(f, "_:"),
      Self::Keyword(_, xs) => {
        for x in xs {
          write!(f, ":{}", Self::escape_symbol(x))?;
        }
        Ok(())
      },
      Self::String(_, x) => write!(f, "\"{}\"", x.escape_default()),
      Self::Char(_, x) => write!(f, "'{}'", x.escape_default()),
      Self::List(_, xs, None) => {
        let mut iter = xs.iter().peekable();
        write!(f, "(")?;
        while let Some(x) = iter.next() {
          if let None = iter.peek() {
            write!(f, "{}", x)?;
          }
          else {
            write!(f, "{} ", x)?;
          }
        }
        write!(f, ")")
      },
      Self::List(_, xs, Some(end)) => {
        let mut iter = xs.iter().peekable();
        write!(f, "(")?;
        while let Some(x) = iter.next() {
          if let None = iter.peek() {
            write!(f, "{}, {}", x, end)?;
          }
          else {
            write!(f, "{}, ", x)?;
          }
        }
        write!(f, ")")
      },
      Self::Map(_, xs) => {
        let mut iter = xs.iter().peekable();
        write!(f, "{{")?;
        while let Some((key, val)) = iter.next() {
          if let None = iter.peek() {
            write!(f, "{} = {}", key, val)?;
          }
          else {
            write!(f, "{} = {}, ", key, val)?;
          }
        }
        write!(f, "}}")
      },
      Self::Link(_, ctx, xs) => {
        let mut iter = xs.iter().peekable();
        write!(f, "[{} ", ctx)?;
        while let Some(x) = iter.next() {
          if let None = iter.peek() {
            write!(f, "{}", Self::U64(Pos::No, *x))?;
          }
          else {
            write!(f, "{} ", Self::U64(Pos::No, *x))?;
          }
        }
        write!(f, "]")
      },
    }
  }
}

// Redefine Equality for Syn to ignore the Pos arguments, which only matter for
// parser errors
impl<F: LurkField> PartialEq for Syn<F> {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Num(_, x), Self::Num(_, y)) => x == y,
      (Self::U64(_, x), Self::U64(_, y)) => x == y,
      (Self::Symbol(_, x), Self::Symbol(_, y)) => x == y,
      (Self::Keyword(_, x), Self::Keyword(_, y)) => x == y,
      (Self::String(_, x), Self::String(_, y)) => x == y,
      (Self::Char(_, x), Self::Char(_, y)) => x == y,
      (Self::List(_, x, x1), Self::List(_, y, y1)) => x == y && x1 == y1,
      (Self::Map(_, x), Self::Map(_, y)) => x == y,
      (Self::Link(_, x, x1), Self::Link(_, y, y1)) => x == y && x1 == y1,
      _ => false,
    }
  }
}

impl<F: LurkField> Eq for Syn<F> {}

#[cfg(feature = "test-utils")]
pub mod test_utils {
  use blstrs::Scalar as Fr;
  // use im::Vector;
  use lurk_ff::{
    field::test_utils::FWrap,
    test_utils::frequency,
  };
  use quickcheck::{
    Arbitrary,
    Gen,
  };

  use super::*;

  impl Syn<Fr> {
    fn arbitrary_syn(g: &mut Gen) -> Self {
      let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Syn<Fr>>)> = vec![
        (100, Box::new(|g| Self::Num(Pos::No, FWrap::arbitrary(g).0))),
        (100, Box::new(|g| Self::U64(Pos::No, u64::arbitrary(g)))),
        (100, Box::new(|g| Self::Char(Pos::No, char::arbitrary(g)))),
        (100, Box::new(|g| Self::String(Pos::No, Self::arbitrary_string(g)))),
        (50, Box::new(|g| Self::Symbol(Pos::No, Self::arbitrary_symbol(g)))),
        (50, Box::new(|g| Self::Keyword(Pos::No, Self::arbitrary_symbol(g)))),
        (50, Box::new(|g| Self::arbitrary_list(g))),
        (50, Box::new(|g| Self::arbitrary_map(g))),
        (50, Box::new(|g| Self::arbitrary_link(g))),
      ];
      frequency(g, input)
    }

    fn arbitrary_string(g: &mut Gen) -> String {
      let num_chars = usize::arbitrary(g) % 5;
      let mut s = String::new();
      for _ in 0..num_chars {
        let c = char::arbitrary(g);
        s.push(c);
      }
      s
    }

    fn arbitrary_limb(g: &mut Gen) -> String {
      let num_chars = usize::arbitrary(g) % 5;
      let mut s = String::new();
      for _ in 0..num_chars {
        let c = char::arbitrary(g);
        if !char::is_whitespace(c) && c != '\\' {
          s.push(c);
        }
      }
      s
    }

    fn arbitrary_symbol(g: &mut Gen) -> Vec<String> {
      let num_syms = usize::arbitrary(g) % 3;
      let mut sym = Vec::new();
      for _ in 0..num_syms {
        let s = Self::arbitrary_limb(g);
        sym.push(s);
      }
      sym
    }

    fn arbitrary_list(g: &mut Gen) -> Self {
      let num_exprs: usize = Arbitrary::arbitrary(g);
      let num_exprs = num_exprs % 4;
      let mut exprs = Vec::new();
      for _ in 0..num_exprs {
        let expr = Syn::arbitrary_syn(g);
        exprs.push(expr);
      }
      let improper: bool = Arbitrary::arbitrary(g);
      let end = exprs.pop();
      if improper && num_exprs >= 2 && !matches!(end, Some(Syn::List(_, _, _)))
      {
        Syn::List(Pos::No, exprs, end.map(Box::new))
      }
      else {
        Syn::List(Pos::No, exprs, None)
      }
    }

    fn arbitrary_map(g: &mut Gen) -> Self {
      let num_exprs: usize = Arbitrary::arbitrary(g);
      let num_exprs = num_exprs % 3;
      // we use a BTreeMap to get the right ordering
      let mut map = BTreeMap::new();
      for _ in 0..num_exprs {
        let key = Syn::arbitrary_syn(g);
        let val = Syn::arbitrary_syn(g);
        map.insert(key, val);
      }
      Syn::Map(Pos::No, map.into_iter().collect())
    }

    fn arbitrary_link(g: &mut Gen) -> Self {
      let num_xs: usize = Arbitrary::arbitrary(g);
      let num_xs = num_xs % 4;
      let mut xs = Vec::new();
      for _ in 0..num_xs {
        let x = u64::arbitrary(g);
        xs.push(x);
      }
      Syn::Link(Pos::No, Box::new(Syn::arbitrary_syn(g)), xs)
    }
  }

  impl Arbitrary for Syn<Fr> {
    fn arbitrary(g: &mut Gen) -> Self { Syn::arbitrary_syn(g) }
  }
}

#[cfg(all(test, feature = "test-utils"))]
mod test {
  use blstrs::Scalar as Fr;

  use super::*;

  //#[test]
  // fn display_link() {
  //    println!(
  //        "{}",
  //        Syn::<Fr>::Link(
  //            Pos::No,
  //            Box::new(Syn::Symbol(Pos::No,
  // vec![Sym::Sym("sha256".to_string())])),            vec![u64::MAX,
  // u64::MAX, u64::MAX, u64::MAX]        )
  //    );
  //    assert!(false)
  //}
  #[test]
  fn unit_syn_print() {
    assert_eq!(
      format!("{}", Syn::<Fr>::Symbol(Pos::No, vec![])),
      "_.".to_string()
    );
    assert_eq!(
      format!("{}", Syn::<Fr>::Keyword(Pos::No, vec![])),
      "_:".to_string()
    );
    assert_eq!(
      format!("{}", Syn::<Fr>::Symbol(Pos::No, vec!["".to_string()])),
      ".".to_string()
    );
    assert_eq!(
      format!("{}", Syn::<Fr>::Keyword(Pos::No, vec!["".to_string()])),
      ":".to_string()
    );
    assert_eq!(
      format!("{}", Syn::<Fr>::Symbol(Pos::No, vec!["foo".to_string()])),
      "foo".to_string()
    );
    assert_eq!(
      format!(
        "{}",
        Syn::<Fr>::Symbol(
          Pos::No,
          vec!["foo".to_string(), "".to_string(), "".to_string(),]
        )
      ),
      "foo..".to_string()
    );
    assert_eq!(
      format!("{}", Syn::<Fr>::Keyword(Pos::No, vec!["foo".to_string()])),
      ":foo".to_string()
    );
    assert_eq!(
      format!(
        "{}",
        Syn::<Fr>::Symbol(Pos::No, vec!["".to_string(), "foo".to_string()])
      ),
      "..foo".to_string()
    );
    assert_eq!(
      format!(
        "{}",
        Syn::<Fr>::Keyword(Pos::No, vec!["".to_string(), "foo".to_string()])
      ),
      "::foo".to_string()
    );
    assert_eq!(
      format!("{}", Syn::<Fr>::List(Pos::No, vec![], None)),
      "()".to_string()
    );
    assert_eq!(
      format!(
        "{}",
        Syn::<Fr>::List(
          Pos::No,
          vec![
            Syn::U64(Pos::No, 1),
            Syn::U64(Pos::No, 2),
            Syn::U64(Pos::No, 3),
          ],
          None
        )
      ),
      "(1u64 2u64 3u64)".to_string()
    );
    assert_eq!(
      format!(
        "{}",
        Syn::<Fr>::List(
          Pos::No,
          vec![
            Syn::U64(Pos::No, 1),
            Syn::U64(Pos::No, 2),
            Syn::U64(Pos::No, 3),
          ],
          Some(Box::new(Syn::U64(Pos::No, 4)))
        )
      ),
      "(1u64, 2u64, 3u64, 4u64)".to_string()
    );
    assert_eq!(
      format!(
        "{}",
        Syn::<Fr>::Map(
          Pos::No,
          vec![
            (Syn::Symbol(Pos::No, vec!["a".to_string()]), Syn::U64(Pos::No, 1)),
            (Syn::Symbol(Pos::No, vec!["b".to_string()]), Syn::U64(Pos::No, 2)),
            (Syn::Symbol(Pos::No, vec!["c".to_string()]), Syn::U64(Pos::No, 3)),
          ],
        )
      ),
      "{a = 1u64, b = 2u64, c = 3u64}".to_string()
    );
  }

  #[quickcheck]
  fn prop_syn_generates(syn: Syn<Fr>) -> bool {
    // println!("-------------");
    let mut store1 = Store::<Fr>::default();
    let cache = PoseidonCache::default();
    let _ptr1 = store1.intern_syn(&cache, &syn);
    true
  }
}
