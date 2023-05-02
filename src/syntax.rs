use std::fmt;

use crate::field::LurkField;
use crate::num::Num;
use crate::parser::position::Pos;
use crate::ptr::Ptr;
use crate::store::Store;
use crate::symbol::Symbol;
use crate::uint::UInt;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

// Lurk syntax
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Syntax<F: LurkField> {
    Num(Pos, Num<F>),
    // A u64 integer: 1u64, 0xffu64
    UInt(Pos, UInt),
    // A hierarchical symbol foo, foo.bar.baz or keyword :foo
    Symbol(Pos, Symbol),
    // A string literal: "foobar", "foo\nbar"
    String(Pos, String),
    // A character literal: #\A #\λ #\u03BB
    Char(Pos, char),
    // A quoted expression: 'a, '(1 2)
    Quote(Pos, Box<Syntax<F>>),
    // A nil-terminated cons-list of expressions: (1 2 3)
    List(Pos, Vec<Syntax<F>>),
    // An imprpoer cons-list of expressions: (1 2 . 3)
    Improper(Pos, Vec<Syntax<F>>, Box<Syntax<F>>),
}

#[cfg(not(target_arch = "wasm32"))]
impl<Fr: LurkField> Arbitrary for Syntax<Fr> {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        let leaf = prop_oneof![
            any::<Num<Fr>>().prop_map(|x| Syntax::Num(Pos::No, x)),
            any::<UInt>().prop_map(|x| Syntax::UInt(Pos::No, x)),
            any::<Symbol>().prop_map(|x| Syntax::Symbol(Pos::No, x)),
            any::<String>().prop_map(|x| Syntax::String(Pos::No, x)),
            any::<char>().prop_map(|x| Syntax::Char(Pos::No, x))
        ];
        leaf.prop_recursive(8, 256, 10, |inner| {
            prop_oneof![
                inner
                    .clone()
                    .prop_map(|x| Syntax::Quote(Pos::No, Box::new(x))),
                prop::collection::vec(inner.clone(), 0..10).prop_map(|x| Syntax::List(Pos::No, x)),
                prop::collection::vec(inner.clone(), 1..11).prop_map(|mut xs| {
                    let x = xs.pop().unwrap();
                    Syntax::Improper(Pos::No, xs, Box::new(x))
                })
            ]
        })
        .boxed()
    }
}

impl<F: LurkField> fmt::Display for Syntax<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Num(_, x) => write!(f, "{}", x),
            Self::UInt(_, x) => write!(f, "{}", x),
            Self::Symbol(_, sym) => write!(f, "{}", sym),
            Self::String(_, x) => write!(f, "\"{}\"", x.escape_default()),
            Self::Char(_, x) => write!(f, "#\\{}", x.escape_default()),
            Self::Quote(_, x) => write!(f, "'{}", x),
            Self::List(_, xs) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    match iter.peek() {
                        Some(_) => write!(f, "{} ", x)?,
                        None => write!(f, "{}", x)?,
                    }
                }
                write!(f, ")")
            }
            Self::Improper(_, xs, end) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    match iter.peek() {
                        Some(_) => write!(f, "{} ", x)?,
                        None => write!(f, "{} . {}", x, *end)?,
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl<F: LurkField> Store<F> {
    pub fn intern_syntax(&mut self, syn: Syntax<F>) -> Ptr<F> {
        match syn {
            Syntax::Num(_, x) => self.intern_num(x),
            Syntax::UInt(_, x) => self.intern_uint(x),
            Syntax::Char(_, x) => self.intern_char(x),
            Syntax::Symbol(_, x) => self.intern_symbol(x),
            Syntax::String(_, x) => self.intern_string(x),
            Syntax::Quote(pos, x) => {
                let xs = vec![Syntax::Symbol(pos, Symbol::lurk_sym("quote")), *x];
                self.intern_syntax(Syntax::List(pos, xs))
            }
            Syntax::List(_, xs) => {
                let mut cdr = self.nil();
                for x in xs.into_iter().rev() {
                    let car = self.intern_syntax(x);
                    cdr = self.intern_cons(car, cdr);
                }
                cdr
            }
            Syntax::Improper(_, xs, end) => {
                let mut cdr = self.intern_syntax(*end);
                for x in xs.into_iter().rev() {
                    let car = self.intern_syntax(x);
                    cdr = self.intern_cons(car, cdr);
                }
                cdr
            }
        }
    }

    pub fn fetch_syntax(&mut self, ptr: Ptr<F>) -> Option<Syntax<F>> {
        todo!()
    }
}

//#[cfg(test)]
//mod test {
//    use super::*;
//    use blstrs::Scalar as Fr;
//    use proptest::prelude::*;
//
//    //#[test]
//    //fn display_syntax() {
//    //    assert_eq!("NIL", format!("{}", Lurk::<Fr>::Nil(Pos::No)));
//    //    assert_eq!(
//    //        "(NIL)",
//    //        format!(
//    //            "{}",
//    //            Lurk::<Fr>::Cons(Pos::No, Box::new((Lurk::Nil(Pos::No), Lurk::Nil(Pos::No))))
//    //        )
//    //    );
//    //    assert_eq!(
//    //        "(#\\a . #\\b)",
//    //        format!(
//    //            "{}",
//    //            Lurk::<Fr>::Cons(Pos::No, Box::new((Lurk::Nil(Pos::No), Lurk::Nil(Pos::No))))
//    //        )
//    //    )
//    //}
//
//    //proptest! {
//    //#[test]
//    //fn prop_display_syntax(x in any::<Lurk<Fr>>()) {
//    //  println!("{}", x);
//    //  assert!(false)
//    //}
//    //}
//}
