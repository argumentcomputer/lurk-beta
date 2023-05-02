use std::fmt;

use crate::field::LurkField;
use crate::num::Num;
use crate::parser::position::Pos;
use crate::symbol::Symbol;
use crate::uint::UInt;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

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
    // A nil-terminated cons-list of expressions: (1 2 3)
    List(Pos, Vec<Syntax<F>>),
    // An imprpoer cons-list of expressions: (1 2 . 3)
    Improper(Pos, Vec<Syntax<F>>, Box<Syntax<F>>),
    // A quoted expression: 'a, '(1 2)
    Quote(Pos, Syntax<F>),
}

//impl<F: LurkField> fmt::Display for Syntax<F> {
//    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//        match self {
//            Self::Num(_, x) => write!(f, "{}", x),
//            Self::UInt(_, x) => write!(f, "{}", x),
//            //Self::Symbol(_, sym) => write!(f, "{}", sym.print_escape()),
//            Self::String(_, x) => write!(f, "\"{}\"", x.escape_default()),
//            Self::Char(_, x) => write!(f, "#\\{}", x.escape_default()),
//            _ => todo!(),
//        }
//    }
//}
//
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
