use std::fmt;

use crate::field::LurkField;
use crate::num::Num;
use crate::package::SymbolRef;
use crate::parser::position::Pos;
use crate::uint::UInt;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

/// Lurk's syntax for parsing
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Syntax<F: LurkField> {
    /// An element of the finite field `F`
    Num(Pos, Num<F>),
    /// A u64 integer: 1u64, 0xffu64
    UInt(Pos, UInt),
    /// A hierarchical symbol: foo, foo.bar.baz or keyword :foo
    Symbol(Pos, SymbolRef),
    /// A string literal: "foobar", "foo\nbar"
    String(Pos, String),
    /// A character literal: 'A', 'λ'
    Char(Pos, char),
    /// A quoted expression: 'a, '(1 2)
    Quote(Pos, Box<Syntax<F>>),
    /// A nil-terminated cons-list of expressions: (1 2 3)
    List(Pos, Vec<Syntax<F>>),
    /// An improper cons-list of expressions: (1 2 . 3)
    Improper(Pos, Vec<Syntax<F>>, Box<Syntax<F>>),
}

impl<F: LurkField> Syntax<F> {
    /// Retrieves the `Pos` attribute
    pub fn get_pos(&self) -> &Pos {
        match self {
            Self::Num(pos, _)
            | Self::UInt(pos, _)
            | Self::Symbol(pos, _)
            | Self::String(pos, _)
            | Self::Char(pos, _)
            | Self::Quote(pos, _)
            | Self::List(pos, _)
            | Self::Improper(pos, ..) => pos,
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
impl<Fr: LurkField> Arbitrary for Syntax<Fr> {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        use crate::Symbol;
        let leaf = prop_oneof![
            any::<Num<Fr>>().prop_map(|x| Syntax::Num(Pos::No, x)),
            any::<UInt>().prop_map(|x| Syntax::UInt(Pos::No, x)),
            any::<Symbol>().prop_map(|x| Syntax::Symbol(Pos::No, x.into())),
            any::<String>().prop_map(|x| Syntax::String(Pos::No, x)),
            any::<char>().prop_map(|x| Syntax::Char(Pos::No, x))
        ];
        leaf.prop_recursive(8, 256, 10, |inner| {
            prop_oneof![
                inner
                    .clone()
                    .prop_map(|x| Syntax::Quote(Pos::No, Box::new(x))),
                prop::collection::vec(inner.clone(), 0..10).prop_map(|x| Syntax::List(Pos::No, x)),
                prop::collection::vec(inner, 2..12).prop_map(|mut xs| {
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
            Self::Num(_, x) => write!(f, "{x}"),
            Self::UInt(_, x) => write!(f, "{x}u64"),
            Self::Symbol(_, x) => write!(f, "{x}"),
            Self::String(_, x) => write!(f, "\"{}\"", x.escape_default()),
            Self::Char(_, x) => {
                if *x == '(' || *x == ')' {
                    write!(f, "'\\{x}'")
                } else {
                    write!(f, "'{}'", x.escape_default())
                }
            }
            Self::Quote(_, x) => write!(f, "'{x}"),
            Self::List(_, xs) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    match iter.peek() {
                        Some(_) => write!(f, "{x} ")?,
                        None => write!(f, "{x}")?,
                    }
                }
                write!(f, ")")
            }
            Self::Improper(_, xs, end) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    match iter.peek() {
                        Some(_) => write!(f, "{x} ")?,
                        None => write!(f, "{} . {}", x, *end)?,
                    }
                }
                write!(f, ")")
            }
        }
    }
}
