use std::fmt;

use crate::expr::Expression;
use crate::field::LurkField;
use crate::num::Num;
use crate::parser::position::Pos;
use crate::ptr::Ptr;
use crate::store::Store;
use crate::symbol::{LurkSym, Symbol};
use crate::uint::UInt;
use std::collections::HashMap;

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
    // A hierarchical symbol foo, foo.bar.baz or keyword :foo
    LurkSym(Pos, LurkSym),
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

impl<F: LurkField> Syntax<F> {
    pub fn nil(pos: Pos) -> Syntax<F> {
        Syntax::LurkSym(Pos::No, LurkSym::Nil)
    }
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
            any::<LurkSym>().prop_map(|x| Syntax::LurkSym(Pos::No, x)),
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
            Self::LurkSym(_, sym) => write!(f, "{}", sym),
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
            Syntax::LurkSym(_, x) => self.intern_symbol(Symbol::lurk_sym(&format!("{x}"))),
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

    fn fetch_syntax_list(&self, mut ptr: Ptr<F>) -> Option<Syntax<F>> {
        let mut list = vec![];
        loop {
            match self.fetch(&ptr)? {
                Expression::Cons(car, cdr) => {
                    list.push(self.fetch_syntax(car)?);
                    ptr = cdr;
                }
                Expression::Nil => {
                    if list.is_empty() {
                        return Some(Syntax::LurkSym(Pos::No, LurkSym::Nil))
                    }
                    else if list.len() == 2 {
                        if let Syntax::LurkSym(_, LurkSym::Quote) = list[0] {
                            return Some(Syntax::Quote(Pos::No, Box::new(list[1].clone())))
                        }
                        return Some(Syntax::List(Pos::No, list))
                    }
                    else {
                        return Some(Syntax::List(Pos::No, list))
                    }
                }
                _ => {
                    if list.is_empty() {
                        return None
                    }
                    else {
                        let end = Box::new(self.fetch_syntax(ptr)?);
                        return Some(Syntax::Improper(Pos::No, list, end))
                    }
                }
            }
        }
    }

    fn fetch_syntax_aux(&self, lurk_syms: HashMap<Symbol, LurkSym>, ptr: Ptr<F>) -> Option<Syntax<F>> {
        let expr = self.fetch(&ptr)?;
        match expr {
            Expression::Num(f) => Some(Syntax::Num(Pos::No, f)),
            Expression::Char(_) => Some(Syntax::Char(Pos::No, self.fetch_char(&ptr)?)),
            Expression::UInt(_) => Some(Syntax::UInt(Pos::No, self.fetch_uint(&ptr)?)),
            Expression::Nil |
            Expression::Cons(..) => self.fetch_syntax_list(ptr),
            Expression::StrNil => Some(Syntax::String(Pos::No, "".to_string())),
            Expression::StrCons(..) => Some(Syntax::String(Pos::No, self.fetch_string(&ptr)?)),
            Expression::SymNil => Some(Syntax::Symbol(Pos::No, Symbol::root())),
            Expression::SymCons(..) => {
                let sym = self.fetch_symbol(&ptr)?;
                if let Some(sym) = lurk_syms.get(&sym) {
                    Some(Syntax::LurkSym(Pos::No, *sym))
                }
                else {
                    Some(Syntax::Symbol(Pos::No, sym))
                }
            },
            Expression::Key(..) => Some(Syntax::Symbol(Pos::No, self.fetch_key(&ptr)?)),
            Expression::Comm(..) |
            Expression::Thunk(..) |
            Expression::Fun(..) => None,
        }
    }

    pub fn fetch_syntax(&self, ptr: Ptr<F>) -> Option<Syntax<F>> {
        let lurk_syms = Symbol::lurk_syms();
        self.fetch_syntax_aux(lurk_syms, ptr)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use blstrs::Scalar as Fr;
    use proptest::prelude::*;

    // TODO: Write better tests
    #[test]
    fn display_syntax() {
        assert_eq!("nil", format!("{}", Syntax::<Fr>::nil(Pos::No)));
        assert_eq!(
            "(nil)",
            format!(
                "{}",
                Syntax::<Fr>::List(Pos::No, vec![Syntax::nil(Pos::No)])
            )
        );
        assert_eq!(
            "(nil . nil)",
            format!(
                "{}",
                Syntax::<Fr>::Improper(Pos::No, vec![Syntax::nil(Pos::No)], Box::new(Syntax::nil(Pos::No)))
            )
        )
    }

    // proptest! {
    //     #[test]
    //     fn prop_display_syntax(x in any::<Syntax<Fr>>()) {
    //         println!("{}", x);
    //         assert!(false)
    //     }
    // }
}
