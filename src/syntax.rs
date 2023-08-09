use std::fmt;

use crate::expr::Expression;
use crate::field::LurkField;
use crate::num::Num;
use crate::package::SymbolRef;
use crate::parser::position::Pos;
use crate::ptr::Ptr;
use crate::state::lurk_sym;
use crate::store::Store;
use crate::tag::ExprTag;
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
    Symbol(Pos, SymbolRef),
    // A string literal: "foobar", "foo\nbar"
    String(Pos, String),
    // A character literal: #\A #\λ #\u03BB
    Char(Pos, char),
    // A quoted expression: 'a, '(1 2)
    Quote(Pos, Box<Syntax<F>>),
    // A nil-terminated cons-list of expressions: (1 2 3)
    List(Pos, Vec<Syntax<F>>),
    // An improper cons-list of expressions: (1 2 . 3)
    Improper(Pos, Vec<Syntax<F>>, Box<Syntax<F>>),
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
            Self::Num(_, x) => write!(f, "{}", x),
            Self::UInt(_, x) => write!(f, "{}u64", x),
            Self::Symbol(_, x) => write!(f, "{}", x),
            Self::String(_, x) => write!(f, "\"{}\"", x.escape_default()),
            Self::Char(_, x) => {
                if *x == '(' || *x == ')' {
                    write!(f, "'\\{}'", x)
                } else {
                    write!(f, "'{}'", x.escape_default())
                }
            }
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
            Syntax::Symbol(_, symbol) => self.intern_symbol(&symbol),
            Syntax::String(_, x) => self.intern_string(&x),
            Syntax::Quote(pos, x) => {
                let xs = vec![Syntax::Symbol(pos, lurk_sym("quote").into()), *x];
                self.intern_syntax(Syntax::List(pos, xs))
            }
            Syntax::List(_, xs) => {
                let mut cdr = self.nil_ptr();
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

    /// Tries to fetch a syntactic list from an expression pointer, by looping over cons cells and
    /// collecting their contents. If the ptr does not point to a cons or nil (i.e. not a list) we
    /// return None. If after traversing zero or more cons cells we hit a `nil`, we return a proper
    /// list (`Syntax::List`), otherwise an improper list (`Syntax::Improper`). If the proper list
    /// is a quotation `(quote x)`, then we return the syntactic quotation `Syntax::Quote`
    #[allow(dead_code)]
    fn fetch_syntax_list(&self, mut ptr: Ptr<F>) -> Option<Syntax<F>> {
        let mut list = vec![];
        loop {
            match self.fetch(&ptr)? {
                Expression::Cons(car, cdr) => {
                    list.push(self.fetch_syntax(car)?);
                    ptr = cdr;
                }
                Expression::Nil => {
                    return Some(Syntax::List(Pos::No, list));
                }
                _ => {
                    if list.is_empty() {
                        return None;
                    } else {
                        let end = Box::new(self.fetch_syntax(ptr)?);
                        return Some(Syntax::Improper(Pos::No, list, end));
                    }
                }
            }
        }
    }

    fn fetch_syntax(&self, ptr: Ptr<F>) -> Option<Syntax<F>> {
        match ptr.tag {
            ExprTag::Num => Some(Syntax::Num(Pos::No, *self.fetch_num(&ptr)?)),
            ExprTag::Char => Some(Syntax::Char(Pos::No, self.fetch_char(&ptr)?)),
            ExprTag::U64 => Some(Syntax::UInt(Pos::No, self.fetch_uint(&ptr)?)),
            ExprTag::Str => Some(Syntax::String(Pos::No, self.fetch_string(&ptr)?)),
            ExprTag::Nil => Some(Syntax::Symbol(Pos::No, lurk_sym("nil").into())),
            ExprTag::Cons => self.fetch_syntax_list(ptr),
            ExprTag::Sym => Some(Syntax::Symbol(Pos::No, self.fetch_sym(&ptr)?.into())),
            ExprTag::Key => Some(Syntax::Symbol(Pos::No, self.fetch_key(&ptr)?.into())),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use blstrs::Scalar as Fr;

    #[test]
    fn display_syntax() {
        let mut s = Store::<Fr>::default();

        macro_rules! improper {
            ( $( $x:expr ),+ ) => {
                {
                    let mut vec = vec!($($x,)*);
                    let mut tmp = vec.pop().unwrap();
                    while let Some(x) = vec.pop() {
                        tmp = s.cons(x, tmp);
                    }
                    tmp
                }
            };
        }

        macro_rules! list {
            ( $( $x:expr ),* ) => {
                {
                    let mut vec = vec!($($x,)*);
                    let mut tmp = s.nil_ptr();
                    while let Some(x) = vec.pop() {
                        tmp = s.cons(x, tmp);
                    }
                    tmp
                }
            };
        }

        macro_rules! sym {
            ( $sym:ident ) => {{
                s.sym(stringify!($sym))
            }};
        }

        // Quote tests
        let expr = list!(sym!(quote), list!(sym!(f), sym!(x), sym!(y)));
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("'(f x y)", &format!("{}", output));

        let expr = list!(sym!(quote), sym!(f), sym!(x), sym!(y));
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("(quote f x y)", &format!("{}", output));

        // List tests
        let expr = list!();
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("nil", &format!("{}", output));

        let expr = improper!(sym!(x), sym!(y), sym!(z));
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("(x y . z)", &format!("{}", output));

        let expr = improper!(sym!(x), sym!(y), sym!(nil));
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("(x y)", &format!("{}", output));
    }

    #[test]
    fn syntax_rootkey_roundtrip() {
        let mut store1 = Store::<Fr>::default();
        let ptr1 = store1.intern_syntax(Syntax::Symbol(Pos::No, Symbol::root_key().into()));
        let (z_store, z_ptr) = store1.to_z_store_with_ptr(&ptr1).unwrap();
        let (store2, ptr2) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
        let y = store2.fetch_syntax(ptr2).unwrap();
        let ptr2 = store1.intern_syntax(y);
        assert!(store1.ptr_eq(&ptr1, &ptr2).unwrap());
    }

    #[test]
    fn syntax_empty_keyword_roundtrip() {
        let mut store1 = Store::<Fr>::default();
        let ptr1 = store1.intern_syntax(Syntax::Symbol(Pos::No, Symbol::key(&[""]).into()));
        let (z_store, z_ptr) = store1.to_z_store_with_ptr(&ptr1).unwrap();
        let (store2, ptr2) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
        let y = store2.fetch_syntax(ptr2).unwrap();
        let ptr2 = store1.intern_syntax(y);
        assert!(store1.ptr_eq(&ptr1, &ptr2).unwrap());
    }

    proptest! {
        // TODO: Proptest the Store/ZStore roundtrip with two distinct syntaxes
        #[test]
        fn syntax_full_roundtrip(x in any::<Syntax<Fr>>()) {
            let mut store1 = Store::<Fr>::default();
            let ptr1 = store1.intern_syntax(x);
            let (z_store, z_ptr) = store1.to_z_store_with_ptr(&ptr1).unwrap();
            let (store2, ptr2) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
            let y = store2.fetch_syntax(ptr2).unwrap();
            let ptr2 = store1.intern_syntax(y);
            assert!(store1.ptr_eq(&ptr1, &ptr2).unwrap());
        }
    }
}
