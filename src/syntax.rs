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
    // Temporary shim until packages are correctly implemented
    LurkSym(Pos, LurkSym),
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

impl<F: LurkField> Syntax<F> {
    pub fn nil(pos: Pos) -> Syntax<F> {
        Syntax::LurkSym(pos, LurkSym::Nil)
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
            any::<Symbol>().prop_map(|x| {
                if let Some(val) = Symbol::lurk_syms().get(&Symbol::lurk_sym(&format!("{}", x))) {
                    Syntax::LurkSym(Pos::No, *val)
                } else {
                    Syntax::Symbol(Pos::No, x)
                }
            }),
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
            Self::Symbol(_, sym) => write!(f, "{}", sym),
            Self::LurkSym(_, sym) => write!(f, "{}", sym),
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

    /// Tries to fetch a syntactic list from an expression pointer, by looping over cons cells and
    /// collecting their contents. If the ptr does not point to a cons or nil (i.e. not a list) we
    /// return None. If after traversing zero or more cons cells we hit a `nil`, we return a proper
    /// list (`Syntax::List`), otherwise an improper list (`Syntax::Improper`). If the proper list
    /// is a quotation `(quote x)`, then we return the syntactic quotation `Syntax::Quote`
    fn fetch_syntax_list(&self, mut ptr: Ptr<F>) -> Option<Syntax<F>> {
        let mut list = vec![];
        loop {
            match self.fetch(&ptr)? {
                Expression::Cons(car, cdr) => {
                    list.push(self.fetch_syntax(car)?);
                    ptr = cdr;
                }
                Expression::Nil => {
                    return match (list.len(), list.get(0)) {
                        (0, _) => Some(Syntax::LurkSym(Pos::No, LurkSym::Nil)),
                        (2, Some(Syntax::LurkSym(_, LurkSym::Quote))) => {
                            Some(Syntax::Quote(Pos::No, Box::new(list[1].clone())))
                        }
                        _ => Some(Syntax::List(Pos::No, list)),
                    }
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

    fn fetch_syntax_aux(
        &self,
        lurk_syms: HashMap<Symbol, LurkSym>,
        ptr: Ptr<F>,
    ) -> Option<Syntax<F>> {
        let expr = self.fetch(&ptr)?;
        match expr {
            Expression::Num(f) => Some(Syntax::Num(Pos::No, f)),
            Expression::Char(_) => Some(Syntax::Char(Pos::No, self.fetch_char(&ptr)?)),
            Expression::UInt(_) => Some(Syntax::UInt(Pos::No, self.fetch_uint(&ptr)?)),
            Expression::Nil | Expression::Cons(..) => self.fetch_syntax_list(ptr),
            Expression::EmptyStr => Some(Syntax::String(Pos::No, "".to_string())),
            Expression::Str(..) => Some(Syntax::String(Pos::No, self.fetch_string(&ptr)?)),
            Expression::RootKey => Some(Syntax::Symbol(Pos::No, Symbol::key_root())),
            Expression::RootSym => Some(Syntax::Symbol(Pos::No, Symbol::root())),
            Expression::Sym(..) => {
                let sym = self.fetch_symbol(&ptr)?;
                if let Some(sym) = lurk_syms.get(&sym) {
                    Some(Syntax::LurkSym(Pos::No, *sym))
                } else {
                    Some(Syntax::Symbol(Pos::No, sym))
                }
            }
            Expression::Key(..) => Some(Syntax::Symbol(Pos::No, self.fetch_key(&ptr)?)),
            Expression::Comm(..) | Expression::Thunk(..) | Expression::Fun(..) => None,
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

    #[test]
    fn display_syntax() {
        let mut s = Store::<Fr>::default();
        let lurk_syms = Symbol::lurk_syms();

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
                    let mut tmp = s.nil();
                    while let Some(x) = vec.pop() {
                        tmp = s.cons(x, tmp);
                    }
                    tmp
                }
            };
        }

        macro_rules! sym {
            ( $sym:ident ) => {{
                let sym = stringify!($sym);
                if lurk_syms.contains_key(&Symbol::lurk_sym(sym)) {
                    s.lurk_sym(sym)
                } else {
                    s.sym(sym)
                }
            }};
        }

        // Quote tests
        let expr = list!(sym!(quote), list!(sym!(f), sym!(x), sym!(y)));
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("'(f x y)".to_string(), format!("{}", output));

        let expr = list!(sym!(quote), sym!(f), sym!(x), sym!(y));
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("(quote f x y)".to_string(), format!("{}", output));

        // List tests
        let expr = list!();
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("nil".to_string(), format!("{}", output));

        let expr = improper!(sym!(x), sym!(y), sym!(z));
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("(x y . z)".to_string(), format!("{}", output));

        let expr = improper!(sym!(x), sym!(y), sym!(nil));
        let output = s.fetch_syntax(expr).unwrap();
        assert_eq!("(x y)".to_string(), format!("{}", output));
    }

    #[test]
    fn syntax_key_roundtrip() {
        let mut store1 = Store::<Fr>::default();
        let ptr1 = store1.intern_syntax(Syntax::Symbol(Pos::No, Symbol::Key(vec![])));
        let (z_store, z_ptr) = store1.to_z_store_with_ptr(&ptr1).unwrap();
        let (store2, ptr2) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
        let y = store2.fetch_syntax(ptr2).unwrap();
        let ptr2 = store1.intern_syntax(y);
        assert!(store1.ptr_eq(&ptr1, &ptr2).unwrap());
    }
    #[test]
    fn syntax_key_roundtrip2() {
        let mut store1 = Store::<Fr>::default();
        let ptr1 = store1.intern_syntax(Syntax::Symbol(Pos::No, Symbol::Key(vec!["".to_string()])));
        println!("ptr1 {:?}", ptr1);
        let (z_store, z_ptr) = store1.to_z_store_with_ptr(&ptr1).unwrap();
        println!("z_ptr {:?}", z_ptr);
        let (store2, ptr2) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
        println!("ptr2 {:?}", ptr2);
        let y = store2.fetch_syntax(ptr2).unwrap();
        println!("y {:?}", y);
        let ptr2 = store1.intern_syntax(y);
        println!("ptr2 {:?}", ptr2);
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
