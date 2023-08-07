use anyhow::{bail, Result};
use std::fmt;

use crate::field::LurkField;
use crate::num::Num;
use crate::parser::position::Pos;
use crate::ptr::Ptr;
use crate::state::{lurk_sym_path, meta_package_symbol, State};
use crate::store::Store;
use crate::uint::UInt;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

// Lurk syntax
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Syntax<F: LurkField> {
    Num(Pos, Num<F>),
    // A u64 integer: 1u64, 0xffu64
    UInt(Pos, UInt),
    // An absolute path with a keyword flag: .a.b, :a.b
    Path(Pos, Vec<String>, bool),
    // A relative path: a.b
    RelPath(Pos, Vec<String>),
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
        let leaf = prop_oneof![
            any::<Num<Fr>>().prop_map(|x| Syntax::Num(Pos::No, x)),
            any::<UInt>().prop_map(|x| Syntax::UInt(Pos::No, x)),
            any::<(Vec<String>, bool)>().prop_map(|(ss, b)| Syntax::Path(Pos::No, ss, b)),
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
        use crate::symbol::Symbol;
        match self {
            Self::Num(_, x) => write!(f, "{}", x),
            Self::UInt(_, x) => write!(f, "{}u64", x),
            Self::Path(_, path, key) => {
                let sym = if *key {
                    Symbol::key(path)
                } else {
                    Symbol::sym(path)
                };
                write!(f, "{}", sym)
            }
            Self::RelPath(_, path) => {
                write!(f, "{}", Symbol::format_path(path))
            }
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
    pub fn intern_syntax(&mut self, state: &mut State, syn: Syntax<F>) -> Result<Ptr<F>> {
        match syn {
            Syntax::Num(_, x) => Ok(self.intern_num(x)),
            Syntax::UInt(_, x) => Ok(self.intern_uint(x)),
            Syntax::Char(_, x) => Ok(self.intern_char(x)),
            Syntax::Path(_, path, key) => {
                let sym = state.intern_path(&path, key)?;
                Ok(self.intern_symbol(&sym))
            }
            Syntax::RelPath(_, path) => {
                let sym = state.intern_relative_path(&path)?;
                Ok(self.intern_symbol(&sym))
            }
            Syntax::String(_, x) => Ok(self.intern_string(&x)),
            Syntax::Quote(pos, x) => {
                let xs = vec![Syntax::Path(pos, lurk_sym_path("quote"), false), *x];
                self.intern_syntax(state, Syntax::List(pos, xs))
            }
            Syntax::List(_, xs) => {
                let mut cdr = self.nil_ptr();
                for x in xs.into_iter().rev() {
                    let car = self.intern_syntax(state, x)?;
                    cdr = self.intern_cons(car, cdr);
                }
                Ok(cdr)
            }
            Syntax::Improper(_, xs, end) => {
                let mut cdr = self.intern_syntax(state, *end)?;
                for x in xs.into_iter().rev() {
                    let car = self.intern_syntax(state, x)?;
                    cdr = self.intern_cons(car, cdr);
                }
                Ok(cdr)
            }
        }
    }

    pub fn intern_syntax_meta(&mut self, state: &mut State, syn: Syntax<F>) -> Result<Ptr<F>> {
        if let Syntax::List(pos_list, mut list) = syn {
            macro_rules! pre {
                () => {{
                    let saved_package_name = state.get_current_package_name().clone();
                    state.set_current_package(meta_package_symbol().into())?;
                    saved_package_name
                }};
            }
            macro_rules! pos {
                ( $saved_package_name:expr, $pos_path:expr, $sym:expr ) => {{
                    state.set_current_package($saved_package_name)?;
                    let sym_syn = Syntax::Path(*$pos_path, $sym.path().to_vec(), false);
                    list[0] = sym_syn;
                    self.intern_syntax(state, Syntax::List(pos_list, list))
                }};
            }
            match list.first() {
                Some(Syntax::RelPath(pos_path, path)) => {
                    let saved_package_name = pre!();
                    let sym = state.intern_relative_path(path)?;
                    pos!(saved_package_name, pos_path, sym)
                }
                Some(Syntax::Path(pos_path, path, false)) => {
                    let saved_package_name = pre!();
                    let sym = state.intern_path(path, false)?;
                    pos!(saved_package_name, pos_path, sym)
                }
                _ => bail!("The head of a meta command must be a symbol"),
            }
        } else {
            bail!("Meta commands must be lists: !(<cmd> <args...>)")
        }
    }

    //     /// Tries to fetch a syntactic list from an expression pointer, by looping over cons cells and
    //     /// collecting their contents. If the ptr does not point to a cons or nil (i.e. not a list) we
    //     /// return None. If after traversing zero or more cons cells we hit a `nil`, we return a proper
    //     /// list (`Syntax::List`), otherwise an improper list (`Syntax::Improper`). If the proper list
    //     /// is a quotation `(quote x)`, then we return the syntactic quotation `Syntax::Quote`
    //     fn fetch_syntax_list(&self, mut ptr: Ptr<F>) -> Option<Syntax<F>> {
    //         let mut list = vec![];
    //         loop {
    //             match self.fetch(&ptr)? {
    //                 Expression::Cons(car, cdr) => {
    //                     list.push(self.fetch_syntax(car)?);
    //                     ptr = cdr;
    //                 }
    //                 Expression::Nil => {
    //                     return Some(Syntax::List(Pos::No, list));
    //                 }
    //                 _ => {
    //                     if list.is_empty() {
    //                         return None;
    //                     } else {
    //                         let end = Box::new(self.fetch_syntax(ptr)?);
    //                         return Some(Syntax::Improper(Pos::No, list, end));
    //                     }
    //                 }
    //             }
    //         }
    //     }

    //     pub fn fetch_syntax(&self, ptr: Ptr<F>) -> Option<Syntax<F>> {
    //         let expr = self.fetch(&ptr)?;
    //         match expr {
    //             Expression::Num(f) => Some(Syntax::Num(Pos::No, f)),
    //             Expression::Char(_) => Some(Syntax::Char(Pos::No, self.fetch_char(&ptr)?)),
    //             Expression::UInt(_) => Some(Syntax::UInt(Pos::No, self.fetch_uint(&ptr)?)),
    //             Expression::Nil | Expression::Cons(..) => self.fetch_syntax_list(ptr),
    //             Expression::EmptyStr => Some(Syntax::String(Pos::No, "".to_string())),
    //             Expression::Str(..) => Some(Syntax::String(Pos::No, self.fetch_string(&ptr)?)),
    //             Expression::RootSym => Some(Syntax::Path(Pos::No, vec![], false)),
    //             Expression::Sym(..) => {
    //                 let sym = self.fetch_sym(&ptr)?;
    //                 Some(Syntax::Path(Pos::No, sym.path().to_vec(), false))
    //             }
    //             Expression::Key(..) => {
    //                 let sym = self.fetch_key(&ptr)?;
    //                 Some(Syntax::Path(Pos::No, sym.path().to_vec(), true))
    //             }
    //             Expression::Comm(..) | Expression::Thunk(..) | Expression::Fun(..) => None,
    //         }
    //     }
}

// #[cfg(test)]
// mod test {
//     use super::*;
//     use blstrs::Scalar as Fr;

//     #[test]
//     fn display_syntax() {
//         let mut s = Store::<Fr>::default();

//         macro_rules! improper {
//             ( $( $x:expr ),+ ) => {
//                 {
//                     let mut vec = vec!($($x,)*);
//                     let mut tmp = vec.pop().unwrap();
//                     while let Some(x) = vec.pop() {
//                         tmp = s.cons(x, tmp);
//                     }
//                     tmp
//                 }
//             };
//         }

//         macro_rules! list {
//             ( $( $x:expr ),* ) => {
//                 {
//                     let mut vec = vec!($($x,)*);
//                     let mut tmp = s.nil();
//                     while let Some(x) = vec.pop() {
//                         tmp = s.cons(x, tmp);
//                     }
//                     tmp
//                 }
//             };
//         }

//         macro_rules! sym {
//             ( $sym:ident ) => {{
//                 s.sym(stringify!($sym))
//             }};
//         }

//         // Quote tests
//         let expr = list!(sym!(quote), list!(sym!(f), sym!(x), sym!(y)));
//         let output = s.fetch_syntax(expr).unwrap();
//         assert_eq!("'(f x y)".to_string(), format!("{}", output));

//         let expr = list!(sym!(quote), sym!(f), sym!(x), sym!(y));
//         let output = s.fetch_syntax(expr).unwrap();
//         assert_eq!("(quote f x y)".to_string(), format!("{}", output));

//         // List tests
//         let expr = list!();
//         let output = s.fetch_syntax(expr).unwrap();
//         assert_eq!("nil".to_string(), format!("{}", output));

//         let expr = improper!(sym!(x), sym!(y), sym!(z));
//         let output = s.fetch_syntax(expr).unwrap();
//         assert_eq!("(x y . z)".to_string(), format!("{}", output));

//         let expr = improper!(sym!(x), sym!(y), sym!(nil));
//         let output = s.fetch_syntax(expr).unwrap();
//         assert_eq!("(x y)".to_string(), format!("{}", output));
//     }

//     #[test]
//     fn syntax_rootkey_roundtrip() {
//         let mut store1 = Store::<Fr>::default();
//         let ptr1 = store1.intern_syntax(Syntax::Path(Pos::No, vec![], true));
//         let (z_store, z_ptr) = store1.to_z_store_with_ptr(&ptr1).unwrap();
//         let (store2, ptr2) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
//         let y = store2.fetch_syntax(ptr2).unwrap();
//         let ptr2 = store1.intern_syntax(y);
//         assert!(store1.ptr_eq(&ptr1, &ptr2).unwrap());
//     }
//     #[test]
//     fn syntax_empty_keyword_roundtrip() {
//         let mut store1 = Store::<Fr>::default();
//         let ptr1 = store1.intern_syntax(Syntax::Path(Pos::No, vec!["".into()], true));
//         let (z_store, z_ptr) = store1.to_z_store_with_ptr(&ptr1).unwrap();
//         let (store2, ptr2) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
//         let y = store2.fetch_syntax(ptr2).unwrap();
//         let ptr2 = store1.intern_syntax(y);
//         assert!(store1.ptr_eq(&ptr1, &ptr2).unwrap());
//     }

//     proptest! {
//         // TODO: Proptest the Store/ZStore roundtrip with two distinct syntaxes
//         #[test]
//         fn syntax_full_roundtrip(x in any::<Syntax<Fr>>()) {
//             let mut store1 = Store::<Fr>::default();
//             let ptr1 = store1.intern_syntax(x);
//             let (z_store, z_ptr) = store1.to_z_store_with_ptr(&ptr1).unwrap();
//             let (store2, ptr2) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
//             let y = store2.fetch_syntax(ptr2).unwrap();
//             let ptr2 = store1.intern_syntax(y);
//             assert!(store1.ptr_eq(&ptr1, &ptr2).unwrap());
//         }
//     }
// }
