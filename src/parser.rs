use std::iter::Peekable;

use ff::PrimeField;

use crate::store::{Ptr, Store};

use nom_locate::LocatedSpan;

pub type Span<'a> = LocatedSpan<&'a str>;

pub mod base;
pub mod error;
pub mod string;
pub mod syntax;

use error::ParseError;
use syntax::Term;

impl<F: PrimeField> Store<F> {
    pub fn read(&mut self, input: &str) -> Option<Ptr<F>> {
        self.parse_term(input).ok()
    }

    pub fn parse_term<'a>(&mut self, input: &'a str) -> Result<Ptr<F>, ParseError<Span<'a>>> {
        match syntax::parse_term()(Span::<'a>::new(input)) {
            Ok((_, t)) => {
                let ptr = self.store_term(t);
                Ok(ptr)
            }
            Err(nom::Err::Error(e)) => Err(e),
            Err(nom::Err::Failure(e)) => Err(e),
            // TODO: use complete combinator to remove this case, which should
            // be unreachable
            Err(nom::Err::Incomplete(x)) => {
                panic!("incomplete input: {:?}", x)
            }
        }
    }
    pub fn store_term(&mut self, input: Term<F>) -> Ptr<F> {
        match input {
            Term::Str(s) => self.intern_str(s),
            Term::Sym(s) => {
                let mut s = s;
                // TODO: double check that converting to uppercase like this is
                // right
                Self::convert_sym_case(&mut s);
                self.intern_sym(s)
            }
            Term::Num(x) => self.intern_num(x),
            Term::Nil => self.intern_nil(),
            Term::Cons(car, cdr) => {
                let car_ptr = self.store_term(*car);
                let cdr_ptr = self.store_term(*cdr);
                self.intern_cons(car_ptr, cdr_ptr)
            }
        }
    }
}

#[cfg(test)]
mod test {
    //    use crate::writer::Write;
    //    use blstrs::Scalar as Fr;
    //
    //    use super::*;
    //
    //    #[test]
    //    fn read_sym() {
    //        let test = |input, expected: &str| {
    //            let mut store = Store::<Fr>::default();
    //            let ptr = &store.read(input).unwrap();
    //            let expr = store.fetch(&ptr).unwrap();
    //
    //            assert_eq!(expected, expr.as_sym_str().unwrap());
    //        };
    //
    //        test("asdf", "ASDF");
    //        test("asdf ", "ASDF");
    //        test("asdf(", "ASDF");
    //        test(" asdf", "ASDF");
    //        test(" asdf ", "ASDF");
    //        test(
    //            "
    //asdf(", "ASDF",
    //        );
    //    }
    //
    //    #[test]
    //    fn read_nil() {
    //        let mut store = Store::<Fr>::default();
    //        let expr = store.read("nil").unwrap();
    //        assert!(expr.is_nil());
    //    }
    //
    //    #[test]
    //    fn read_num() {
    //        let test = |input, expected: u64| {
    //            let mut store = Store::<Fr>::default();
    //            let expr = store.read(input).unwrap();
    //            assert_eq!(store.intern_num(expected), expr);
    //        };
    //        test("123", 123);
    //        test("0987654321", 987654321);
    //        test("123)", 123);
    //        test("123 ", 123);
    //        test("123z", 123);
    //        test(" 123", 123);
    //        test(
    //            "
    //0987654321",
    //            987654321,
    //        );
    //    }
    //
    //    #[test]
    //    fn read_list() {
    //        let mut s = Store::<Fr>::default();
    //        let test = |store: &mut Store<Fr>, input, expected| {
    //            let expr = store.read(input).unwrap();
    //            assert_eq!(expected, &expr);
    //        };
    //
    //        let a = s.num(123);
    //        let b = s.nil();
    //        let expected = s.cons(a, b);
    //        test(&mut s, "(123)", &expected);
    //
    //        let a = s.num(321);
    //        let expected2 = s.cons(a, expected);
    //        test(&mut s, "(321 123)", &expected2);
    //
    //        let a = s.sym("PUMPKIN");
    //        let expected3 = s.cons(a, expected2);
    //        test(&mut s, "(pumpkin 321 123)", &expected3);
    //
    //        let expected4 = s.cons(expected, s.get_nil());
    //        test(&mut s, "((123))", &expected4);
    //
    //        let (a, b) = (s.num(321), s.nil());
    //        let alt = s.cons(a, b);
    //        let expected5 = s.cons(alt, expected4);
    //        test(&mut s, "((321) (123))", &expected5);
    //
    //        let expected6 = s.cons(expected2, expected3);
    //        test(&mut s, "((321 123) pumpkin 321 123)", &expected6);
    //
    //        let (a, b) = (s.num(1), s.num(2));
    //        let pair = s.cons(a, b);
    //        let list = [pair, s.num(3)];
    //        let expected7 = s.intern_list(&list);
    //        test(&mut s, "((1 . 2) 3)", &expected7);
    //    }
    //
    //    #[test]
    //    fn read_improper_list() {
    //        let mut s = Store::<Fr>::default();
    //        let test = |store: &mut Store<Fr>, input, expected| {
    //            let expr = store.read(input).unwrap();
    //            assert_eq!(expected, &expr);
    //        };
    //
    //        let (a, b) = (s.num(123), s.num(321));
    //        let expected = s.cons(a, b);
    //        test(&mut s, "(123 . 321)", &expected);
    //
    //        assert_eq!(s.read("(123 321)"), s.read("(123 . ( 321 ))"))
    //    }
    //    #[test]
    //    fn read_print_expr() {
    //        let mut s = Store::<Fr>::default();
    //        let test = |store: &mut Store<Fr>, input| {
    //            let expr = store.read(input).unwrap();
    //            let output = expr.fmt_to_string(store);
    //            assert_eq!(input, output);
    //        };
    //
    //        test(&mut s, "A");
    //        test(&mut s, "(A . B)");
    //        test(&mut s, "(A B C)");
    //        test(&mut s, "(A (B) C)");
    //        test(&mut s, "(A (B . C) (D E (F)) G)");
    //        // test(&mut s, "'A");
    //        // test(&mut s, "'(A B)");
    //    }
    //
    //    #[test]
    //    fn read_maybe_meta() {
    //        let mut s = Store::<Fr>::default();
    //        let test =
    //            |store: &mut Store<Fr>, input: &str, expected_ptr: Ptr<Fr>, expected_meta: bool| {
    //                let mut chars = input.chars().peekable();
    //
    //                match store.read_maybe_meta(&mut chars).unwrap() {
    //                    (ptr, meta) => {
    //                        assert_eq!(expected_ptr, ptr);
    //                        assert_eq!(expected_meta, meta);
    //                    }
    //                };
    //            };
    //
    //        let num = s.num(123);
    //        test(&mut s, "123", num, false);
    //
    //        {
    //            let list = [s.num(123), s.num(321)];
    //            let l = s.list(&list);
    //            test(&mut s, " (123 321)", l, false);
    //        }
    //        {
    //            let list = [s.num(123), s.num(321)];
    //            let l = s.list(&list);
    //            test(&mut s, " !(123 321)", l, true);
    //        }
    //        {
    //            let list = [s.num(123), s.num(321)];
    //            let l = s.list(&list);
    //            test(&mut s, " ! (123 321)", l, true);
    //        }
    //        {
    //            let sym = s.sym("asdf");
    //            test(&mut s, "!asdf", sym, true);
    //        }
    //        {
    //            let sym = s.sym(":assert");
    //            let l = s.list(&[sym]);
    //            test(&mut s, "!(:assert)", l, true);
    //        }
    //        {
    //            let sym = s.sym("asdf");
    //            test(
    //                &mut s,
    //                ";; comment
    //!asdf",
    //                sym,
    //                true,
    //            );
    //        }
    //    }
    //    #[test]
    //    fn is_keyword() {
    //        let mut s = Store::<Fr>::default();
    //        let kw = s.sym(":UIOP");
    //        let not_kw = s.sym("UIOP");
    //
    //        assert!(s.fetch(&kw).unwrap().is_keyword_sym());
    //        assert!(!s.fetch(&not_kw).unwrap().is_keyword_sym());
    //    }
    //
    //    #[test]
    //    fn read_string() {
    //        let mut s = Store::<Fr>::default();
    //
    //        let test =
    //            |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>, expr: Option<&str>| {
    //                let maybe_string = store.read_string(&mut input.chars().peekable());
    //                assert_eq!(expected, maybe_string);
    //                if let Some(ptr) = maybe_string {
    //                    let res = store
    //                        .fetch(&ptr)
    //                        .expect(&format!("failed to fetch: {:?}", input));
    //                    assert_eq!(res.as_str(), expr);
    //                }
    //            };
    //
    //        let sym = s.intern_str("asdf");
    //        test(&mut s, "\"asdf\"", Some(sym), Some("asdf"));
    //        test(&mut s, "\"asdf", None, None);
    //        test(&mut s, "asdf", None, None);
    //
    //        {
    //            let input = "\"foo/bar/baz\"";
    //            let ptr = s.read_string(&mut input.chars().peekable()).unwrap();
    //            let res = s
    //                .fetch(&ptr)
    //                .expect(&format!("failed to fetch: {:?}", input));
    //            assert_eq!(res.as_str().unwrap(), "foo/bar/baz");
    //        }
    //    }
    //
    //    #[test]
    //    fn read_with_comments() {
    //        let mut s = Store::<Fr>::default();
    //
    //        let test = |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>| {
    //            let res = store.read(input);
    //            assert_eq!(expected, res);
    //        };
    //
    //        let num = s.num(321);
    //        test(
    //            &mut s,
    //            ";123
    //321",
    //            Some(num),
    //        );
    //    }
}
