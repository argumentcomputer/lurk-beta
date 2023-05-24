use crate::field::LurkField;
use crate::ptr::Ptr;
use crate::store::Store;
use nom::sequence::preceded;
use nom::Parser;
use thiserror;

pub mod base;
pub mod error;
pub mod position;
pub mod string;
pub mod syntax;

pub type Span<'a> = nom_locate::LocatedSpan<&'a str>;

// see https://github.com/sg16-unicode/sg16/issues/69
pub static LURK_WHITESPACE: [char; 27] = [
    '\u{0009}', '\u{000A}', '\u{000B}', '\u{000C}', '\u{000D}', '\u{0020}', '\u{0085}', '\u{200E}',
    '\u{200F}', '\u{2028}', '\u{2029}', '\u{20A0}', '\u{1680}', '\u{2000}', '\u{2001}', '\u{2002}',
    '\u{2003}', '\u{2004}', '\u{2005}', '\u{2006}', '\u{2007}', '\u{2008}', '\u{2009}', '\u{200A}',
    '\u{202F}', '\u{205F}', '\u{3000}',
];

#[derive(thiserror::Error, Debug, Clone)]
pub enum Error {
    #[error("Empty input error")]
    NoInput,
    #[error("Syntax error: {0}")]
    Syntax(String),
}

impl<F: LurkField> Store<F> {
    pub fn read(&mut self, input: &str) -> Result<Ptr<F>, Error> {
        match preceded(syntax::parse_space, syntax::parse_syntax()).parse(Span::new(input)) {
            Ok((_i, x)) => Ok(self.intern_syntax(x)),
            Err(e) => Err(Error::Syntax(format!("{}", e))),
        }
    }

    pub fn read_maybe_meta<'a>(
        &mut self,
        input: Span<'a>,
    ) -> Result<(Span<'a>, Ptr<F>, bool), Error> {
        use syntax::*;
        match preceded(parse_space, parse_maybe_meta()).parse(input) {
            Ok((i, Some((is_meta, x)))) => Ok((i, self.intern_syntax(x), is_meta)),
            Ok((_, None)) => Err(Error::NoInput),
            Err(e) => Err(Error::Syntax(format!("{}", e))),
        }
    }
}

//#[cfg(test)]
//mod test {
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
//            let expr = store.fetch(ptr).unwrap();
//            dbg!(&expected, &expr.as_sym_str());
//            assert_eq!(expr.as_sym_str().unwrap(), expected);
//        };
//
//        test(".lurk.+", ".LURK.+");
//        test(".lurk.-", ".LURK.-");
//        test("-", ".LURK.-");
//        test("-xxx", ".LURK.-XXX");
//        test("asdf", ".LURK.ASDF");
//        test("asdf ", ".LURK.ASDF");
//        test("asdf(", ".LURK.ASDF");
//        test(" asdf", ".LURK.ASDF");
//        test(" asdf ", ".LURK.ASDF");
//        test(
//            "
//        asdf(",
//            ".LURK.ASDF",
//        );
//        test("foo-bar", ".LURK.FOO-BAR");
//        test("foo_bar", ".LURK.FOO_BAR");
//
//        test("|foo_BAR|", ".LURK.|foo_BAR|");
//
//        test(":asdf", ":ASDF");
//        test(":asdf.fdsa", ":ASDF.FDSA");
//        test("asdf.fdsa", ".LURK.ASDF.FDSA");
//
//        test(
//            "|A quoted symbol: α, β, ∧, ∨, ∑|",
//            ".LURK.|A quoted symbol: α, β, ∧, ∨, ∑|",
//        );
//        test("|UNNECESSARY-QUOTING|", ".LURK.UNNECESSARY-QUOTING");
//        test(
//            "|A quoted symbol with a dot.|",
//            ".LURK.|A quoted symbol with a dot.|",
//        );
//        test(
//            r#"|Symbol with \|escaped pipes\| contained|"#,
//            r#".LURK.|Symbol with \|escaped pipes\| contained|"#,
//        );
//
//        test("|asdf|.fdsa", ".LURK.|asdf|.FDSA");
//        test("|ASDF|.fdsa", ".LURK.ASDF.FDSA");
//        test("|ASDF.FDSA|.xxx", ".LURK.|ASDF.FDSA|.XXX");
//        test("|ASDF.fdsa|", ".LURK.|ASDF.fdsa|");
//        test("|ASDF.FDSA|", ".LURK.|ASDF.FDSA|");
//
//        // TODO: Test that this is an error: "asdf:fdsa"
//    }
//
//    #[test]
//    fn test_sym_path() {
//        let test = |input, expected: Vec<&str>| {
//            let mut store = Store::<Fr>::default();
//
//            let ptr = &store.read(input).unwrap();
//            let expr = store.fetch(ptr).unwrap();
//            let sym = expr.as_sym().unwrap();
//
//            assert_eq!(sym.path(), &expected);
//        };
//
//        test("asdf", vec!["", "LURK", "ASDF"]);
//        test("asdf.fdsa", vec!["", "LURK", "ASDF", "FDSA"]);
//
//        test(".asdf", vec!["", "ASDF"]);
//        test(".asdf.fdsa", vec!["", "ASDF", "FDSA"]);
//        test(".|APPLE.ORANGE|.pear", vec!["", "APPLE.ORANGE", "PEAR"]);
//        test(".|asdf|.fdsa", vec!["", "asdf", "FDSA"]);
//
//        test(".asdf.|fdsa|", vec!["", "ASDF", "fdsa"]);
//
//        test(":asdf", vec!["", "ASDF"]);
//        test(":asdf.|fdsa|", vec!["", "ASDF", "fdsa"]);
//
//        test(".||", vec!["", ""]);
//        test(".||.||", vec!["", "", ""]);
//        test(":||", vec!["", ""]);
//        test(":||.||", vec!["", "", ""]);
//        test(".asdf.||.fdsa.||", vec!["", "ASDF", "", "FDSA", ""]);
//    }
//
//    #[test]
//    fn symbol_in_list() {
//        let mut store = Store::<Fr>::default();
//        let expr = store.read("'(+)").unwrap();
//        let expr2 = store.read("'(.lurk.+)").unwrap();
//
//        assert!(store.ptr_eq(&expr, &expr2).unwrap());
//    }
//
//    #[test]
//    fn naked_dot_in_list() {
//        let mut store = Store::<Fr>::default();
//
//        let expected_error = match store.read("(.)").err().unwrap() {
//            Error::Syntax(s) => s == *"Misplaced dot",
//            _ => false,
//        };
//
//        assert!(expected_error);
//    }
//
//    #[test]
//    fn absolute_symbol_in_list() {
//        let mut store = Store::<Fr>::default();
//
//        let expr = store.read("(a .b)").unwrap();
//        let expr2 = store.read("(.b)").unwrap();
//        let a = store.read("a").unwrap();
//        let b = store.read(".b").unwrap();
//        let nil = store.nil();
//
//        let b_list = store.cons(b, nil);
//        let a_b_list = store.cons(a, b_list);
//
//        assert!(store.ptr_eq(&a_b_list, &expr).unwrap());
//        assert!(store.ptr_eq(&b_list, &expr2).unwrap());
//    }
//
//    #[test]
//    fn naked_dot() {
//        let mut store = Store::<Fr>::default();
//
//        let expected_error = match store.read(".").err().unwrap() {
//            Error::Syntax(s) => s == *"Misplaced dot",
//            _ => false,
//        };
//
//        assert!(expected_error);
//    }
//
//    #[test]
//    fn list_tail() {
//        let mut store = Store::<Fr>::default();
//        let expr = store.read("'(+)").unwrap();
//        let expr2 = store.read("'(.lurk.+)").unwrap();
//
//        assert!(store.ptr_eq(&expr, &expr2).unwrap());
//    }
//
//    #[test]
//    fn read_nil() {
//        let mut store = Store::<Fr>::default();
//        let expr = store.read(".lurk.nil").unwrap();
//        let expr2 = store.read("nil").unwrap();
//        assert!(expr.is_nil());
//        assert!(expr2.is_nil());
//    }
//
//    #[test]
//    fn read_num() {
//        let test = |input, expected: u64| {
//            let mut store = Store::<Fr>::default();
//            let expr = store.read(input).unwrap();
//            let expected = store.intern_num(expected);
//            assert!(store.ptr_eq(&expected, &expr).unwrap());
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
//
//        let test = |input, expected: Fr| {
//            let mut store = Store::<Fr>::default();
//            let expr = store.read(input).unwrap();
//            let expected = store.intern_num(crate::num::Num::from_scalar(expected));
//            assert!(store.ptr_eq(&expected, &expr).unwrap());
//        };
//        test("0x10", Fr::from(16));
//        test("0x22", Fr::from(34));
//        test("0x0010", Fr::from(16));
//        test("0x0022", Fr::from(34));
//
//        test("0X10", Fr::from(16));
//        test("0X22", Fr::from(34));
//
//        test("0x000e", Fr::from(14));
//
//        test(
//            "0x000000000000000000000000000000000000000000000000000000000000000f",
//            Fr::from(15),
//        );
//
//        test("0x000F", Fr::from(15));
//
//        test(
//            "0x000000000000000000000000000000000000000000000000000000000000000F",
//            Fr::from(15),
//        );
//
//        {
//            let x = 18446744073709551615;
//            assert_eq!(u64::MAX, x);
//            test("18446744073709551616", Fr::from(x) + Fr::from(1));
//        }
//
//        test("1230xa", Fr::from(1230));
//
//        let test = |a, b| {
//            let mut store = Store::<Fr>::default();
//            let a_num = store.read(a).unwrap();
//            let b_num = store.read(b).unwrap();
//            dbg!(a_num.fmt_to_string(&store), b_num.fmt_to_string(&store));
//            assert!(store.ptr_eq(&a_num, &b_num).unwrap());
//        };
//
//        test("18446744073709551616", "0x10000000000000000");
//        test("123456789123456789123", "0x6B14E9F9B0DF36A83");
//
//        // > (- 0 1)
//        // [3 iterations] => 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000
//        // (format nil "~x" (mod (expt 2 256) (1+ #x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000)))
//        // "1824B159ACC5056F998C4FEFECBC4FF55884B7FA0003480200000001FFFFFFFE"
//        test(
//            "0x10000000000000000000000000000000000000000000000000000000000000000",
//            "0x1824B159ACC5056F998C4FEFECBC4FF55884B7FA0003480200000001FFFFFFFE",
//        );
//
//        test(
//            "-1",
//            "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000",
//        );
//        test(
//            "1/2",
//            "0x39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff80000001",
//        );
//        test(
//            "-1/2",
//            "0x39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff80000000",
//        );
//        test("0xe/2", "7");
//        test("-0xf/2", "-15/2");
//    }
//
//    #[test]
//    fn read_u64() {
//        let test = |input, expected: u64| {
//            let mut store = Store::<Fr>::default();
//            let expr = store.read(input).unwrap();
//            let expected = store.get_u64(expected);
//            assert!(store.ptr_eq(&expected, &expr).unwrap());
//        };
//
//        test("123u64", 123);
//        test("0xffu64", 255);
//        test("123U64", 123);
//        test("0XFFU64", 255);
//
//        // This is the largest U64.
//        test("0xffffffffffffffffu64", 18446744073709551615);
//    }
//
//    #[test]
//    fn read_u64_overflows() {
//        let test = |input| {
//            let mut store = Store::<Fr>::default();
//            let expr = store.read(input);
//            assert!(expr.is_err());
//        };
//
//        test("0xffffffffffffffffffu64");
//        test("999999999999999999999999999999999999u64");
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
//        let a = s.sym("pumpkin");
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
//        assert_eq!(
//            s.read("(123 321)").unwrap(),
//            s.read("(123 . ( 321 ))").unwrap()
//        )
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
//        test(&mut s, "|α|");
//        test(&mut s, "A");
//        test(&mut s, "(A . B)");
//        test(&mut s, "(A B C)");
//        test(&mut s, "(A (B) C)");
//        test(&mut s, "(A (B . C) (D E (F)) G)");
//        // TODO: Writer should replace (quote a) with 'a.
//        // test(&mut s, "'A");
//        // test(&mut s, "'(A B)");
//    }
//
//    #[test]
//    fn read_maybe_meta() {
//        let mut s = Store::<Fr>::default();
//        let package = Package::default();
//        let test =
//            |store: &mut Store<Fr>, input: &str, expected_ptr: Ptr<Fr>, expected_meta: bool| {
//                let mut chars = input.chars().peekmore();
//
//                let (ptr, meta) = store.read_maybe_meta(&mut chars, &package).unwrap();
//                {
//                    assert_eq!(expected_ptr, ptr);
//                    assert_eq!(expected_meta, meta);
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
// !asdf",
//                sym,
//                true,
//            );
//        }
//    }
//    #[test]
//    fn is_keyword() {
//        let mut s = Store::<Fr>::default();
//        let kw = s.read(":uiop").unwrap();
//        let kw2 = s.sym(":UIOP");
//        let not_kw = s.sym(".UIOP");
//
//        let kw_fetched = s.fetch(&kw).unwrap();
//        let kw2_fetched = s.fetch(&kw2).unwrap();
//        let not_kw_fetched = s.fetch(&not_kw).unwrap();
//
//        assert!(kw_fetched.is_keyword_sym());
//        assert!(kw2_fetched.is_keyword_sym());
//        assert!(!not_kw_fetched.is_keyword_sym());
//    }
//
//    #[test]
//    fn read_string() {
//        let mut s = Store::<Fr>::default();
//
//        let test =
//            |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>, expr: Option<&str>| {
//                let maybe_string = store.read_string(&mut input.chars().peekmore()).ok();
//                assert_eq!(expected, maybe_string);
//                if let Some(ptr) = maybe_string {
//                    let res = store
//                        .fetch(&ptr)
//                        .unwrap_or_else(|| panic!("failed to fetch: {:?}", input));
//                    assert_eq!(res.as_str(), expr);
//                }
//            };
//
//        {
//            let str = s.intern_str("asdf");
//            test(&mut s, "\"asdf\"", Some(str), Some("asdf"));
//            test(&mut s, "\"asdf", None, None);
//            test(&mut s, "asdf", None, None);
//        }
//        {
//            let input = "\"foo/bar/baz\"";
//            let ptr = s.read_string(&mut input.chars().peekmore()).unwrap();
//            let res = s
//                .fetch(&ptr)
//                .unwrap_or_else(|| panic!("failed to fetch: {:?}", input));
//            assert_eq!(res.as_str().unwrap(), "foo/bar/baz");
//        }
//
//        {
//            let str = s.intern_str(r#"Bob "Bugs" Murphy"#);
//            test(
//                &mut s,
//                r#""Bob \"Bugs\" Murphy""#,
//                Some(str),
//                Some(r#"Bob "Bugs" Murphy"#),
//            );
//        }
//    }
//
//    #[test]
//    fn read_write_char() {
//        let s = &mut Store::<Fr>::default();
//
//        let a = 'a';
//        let char = s.get_char(a);
//        let input = r#"#\a"#;
//        let ptr = s.read(input).unwrap();
//        let res = s.fetch(&ptr).unwrap();
//        match res {
//            crate::expr::Expression::Char(c) => assert_eq!(a, c),
//            _ => panic!("not a Char"),
//        };
//        let printed = res.fmt_to_string(s);
//
//        assert_eq!(char, ptr);
//        assert_eq!(input, printed);
//    }
//
//    #[test]
//    fn read_with_comments() {
//        let mut s = Store::<Fr>::default();
//
//        let test = |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>| {
//            let res = store.read(input).ok();
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
//
//    #[test]
//    fn read_non_fractions() {
//        let mut s = Store::<Fr>::default();
//
//        let test = |store: &mut Store<Fr>, a: &str, b: &str| {
//            let res_a = store.read(a).unwrap();
//            let res_b = store.read(b).unwrap();
//            assert!(store.ptr_eq(&res_a, &res_b).unwrap());
//        };
//        // These tests demonstrate that '/' behaves like other arithmetic operators
//        // when a fraction is not being parsed.
//
//        test(&mut s, "'(1+ 2)", "'(1 + 2)");
//        test(&mut s, "'(1/ 2)", "'(1 / 2)");
//
//        test(&mut s, "'(0xa+ 2)", "'(0xa + 2)");
//        test(&mut s, "'(0xa/ 2)", "'(0xa / 2)");
//
//        test(&mut s, "1+", "1");
//        test(&mut s, "1/", "1");
//
//        test(&mut s, "0xa+", "0xa");
//        test(&mut s, "0xa/", "0xa");
//    }
//}
