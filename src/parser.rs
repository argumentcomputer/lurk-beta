use std::iter::Peekable;

use crate::field::LurkField;

use crate::store::{Ptr, Store};

impl<F: LurkField> Store<F> {
    pub fn read(&mut self, input: &str) -> Option<Ptr<F>> {
        let mut chars = input.chars().peekable();

        self.read_next(&mut chars)
    }

    pub fn read_string<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Ptr<F>> {
        let mut result = String::new();

        if let Some('"') = skip_whitespace_and_peek(chars) {
            chars.next();
            while let Some(&c) = chars.peek() {
                chars.next();
                // TODO: This does not handle any escaping, so strings containing " cannot be read.
                if c == '"' {
                    let str = self.intern_str(result);
                    return Some(str);
                } else {
                    result.push(c);
                }
            }
            None
        } else {
            None
        }
    }

    pub fn read_quoted_symbol<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Ptr<F>> {
        let mut result = String::new();

        if let Some('|') = skip_whitespace_and_peek(chars) {
            chars.next();
            while let Some(&c) = chars.peek() {
                chars.next();
                // TODO: This does not handle any escaping, so symbols containing | cannot be read.
                if c == '|' {
                    let sym = self.intern_sym(result);
                    return Some(sym);
                } else {
                    result.push(c);
                }
            }
            None
        } else {
            None
        }
    }

    pub fn read_maybe_meta<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<(Ptr<F>, bool)> {
        if let Some(c) = skip_whitespace_and_peek(chars) {
            match c {
                '!' => {
                    chars.next();
                    if let Some(s) = self.read_string(chars) {
                        Some((s, true))
                    } else if let Some((e, is_meta)) = self.read_maybe_meta(chars) {
                        assert!(!is_meta);
                        Some((e, true))
                    } else {
                        None
                    }
                }
                _ => self.read_next(chars).map(|expr| (expr, false)),
            }
        } else {
            None
        }
    }

    pub fn read_next<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Ptr<F>> {
        while let Some(&c) = chars.peek() {
            if let Some(next_expr) = match c {
                '(' => self.read_list(chars),
                '0'..='9' => self.read_number(chars),
                ' ' | '\t' | '\n' | '\r' => {
                    // Skip whitespace.
                    chars.next();
                    continue;
                }
                '\'' => {
                    chars.next();
                    let quote = self.sym("quote");
                    let quoted = self.read_next(chars)?;
                    let inner = self.intern_list(&[quoted]);
                    Some(self.cons(quote, inner))
                }
                '\"' => self.read_string(chars),
                '|' => self.read_quoted_symbol(chars),
                '#' => self.read_pound(chars),
                ';' => {
                    chars.next();
                    if skip_line_comment(chars) {
                        continue;
                    } else {
                        None
                    }
                }
                x if is_symbol_char(&x, true) => self.read_symbol(chars),
                _ => {
                    panic!("bad input character: {}", c);
                }
            } {
                return Some(next_expr);
            }
        }
        None
    }

    // In this context, 'list' includes improper lists, i.e. dotted cons-pairs like (1 . 2).
    fn read_list<T: Iterator<Item = char>>(&mut self, chars: &mut Peekable<T>) -> Option<Ptr<F>> {
        if let Some(&c) = chars.peek() {
            match c {
                '(' => {
                    chars.next(); // Discard.
                    self.read_tail(chars)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    // Read the tail of a list.
    fn read_tail<T: Iterator<Item = char>>(&mut self, chars: &mut Peekable<T>) -> Option<Ptr<F>> {
        if let Some(c) = skip_whitespace_and_peek(chars) {
            match c {
                ')' => {
                    chars.next();
                    Some(self.nil())
                }
                '.' => {
                    chars.next();
                    let cdr = self.read_next(chars).unwrap();
                    let remaining_tail = self.read_tail(chars).unwrap();
                    assert!(remaining_tail.is_nil());

                    Some(cdr)
                }
                _ => {
                    let car = self.read_next(chars).unwrap();
                    let rest = self.read_tail(chars).unwrap();
                    Some(self.cons(car, rest))
                }
            }
        } else {
            panic!("premature end of input");
        }
    }

    fn read_number<T: Iterator<Item = char>>(&mut self, chars: &mut Peekable<T>) -> Option<Ptr<F>> {
        // As written, read_number assumes the next char is known to be a digit.
        // So it will never return None.
        let mut acc: u64 = 0;
        let ten = 10;

        if let Some(&c) = chars.peek() {
            if c == '0' {
                chars.next().unwrap();
                if let Some(&c) = chars.peek() {
                    if c.to_ascii_uppercase() == 'X' {
                        chars.next();
                        return self.read_hex_num(chars);
                    }
                }
            }
        }
        while let Some(&c) = chars.peek() {
            if is_digit_char(&c) {
                let digit_char = chars.next().unwrap();
                let digit = digit_char.to_digit(10).unwrap();
                let n: u64 = digit.into();

                if let Some(new) = acc.checked_mul(ten).and_then(|x| x.checked_add(n)) {
                    acc = new;
                } else {
                    // If acc * 10 + n would overflow, convert to F-sized accumulator and continue.
                    let scalar_acc = F::from(acc) * F::from(ten) + F::from(n);
                    return self.read_number_aux(scalar_acc, chars);
                }
            } else {
                break;
            }
        }
        Some(self.intern_num(acc))
    }

    fn read_number_aux<T: Iterator<Item = char>>(
        &mut self,
        mut acc: F,
        chars: &mut Peekable<T>,
    ) -> Option<Ptr<F>> {
        let zero = F::from(0);
        let ten = F::from(10);

        while let Some(&c) = chars.peek() {
            if is_digit_char(&c) {
                let digit_char = chars.next().unwrap();

                if acc != zero {
                    acc *= ten;
                }
                let digit = digit_char.to_digit(10).unwrap();
                let n: u64 = digit.into();
                let f: F = n.into();
                acc += f;
            } else {
                break;
            }
        }
        Some(self.intern_num(crate::num::Num::Scalar(acc)))
    }

    fn read_hex_num<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Ptr<F>> {
        let zero = F::from(0);
        let mut acc = zero;
        let sixteen = F::from(16);

        while let Some(&c) = chars.peek() {
            if is_hex_digit_char(&c) {
                let digit_char = chars.next().unwrap();

                if acc != zero {
                    acc *= sixteen;
                }
                let digit = digit_char.to_digit(16).unwrap();
                let n: u64 = digit.into();
                let f: F = n.into();
                acc += f;
            } else {
                break;
            }
        }
        Some(self.intern_num(crate::num::Num::Scalar(acc)))
    }

    pub(crate) fn read_symbol<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Ptr<F>> {
        let name = Self::read_unquoted_symbol_name(chars);
        Some(self.intern_sym(name))
    }

    pub(crate) fn read_unquoted_symbol_name<T: Iterator<Item = char>>(
        chars: &mut Peekable<T>,
    ) -> String {
        let mut name = String::new();
        let mut is_initial = true;
        while let Some(&c) = chars.peek() {
            if is_symbol_char(&c, is_initial) {
                let c = chars.next().unwrap();
                name.push(c);
            } else {
                break;
            }
            is_initial = false;
        }
        Self::convert_sym_case(&mut name);
        name
    }

    pub(crate) fn read_pound<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Ptr<F>> {
        chars.next().unwrap();
        if let Some(&c) = chars.peek() {
            match c {
                '\\' => {
                    chars.next();
                    if let Some(&c) = chars.peek() {
                        chars.next();
                        Some(c.into())
                    } else {
                        None
                    }
                }
                _ => None,
            }
        } else {
            None
        }
    }
}

fn is_symbol_char(c: &char, initial: bool) -> bool {
    match c {
        // FIXME: suppport more than just alpha.
        'a'..='z' | 'A'..='Z' | '+' | '-' | '*' | '/' | '=' | '<' | '>' | ':' | '_' => true,
        _ => {
            if initial {
                false
            } else {
                matches!(c, '0'..='9')
            }
        }
    }
}

fn is_digit_char(c: &char) -> bool {
    matches!(c, '0'..='9')
}

fn is_hex_digit_char(c: &char) -> bool {
    matches!(c, '0'..='9' | 'a'..='f' | 'A'..='F')
}

#[allow(dead_code)]
fn is_reserved_char(c: &char) -> bool {
    matches!(c, '(' | ')' | '.')
}

fn is_whitespace_char(c: &char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r')
}

fn is_comment_char(c: &char) -> bool {
    matches!(c, ';')
}

fn is_line_end_char(c: &char) -> bool {
    matches!(c, '\n' | '\r')
}

// Skips whitespace and comments, returning the next character, if any.
fn skip_whitespace_and_peek<T: Iterator<Item = char>>(chars: &mut Peekable<T>) -> Option<char> {
    while let Some(&c) = chars.peek() {
        if is_whitespace_char(&c) {
            chars.next();
        } else if is_comment_char(&c) {
            skip_line_comment(chars);
        } else {
            return Some(c);
        }
    }
    None
}

// Returns true if comment ends with a line end character.
// If false, this comment is unterminated and is the end of input.
fn skip_line_comment<T: Iterator<Item = char>>(chars: &mut Peekable<T>) -> bool {
    while let Some(&c) = chars.peek() {
        if !is_line_end_char(&c) {
            chars.next();
        } else {
            return true;
        }
    }
    false

    //chars.skip_while(|c| *c != '\n' && *c != '\r');
    //     }
    // };
}

#[cfg(test)]
mod test {
    use crate::writer::Write;
    use blstrs::Scalar as Fr;

    use super::*;

    #[test]
    fn read_sym() {
        let test = |input, expected: &str| {
            let mut store = Store::<Fr>::default();
            let ptr = &store.read(input).unwrap();
            let expr = store.fetch(ptr).unwrap();

            assert_eq!(expected, expr.as_sym_str().unwrap());
        };

        test("asdf", "ASDF");
        test("asdf ", "ASDF");
        test("asdf(", "ASDF");
        test(" asdf", "ASDF");
        test(" asdf ", "ASDF");
        test(
            "
asdf(", "ASDF",
        );
        test("foo-bar", "FOO-BAR");
        test("foo_bar", "FOO_BAR");

        test(
            "|A quoted symbol: α, β, ∧, ∨, ∑.|",
            "A quoted symbol: α, β, ∧, ∨, ∑.",
        );
    }

    #[test]
    fn read_nil() {
        let mut store = Store::<Fr>::default();
        let expr = store.read("nil").unwrap();
        assert!(expr.is_nil());
    }

    #[test]
    fn read_num() {
        let test = |input, expected: u64| {
            let mut store = Store::<Fr>::default();
            let expr = store.read(input).unwrap();
            let expected = store.intern_num(expected);
            assert!(store.ptr_eq(&expected, &expr));
        };
        test("123", 123);
        test("0987654321", 987654321);
        test("123)", 123);
        test("123 ", 123);
        test("123z", 123);
        test(" 123", 123);
        test(
            "
0987654321",
            987654321,
        );

        let test = |input, expected: Fr| {
            let mut store = Store::<Fr>::default();
            let expr = store.read(input).unwrap();
            let expected = store.intern_num(crate::num::Num::from_scalar(expected));
            assert!(store.ptr_eq(&expected, &expr));
        };
        test("0x10", Fr::from(16));
        test("0x22", Fr::from(34));
        test("0x0010", Fr::from(16));
        test("0x0022", Fr::from(34));

        test("0X10", Fr::from(16));
        test("0X22", Fr::from(34));

        test("0x000e", Fr::from(14));

        test(
            "0x000000000000000000000000000000000000000000000000000000000000000f",
            Fr::from(15),
        );

        test("0x000F", Fr::from(15));

        test(
            "0x000000000000000000000000000000000000000000000000000000000000000F",
            Fr::from(15),
        );

        {
            let x = 18446744073709551615;
            assert_eq!(u64::MAX, x);
            test("18446744073709551616", Fr::from(x) + Fr::from(1));
        }

        test("1230xa", Fr::from(1230));

        let test = |a, b| {
            let mut store = Store::<Fr>::default();
            let a_num = store.read(a).unwrap();
            let b_num = store.read(b).unwrap();
            dbg!(a_num.fmt_to_string(&store), b_num.fmt_to_string(&store));
            assert!(store.ptr_eq(&a_num, &b_num));
        };

        test("18446744073709551616", "0x10000000000000000");
        test("123456789123456789123", "0x6B14E9F9B0DF36A83");

        // > (- 0 1)
        // [3 iterations] => 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000
        // (format nil "~x" (mod (expt 2 256) (1+ #x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000)))
        // "1824B159ACC5056F998C4FEFECBC4FF55884B7FA0003480200000001FFFFFFFE"
        test(
            "0x10000000000000000000000000000000000000000000000000000000000000000",
            "0x1824B159ACC5056F998C4FEFECBC4FF55884B7FA0003480200000001FFFFFFFE",
        );
    }

    #[test]
    fn read_list() {
        let mut s = Store::<Fr>::default();
        let test = |store: &mut Store<Fr>, input, expected| {
            let expr = store.read(input).unwrap();
            assert_eq!(expected, &expr);
        };

        let a = s.num(123);
        let b = s.nil();
        let expected = s.cons(a, b);
        test(&mut s, "(123)", &expected);

        let a = s.num(321);
        let expected2 = s.cons(a, expected);
        test(&mut s, "(321 123)", &expected2);

        let a = s.sym("PUMPKIN");
        let expected3 = s.cons(a, expected2);
        test(&mut s, "(pumpkin 321 123)", &expected3);

        let expected4 = s.cons(expected, s.get_nil());
        test(&mut s, "((123))", &expected4);

        let (a, b) = (s.num(321), s.nil());
        let alt = s.cons(a, b);
        let expected5 = s.cons(alt, expected4);
        test(&mut s, "((321) (123))", &expected5);

        let expected6 = s.cons(expected2, expected3);
        test(&mut s, "((321 123) pumpkin 321 123)", &expected6);

        let (a, b) = (s.num(1), s.num(2));
        let pair = s.cons(a, b);
        let list = [pair, s.num(3)];
        let expected7 = s.intern_list(&list);
        test(&mut s, "((1 . 2) 3)", &expected7);
    }

    #[test]
    fn read_improper_list() {
        let mut s = Store::<Fr>::default();
        let test = |store: &mut Store<Fr>, input, expected| {
            let expr = store.read(input).unwrap();
            assert_eq!(expected, &expr);
        };

        let (a, b) = (s.num(123), s.num(321));
        let expected = s.cons(a, b);
        test(&mut s, "(123 . 321)", &expected);

        assert_eq!(s.read("(123 321)"), s.read("(123 . ( 321 ))"))
    }
    #[test]
    fn read_print_expr() {
        let mut s = Store::<Fr>::default();
        let test = |store: &mut Store<Fr>, input| {
            let expr = store.read(input).unwrap();
            let output = expr.fmt_to_string(store);
            assert_eq!(input, output);
        };

        test(&mut s, "A");
        test(&mut s, "(A . B)");
        test(&mut s, "(A B C)");
        test(&mut s, "(A (B) C)");
        test(&mut s, "(A (B . C) (D E (F)) G)");
        // test(&mut s, "'A");
        // test(&mut s, "'(A B)");
    }

    #[test]
    fn read_maybe_meta() {
        let mut s = Store::<Fr>::default();
        let test =
            |store: &mut Store<Fr>, input: &str, expected_ptr: Ptr<Fr>, expected_meta: bool| {
                let mut chars = input.chars().peekable();

                let (ptr, meta) = store.read_maybe_meta(&mut chars).unwrap();
                {
                    assert_eq!(expected_ptr, ptr);
                    assert_eq!(expected_meta, meta);
                };
            };

        let num = s.num(123);
        test(&mut s, "123", num, false);

        {
            let list = [s.num(123), s.num(321)];
            let l = s.list(&list);
            test(&mut s, " (123 321)", l, false);
        }
        {
            let list = [s.num(123), s.num(321)];
            let l = s.list(&list);
            test(&mut s, " !(123 321)", l, true);
        }
        {
            let list = [s.num(123), s.num(321)];
            let l = s.list(&list);
            test(&mut s, " ! (123 321)", l, true);
        }
        {
            let sym = s.sym("asdf");
            test(&mut s, "!asdf", sym, true);
        }
        {
            let sym = s.sym(":assert");
            let l = s.list(&[sym]);
            test(&mut s, "!(:assert)", l, true);
        }
        {
            let sym = s.sym("asdf");
            test(
                &mut s,
                ";; comment
!asdf",
                sym,
                true,
            );
        }
    }
    #[test]
    fn is_keyword() {
        let mut s = Store::<Fr>::default();
        let kw = s.sym(":UIOP");
        let not_kw = s.sym("UIOP");

        assert!(s.fetch(&kw).unwrap().is_keyword_sym());
        assert!(!s.fetch(&not_kw).unwrap().is_keyword_sym());
    }

    #[test]
    fn read_string() {
        let mut s = Store::<Fr>::default();

        let test =
            |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>, expr: Option<&str>| {
                let maybe_string = store.read_string(&mut input.chars().peekable());
                assert_eq!(expected, maybe_string);
                if let Some(ptr) = maybe_string {
                    let res = store
                        .fetch(&ptr)
                        .unwrap_or_else(|| panic!("failed to fetch: {:?}", input));
                    assert_eq!(res.as_str(), expr);
                }
            };

        let str = s.intern_str("asdf");
        test(&mut s, "\"asdf\"", Some(str), Some("asdf"));
        test(&mut s, "\"asdf", None, None);
        test(&mut s, "asdf", None, None);

        {
            let input = "\"foo/bar/baz\"";
            let ptr = s.read_string(&mut input.chars().peekable()).unwrap();
            let res = s
                .fetch(&ptr)
                .unwrap_or_else(|| panic!("failed to fetch: {:?}", input));
            assert_eq!(res.as_str().unwrap(), "foo/bar/baz");
        }
    }

    #[test]
    fn read_write_char() {
        let s = &mut Store::<Fr>::default();

        let a = 'a';
        let char = s.get_char(a);
        let input = r#"#\a"#;
        let ptr = s.read(input).unwrap();
        let res = s.fetch(&ptr).unwrap();
        match res {
            crate::store::Expression::Char(c) => assert_eq!(a, c),
            _ => panic!("not a Char"),
        };
        let printed = res.fmt_to_string(s);

        assert_eq!(char, ptr);
        assert_eq!(input, printed);
    }

    #[test]
    fn read_with_comments() {
        let mut s = Store::<Fr>::default();

        let test = |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>| {
            let res = store.read(input);
            assert_eq!(expected, res);
        };

        let num = s.num(321);
        test(
            &mut s,
            ";123
321",
            Some(num),
        );
    }
}
