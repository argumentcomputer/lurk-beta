use std::iter::Peekable;

use ff::PrimeField;

use crate::store::{Ptr, Store};

impl<F: PrimeField> Store<F> {
    pub fn read(&mut self, input: &str) -> Option<Ptr<F>> {
        let mut chars = input.chars().peekable();

        self.read_next(&mut chars)
    }

    // For now, this is only used for REPL/CLI commands.
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
        let mut acc = 0;
        let ten = 10;

        while let Some(&c) = chars.peek() {
            if is_digit_char(&c) {
                if acc != 0 {
                    acc *= ten;
                }
                let digit_char = chars.next().unwrap();
                let digit = digit_char.to_digit(10).unwrap();
                let n: u64 = digit.into();
                acc += n;
            } else {
                break;
            }
        }
        Some(self.intern_num(acc))
    }

    pub(crate) fn read_symbol<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Ptr<F>> {
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
        Some(self.intern_sym(name))
    }
}

fn is_symbol_char(c: &char, initial: bool) -> bool {
    match c {
        // FIXME: suppport more than just alpha.
        'a'..='z' | 'A'..='Z' | '+' | '-' | '*' | '/' | '=' | ':' => true,
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
            let expr = store.fetch(&ptr).unwrap();

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
            assert_eq!(store.intern_num(expected), expr);
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
    }

    #[test]
    fn read_list() {
        let mut store = Store::<Fr>::default();
        let test = |store: &mut Store<Fr>, input, expected| {
            let expr = store.read(input).unwrap();
            assert_eq!(expected, &expr);
        };

        let a = store.num(123);
        let b = store.nil();
        let expected = store.intern_cons(a, b);
        test(&mut store, "(123)", &expected);

        let a = store.num(321);
        let expected2 = store.intern_cons(a, expected);
        test(&mut store, "(321 123)", &expected2);

        let a = store.sym("PUMPKIN");
        let expected3 = store.intern_cons(a, expected2);
        test(&mut store, "(pumpkin 321 123)", &expected3);

        let expected4 = store.intern_cons(expected, store.get_nil());
        test(&mut store, "((123))", &expected4);

        let (a, b) = (store.num(321), store.nil());
        let alt = store.intern_cons(a, b);
        let expected5 = store.intern_cons(alt, expected4);
        test(&mut store, "((321) (123))", &expected5);

        let expected6 = store.intern_cons(expected2, expected3);
        test(&mut store, "((321 123) pumpkin 321 123)", &expected6);

        let (a, b) = (store.num(1), store.num(2));
        let pair = store.intern_cons(a, b);
        let list = [pair, store.num(3)];
        let expected7 = store.intern_list(&list);
        test(&mut store, "((1 . 2) 3)", &expected7);
    }

    #[test]
    fn read_improper_list() {
        let mut store = Store::<Fr>::default();
        let test = |store: &mut Store<Fr>, input, expected| {
            let expr = store.read(input).unwrap();
            assert_eq!(expected, &expr);
        };

        let (a, b) = (store.num(123), store.num(321));
        let expected = store.intern_cons(a, b);
        test(&mut store, "(123 . 321)", &expected);

        assert_eq!(store.read("(123 321)"), store.read("(123 . ( 321 ))"))
    }
    #[test]
    fn read_print_expr() {
        let mut store = Store::<Fr>::default();
        let test = |store: &mut Store<Fr>, input| {
            let expr = store.read(input).unwrap();
            let output = expr.fmt_to_string(store);
            assert_eq!(input, output);
        };

        test(&mut store, "A");
        test(&mut store, "(A . B)");
        test(&mut store, "(A B C)");
        test(&mut store, "(A (B) C)");
        test(&mut store, "(A (B . C) (D E (F)) G)");
        // test(&mut store, "'A");
        // test(&mut store, "'(A B)");
    }

    #[test]
    fn read_maybe_meta() {
        let mut store = Store::<Fr>::default();
        let test =
            |store: &mut Store<Fr>, input: &str, expected_ptr: Ptr<Fr>, expected_meta: bool| {
                let mut chars = input.chars().peekable();

                match store.read_maybe_meta(&mut chars).unwrap() {
                    (ptr, meta) => {
                        assert_eq!(expected_ptr, ptr);
                        assert_eq!(expected_meta, meta);
                    }
                };
            };

        let num = store.num(123);
        test(&mut store, "123", num, false);

        {
            let list = [store.num(123), store.num(321)];
            let l = store.intern_list(&list);
            test(&mut store, " (123 321)", l, false);
        }
        {
            let list = [store.num(123), store.num(321)];
            let l = store.intern_list(&list);
            test(&mut store, " !(123 321)", l, true);
        }
        {
            let list = [store.num(123), store.num(321)];
            let l = store.intern_list(&list);
            test(&mut store, " ! (123 321)", l, true);
        }
        {
            let s = store.sym("asdf");
            test(&mut store, "!asdf", s, true);
        }
        {
            let s = store.sym(":assert");
            let l = store.intern_list(&[s]);
            test(&mut store, "!(:assert)", l, true);
        }
        {
            let s = store.sym("asdf");
            test(
                &mut store,
                ";; comment
!asdf",
                s,
                true,
            );
        }
    }
    #[test]
    fn is_keyword() {
        let mut store = Store::<Fr>::default();
        let kw = store.sym(":UIOP");
        let not_kw = store.sym("UIOP");

        assert!(store.fetch(&kw).unwrap().is_keyword_sym());
        assert!(!store.fetch(&not_kw).unwrap().is_keyword_sym());
    }

    #[test]
    fn read_string() {
        let mut store = Store::<Fr>::default();

        let test =
            |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>, expr: Option<&str>| {
                let maybe_string = store.read_string(&mut input.chars().peekable());
                assert_eq!(expected, maybe_string);
                if let Some(ptr) = maybe_string {
                    let res = store
                        .fetch(&ptr)
                        .expect(&format!("failed to fetch: {:?}", input));
                    assert_eq!(res.as_str(), expr);
                }
            };

        let s = store.intern_str("asdf");
        test(&mut store, "\"asdf\"", Some(s), Some("asdf"));
        test(&mut store, "\"asdf", None, None);
        test(&mut store, "asdf", None, None);

        {
            let input = "\"foo/bar/baz\"";
            let ptr = store.read_string(&mut input.chars().peekable()).unwrap();
            let res = store
                .fetch(&ptr)
                .expect(&format!("failed to fetch: {:?}", input));
            assert_eq!(res.as_str().unwrap(), "foo/bar/baz");
        }
    }

    #[test]
    fn read_with_comments() {
        let mut store = Store::<Fr>::default();

        let test = |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>| {
            let res = store.read(input);
            assert_eq!(expected, res);
        };

        let num = store.num(321);
        test(
            &mut store,
            ";123
321",
            Some(num),
        );
    }
}
