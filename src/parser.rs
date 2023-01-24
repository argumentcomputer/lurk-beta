use peekmore::{PeekMore, PeekMoreIterator};

use crate::field::LurkField;
use crate::package::Package;
use crate::store::{Ptr, Store};
use crate::sym::Sym;
use crate::uint::UInt;
use thiserror;

#[derive(thiserror::Error, Debug, Clone)]
pub enum Error {
    #[error("Empty input error")]
    NoInput,
    #[error("Syntax error: {0}")]
    Syntax(String),
}

impl<F: LurkField> Store<F> {
    pub fn read(&mut self, input: &str) -> Result<Ptr<F>, Error> {
        let package = Default::default();

        self.read_in_package(input, &package)
    }

    pub fn read_in_package(&mut self, input: &str, package: &Package) -> Result<Ptr<F>, Error> {
        let mut chars = input.chars().peekmore();
        if skip_whitespace_and_peek(&mut chars).is_some() {
            self.read_next(&mut chars, package)
        } else {
            Err(Error::NoInput)
        }
    }

    pub fn read_string<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
    ) -> Result<Ptr<F>, Error> {
        let mut result = String::new();

        if let Some('"') = skip_whitespace_and_peek(chars) {
            chars.next();
            while let Some(&c) = chars.peek() {
                chars.next();
                if c == '\\' {
                    if let Some(&c) = chars.peek() {
                        result.push(c);
                        chars.next();
                    }
                } else if c == '"' {
                    let str = self.intern_str(result);
                    return Ok(str);
                } else {
                    result.push(c);
                }
            }
            Err(Error::Syntax("Could not read string".into()))
        } else {
            Err(Error::Syntax("Could not read string".into()))
        }
    }

    pub fn read_maybe_meta<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
        package: &Package,
    ) -> Result<(Ptr<F>, bool), Error> {
        if let Some(c) = skip_whitespace_and_peek(chars) {
            match c {
                '!' => {
                    chars.next();
                    if let Ok(s) = self.read_string(chars) {
                        Ok((s, true))
                    } else if let Ok((e, is_meta)) = self.read_maybe_meta(chars, package) {
                        assert!(!is_meta);
                        Ok((e, true))
                    } else {
                        Err(Error::Syntax("Could not read meta".into()))
                    }
                }
                _ => self.read_next(chars, package).map(|expr| (expr, false)),
            }
        } else {
            Err(Error::NoInput)
        }
    }

    pub fn read_next<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
        package: &Package,
    ) -> Result<Ptr<F>, Error> {
        while let Some(&c) = chars.peek() {
            return match c {
                '(' => self.read_list(chars, package),
                '0'..='9' => self.read_number(chars, true),
                ' ' | '\t' | '\n' | '\r' => {
                    // Skip whitespace.
                    chars.next();
                    continue;
                }
                '\'' => {
                    chars.next();
                    let quote = self.lurk_sym("quote");
                    let quoted = self.read_next(chars, package)?;
                    let inner = self.intern_list(&[quoted]);
                    Ok(self.cons(quote, inner))
                }
                '\"' => self.read_string(chars),
                '|' => self.read_symbol(chars, package),
                '#' => self.read_pound(chars),
                ';' => {
                    chars.next();
                    if skip_line_comment(chars) {
                        continue;
                    } else {
                        Err(Error::Syntax("Bad comment syntax".into()))
                    }
                }
                '-' => self.read_negative_number_or_symbol(chars, package),
                x if is_symbol_char(&x, true) => self.read_symbol(chars, package),
                _ => Err(Error::Syntax(format!("bad input character: {c}"))),
            };
        }
        Err(Error::Syntax("Could not read input".into()))
    }

    // In this context, 'list' includes improper lists, i.e. dotted cons-pairs like (1 . 2).
    fn read_list<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
        package: &Package,
    ) -> Result<Ptr<F>, Error> {
        if let Some(&c) = chars.peek() {
            match c {
                '(' => {
                    chars.next(); // Discard.
                    self.read_tail(true, chars, package)
                }
                _ => Err(Error::Syntax("Could not read list".into())),
            }
        } else {
            Err(Error::Syntax("Could not read list".into()))
        }
    }

    // Read the tail of a list.
    fn read_tail<T: Iterator<Item = char>>(
        &mut self,
        first: bool,
        chars: &mut PeekMoreIterator<T>,
        package: &Package,
    ) -> Result<Ptr<F>, Error> {
        if let Some(c) = skip_whitespace_and_peek(chars) {
            match c {
                ')' => {
                    chars.next();
                    Ok(self.nil())
                }
                '.' if !first => {
                    if is_symbol_char(chars.peek_nth(1).unwrap(), false) {
                        self.read_tail(true, chars, package)
                    } else {
                        chars.next();
                        let cdr = self.read_next(chars, package)?;
                        let remaining_tail = self.read_tail(false, chars, package)?;
                        assert!(remaining_tail.is_nil());

                        Ok(cdr)
                    }
                }
                _ => {
                    let res = self.read_next(chars, package);
                    match res {
                        Err(Error::NoInput) if c == '.' => {
                            Err(Error::Syntax("nothing appears before . in list.".into()))?;
                        }
                        _ => (),
                    };
                    let car = res?;
                    let rest = self.read_tail(false, chars, package)?;
                    Ok(self.cons(car, rest))
                }
            }
        } else {
            Err(Error::Syntax("premature end of input".into()))
        }
    }

    /// Reads a negative number or a symbol beginning with '-'.
    fn read_negative_number_or_symbol<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
        package: &Package,
    ) -> Result<Ptr<F>, Error> {
        if let Some(&c) = chars.peek() {
            match c {
                '-' => {
                    if let Some(&c) = chars.peek_nth(1) {
                        match c {
                            '0'..='9' => {
                                chars.next();
                                let n = self.read_number(chars, true)?;
                                let num: &crate::num::Num<F> =
                                    self.fetch_num(&n).ok_or_else(|| {
                                        Error::Syntax("Could not fetch number".into())
                                    })?;
                                let mut tmp = crate::num::Num::<F>::U64(0);
                                tmp -= *num;
                                Ok(self.intern_num(tmp))
                            }
                            _ => {
                                if let Some(sym) = read_sym(chars)? {
                                    Ok(self.intern_sym_in_package(sym, package))
                                } else {
                                    Ok(self.intern_sym_in_package(Sym::new("-".into()), package))
                                }
                            }
                        }
                    } else {
                        Ok(self.intern_sym_in_package(Sym::new("-".into()), package))
                    }
                }
                _ => Err(Error::Syntax("Could not read nagative number".into())),
            }
        } else {
            Err(Error::Syntax("Could not read negative number".into()))
        }
    }

    fn read_number<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
        maybe_fraction: bool,
    ) -> Result<Ptr<F>, Error> {
        // As written, read_number assumes the next char is known to be a digit.
        // So it will never return None.
        let mut acc: u64 = 0;
        let ten = 10;

        if let Some(&c) = chars.peek() {
            match c {
                '0' => {
                    chars.next().unwrap();
                    if let Some(&c) = chars.peek() {
                        if c.to_ascii_uppercase() == 'X' {
                            chars.next();
                            return self.read_hex_num(chars, maybe_fraction);
                        }
                    }
                }
                '1'..='9' => (),
                _ => return Err(Error::Syntax("Could not read number".into())),
            }
        };
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
                    return self.read_number_aux(scalar_acc, chars, maybe_fraction);
                }
            } else if maybe_fraction && c == '/' {
                if let Some(c2) = chars.peek_nth(1) {
                    if c2.is_ascii_digit() {
                        let mut tmp = crate::num::Num::U64(acc);
                        chars.next();
                        if let Ok(denominator) = self.read_number(chars, false) {
                            let d = self
                                .fetch_num(&denominator)
                                .ok_or_else(|| Error::Syntax("Could not fetch number".into()))?;
                            tmp /= *d;
                        };
                        return Ok(self.intern_num(tmp));
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        match self.read_number_suffix(chars) {
            Some(UInt::U64(_)) => Ok(self.get_u64(acc)),
            None => Ok(self.intern_num(acc)),
        }
    }

    fn read_number_aux<T: Iterator<Item = char>>(
        &mut self,
        mut acc: F,
        chars: &mut PeekMoreIterator<T>,
        maybe_fraction: bool,
    ) -> Result<Ptr<F>, Error> {
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
            } else if maybe_fraction && c == '/' {
                if let Some(c2) = chars.peek_nth(1) {
                    if c2.is_ascii_digit() {
                        let mut tmp = crate::num::Num::Scalar(acc);
                        chars.next();
                        if let Ok(denominator) = self.read_number(chars, false) {
                            let d = self
                                .fetch_num(&denominator)
                                .ok_or_else(|| Error::Syntax("Could not fetch number".into()))?;
                            tmp /= *d;
                        };
                        return Ok(self.intern_num(tmp));
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        match self.read_number_suffix(chars) {
            Some(UInt::U64(_)) => Ok(self.get_u64(
                acc.to_u64()
                    .ok_or_else(|| Error::Syntax("Number too large for u64.".into()))?,
            )),
            None => Ok(self.intern_num(crate::num::Num::Scalar(acc))),
        }
    }

    fn read_hex_num<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
        maybe_fraction: bool,
    ) -> Result<Ptr<F>, Error> {
        // NOTE: `read_hex_num` always interns `Num::Scalar`s,
        // unlike `read_number`, which may return a `Num::U64`.
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
            } else if maybe_fraction && c == '/' {
                if let Some(c2) = chars.peek_nth(1) {
                    if is_hex_digit_char(c2) {
                        let mut tmp = crate::num::Num::Scalar(acc);
                        chars.next();
                        if let Ok(denominator) = self.read_number(chars, false) {
                            let d = self
                                .fetch_num(&denominator)
                                .ok_or_else(|| Error::Syntax("Could not fetch number".into()))?;
                            tmp /= *d;
                        };
                        return Ok(self.intern_num(tmp));
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        match self.read_number_suffix(chars) {
            Some(UInt::U64(_)) => Ok(self.get_u64(
                acc.to_u64()
                    .ok_or_else(|| Error::Syntax("Number too large for u64.".into()))?,
            )),
            None => Ok(self.intern_num(crate::num::Num::Scalar(acc))),
        }
    }

    /// If a number suffix can be read, return a UInt, specifying that suffix. Otherwise return None.
    /// Initially, only `u64` and `U64` are valid suffixes.
    fn read_number_suffix<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
    ) -> Option<UInt> {
        if let Some(c) = chars.peek() {
            if matches!(c, 'U' | 'u') {
                if let Some(c2) = chars.peek_nth(1) {
                    if *c2 == '6' {
                        if let Some(c3) = chars.peek_nth(2) {
                            if *c3 == '4' {
                                chars.next();
                                chars.next();
                                chars.next();
                                Some(UInt::U64(0))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    pub(crate) fn intern_sym_in_package(&mut self, sym: Sym, package: &Package) -> Ptr<F> {
        if sym.is_toplevel() {
            self.intern_sym(&sym)
        } else {
            let parent_sym = package.name();
            let new_sym = parent_sym.extend(sym.path());

            self.intern_sym(&new_sym)
        }
    }

    pub(crate) fn read_symbol<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
        package: &Package,
    ) -> Result<Ptr<F>, Error> {
        if let Some(sym) = read_sym(chars)? {
            if sym.is_root() {
                // The root symbol cannot (currently) be read. A naked dot is an error except in the context of a list tail.
                Err(Error::Syntax("Misplaced dot".into()))
            } else {
                Ok(self.intern_sym_in_package(sym, package))
            }
        } else {
            Err(Error::NoInput)
        }
    }

    pub(crate) fn read_pound<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut PeekMoreIterator<T>,
    ) -> Result<Ptr<F>, Error> {
        chars.next().unwrap();
        if let Some(&c) = chars.peek() {
            match c {
                '\\' => {
                    chars.next();
                    if let Some(&c) = chars.peek() {
                        chars.next();
                        Ok(c.into())
                    } else {
                        Err(Error::Syntax("Could not read character".into()))
                    }
                }
                _ => Err(Error::Syntax("Could not read character".into())),
            }
        } else {
            Err(Error::Syntax("Could not read character".into()))
        }
    }
}

// Read a symbol's canonical full name by first reading the path,
// then constructing the canonical full name from the resulting path.
fn read_sym<T: Iterator<Item = char>>(
    chars: &mut PeekMoreIterator<T>,
) -> Result<Option<Sym>, Error> {
    let (is_keyword, path) = read_symbol_path(chars)?;

    if path.is_empty() {
        Ok(None)
    } else {
        let sym = Sym::new_from_path(is_keyword, path);
        Ok(Some(sym))
    }
}

pub fn read_symbol_path<T: Iterator<Item = char>>(
    chars: &mut PeekMoreIterator<T>,
) -> Result<(bool, Vec<String>), Error> {
    let mut path = Vec::new();

    let is_keyword = if chars.peek() == Some(&KEYWORD_MARKER) {
        chars.next();
        path.push("".into());
        true
    } else {
        false
    };

    if chars.peek() == Some(&SYM_MARKER) {
        chars.next();
        path.push("".into());
    };

    while let Ok(name) = read_symbol_name(chars) {
        path.push(name);

        if chars.peek() == Some(&SYM_MARKER) {
            chars.next();
            continue;
        } else {
            break;
        }
    }

    Ok((is_keyword, path))
}

fn read_symbol_name<T: Iterator<Item = char>>(
    chars: &mut PeekMoreIterator<T>,
) -> Result<String, Error> {
    read_unquoted_symbol_name(chars).or_else(|_| read_quoted_symbol_name(chars))
}

fn read_quoted_symbol_name<T: Iterator<Item = char>>(
    chars: &mut PeekMoreIterator<T>,
) -> Result<String, Error> {
    let mut result = String::new();

    if let Some('|') = chars.peek() {
        chars.next();
        while let Some(&c) = chars.peek() {
            chars.next();
            if c == '\\' {
                if let Some(&c) = chars.peek() {
                    result.push(c);
                    chars.next();
                }
            } else if c == '|' {
                return Ok(result);
            } else {
                result.push(c);
            }
        }
        Err(Error::Syntax("Could not read quoted symbol".into()))
    } else {
        Err(Error::Syntax(
            "End of input when trying to read quoted symbol".into(),
        ))
    }
}

pub(crate) fn convert_sym_case(raw_name: &mut str) {
    // In the future, we could support optional alternate case conventions,
    // so all case conversion should be performed here.
    raw_name.make_ascii_uppercase();
}

pub(crate) fn read_unquoted_symbol_name<T: Iterator<Item = char>>(
    chars: &mut PeekMoreIterator<T>,
) -> Result<String, Error> {
    let mut name = String::new();
    let mut is_initial = true;

    if let Some(c) = chars.peek() {
        if is_symbol_char(c, true) {
            while let Some(&c) = chars.peek() {
                if is_symbol_char(&c, is_initial) {
                    let c = chars.next().unwrap();
                    name.push(c);
                } else {
                    break;
                }
                is_initial = false;
            }
            convert_sym_case(&mut name);
            Ok(name)
        } else {
            Err(Error::Syntax("Could not read unquoted symbol".into()))
        }
    } else {
        Err(Error::Syntax(
            "End of input when trying to read unquoted symbol".into(),
        ))
    }
}

pub(crate) fn maybe_quote_symbol_name_string(symbol_name: &str) -> Result<String, std::fmt::Error> {
    if symbol_name.is_empty() {
        return Ok("||".into());
    }
    let contains_dot = symbol_name.contains(SYM_SEPARATOR);
    let mut chars = symbol_name.chars().peekmore();

    let quote_name = || {
        use std::fmt::Write;
        let mut out = String::new();
        write!(out, "|")?;

        for c in symbol_name.chars() {
            if c == '|' {
                write!(out, "\\{c}")?;
            } else {
                write!(out, "{c}")?;
            }
        }

        write!(out, "|")?;

        Ok(out)
    };

    if let Ok(unquoted) = read_unquoted_symbol_name(&mut chars) {
        if !contains_dot && unquoted == symbol_name {
            Ok(symbol_name.into())
        } else {
            quote_name()
        }
    } else {
        quote_name()
    }
}

pub const KEYWORD_MARKER: char = ':';
pub const SYM_SEPARATOR: &str = ".";
pub const SYM_MARKER: char = '.';

pub fn names_keyword(name: &str) -> (bool, &str) {
    let names_keyword = name.starts_with(KEYWORD_MARKER);
    let names_sym = name.starts_with(SYM_MARKER);

    if name.is_empty() {
        return (false, "");
    }

    // must only be called on a full name.
    assert!(names_sym || names_keyword);

    (names_keyword, &name[1..])
}

fn is_symbol_char(c: &char, initial: bool) -> bool {
    match c {
        c if is_initial_symbol_marker(c) => initial,
        'a'..='z' | 'A'..='Z' | '+' | '-' | '*' | '/' | '%' | '=' | '<' | '>' | '_' | '?' => true,
        _ => {
            if initial {
                false
            } else {
                c.is_ascii_digit()
            }
        }
    }
}

fn is_initial_symbol_marker(c: &char) -> bool {
    matches!(c, &SYM_MARKER | &KEYWORD_MARKER)
}

fn is_digit_char(c: &char) -> bool {
    c.is_ascii_digit()
}

fn is_hex_digit_char(c: &char) -> bool {
    matches!(c, '0'..='9' | 'a'..='f' | 'A'..='F')
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
fn skip_whitespace_and_peek<T: Iterator<Item = char>>(
    chars: &mut PeekMoreIterator<T>,
) -> Option<char> {
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
fn skip_line_comment<T: Iterator<Item = char>>(chars: &mut PeekMoreIterator<T>) -> bool {
    while let Some(&c) = chars.peek() {
        if !is_line_end_char(&c) {
            chars.next();
        } else {
            return true;
        }
    }
    false
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
            dbg!(&expected, &expr.as_sym_str());
            assert_eq!(expr.as_sym_str().unwrap(), expected);
        };

        test(".lurk.+", ".LURK.+");
        test(".lurk.-", ".LURK.-");
        test("-", ".LURK.-");
        test("-xxx", ".LURK.-XXX");
        test("asdf", ".LURK.ASDF");
        test("asdf ", ".LURK.ASDF");
        test("asdf(", ".LURK.ASDF");
        test(" asdf", ".LURK.ASDF");
        test(" asdf ", ".LURK.ASDF");
        test(
            "
        asdf(",
            ".LURK.ASDF",
        );
        test("foo-bar", ".LURK.FOO-BAR");
        test("foo_bar", ".LURK.FOO_BAR");

        test("|foo_BAR|", ".LURK.|foo_BAR|");

        test(":asdf", ":ASDF");
        test(":asdf.fdsa", ":ASDF.FDSA");
        test("asdf.fdsa", ".LURK.ASDF.FDSA");

        test(
            "|A quoted symbol: α, β, ∧, ∨, ∑|",
            ".LURK.|A quoted symbol: α, β, ∧, ∨, ∑|",
        );
        test("|UNNECESSARY-QUOTING|", ".LURK.UNNECESSARY-QUOTING");
        test(
            "|A quoted symbol with a dot.|",
            ".LURK.|A quoted symbol with a dot.|",
        );
        test(
            r#"|Symbol with \|escaped pipes\| contained|"#,
            r#".LURK.|Symbol with \|escaped pipes\| contained|"#,
        );

        test("|asdf|.fdsa", ".LURK.|asdf|.FDSA");
        test("|ASDF|.fdsa", ".LURK.ASDF.FDSA");
        test("|ASDF.FDSA|.xxx", ".LURK.|ASDF.FDSA|.XXX");
        test("|ASDF.fdsa|", ".LURK.|ASDF.fdsa|");
        test("|ASDF.FDSA|", ".LURK.|ASDF.FDSA|");

        // TODO: Test that this is an error: "asdf:fdsa"
    }

    #[test]
    fn test_sym_path() {
        let test = |input, expected: Vec<&str>| {
            let mut store = Store::<Fr>::default();

            let ptr = &store.read(input).unwrap();
            let expr = store.fetch(ptr).unwrap();
            let sym = expr.as_sym().unwrap();

            assert_eq!(sym.path(), &expected);
        };

        test("asdf", vec!["", "LURK", "ASDF"]);
        test("asdf.fdsa", vec!["", "LURK", "ASDF", "FDSA"]);

        test(".asdf", vec!["", "ASDF"]);
        test(".asdf.fdsa", vec!["", "ASDF", "FDSA"]);
        test(".|APPLE.ORANGE|.pear", vec!["", "APPLE.ORANGE", "PEAR"]);
        test(".|asdf|.fdsa", vec!["", "asdf", "FDSA"]);

        test(".asdf.|fdsa|", vec!["", "ASDF", "fdsa"]);

        test(":asdf", vec!["", "ASDF"]);
        test(":asdf.|fdsa|", vec!["", "ASDF", "fdsa"]);

        test(".||", vec!["", ""]);
        test(".||.||", vec!["", "", ""]);
        test(":||", vec!["", ""]);
        test(":||.||", vec!["", "", ""]);
        test(".asdf.||.fdsa.||", vec!["", "ASDF", "", "FDSA", ""]);
    }

    #[test]
    fn symbol_in_list() {
        let mut store = Store::<Fr>::default();
        let expr = store.read("'(+)").unwrap();
        let expr2 = store.read("'(.lurk.+)").unwrap();

        assert!(store.ptr_eq(&expr, &expr2).unwrap());
    }

    #[test]
    fn naked_dot_in_list() {
        let mut store = Store::<Fr>::default();

        let expected_error = match store.read("(.)").err().unwrap() {
            Error::Syntax(s) => s == *"Misplaced dot",
            _ => false,
        };

        assert!(expected_error);
    }

    #[test]
    fn absolute_symbol_in_list() {
        let mut store = Store::<Fr>::default();

        let expr = store.read("(a .b)").unwrap();
        let expr2 = store.read("(.b)").unwrap();
        let a = store.read("a").unwrap();
        let b = store.read(".b").unwrap();
        let nil = store.nil();

        let b_list = store.cons(b, nil);
        let a_b_list = store.cons(a, b_list);

        assert!(store.ptr_eq(&a_b_list, &expr).unwrap());
        assert!(store.ptr_eq(&b_list, &expr2).unwrap());
    }

    #[test]
    fn naked_dot() {
        let mut store = Store::<Fr>::default();

        let expected_error = match store.read(".").err().unwrap() {
            Error::Syntax(s) => s == *"Misplaced dot",
            _ => false,
        };

        assert!(expected_error);
    }

    #[test]
    fn list_tail() {
        let mut store = Store::<Fr>::default();
        let expr = store.read("'(+)").unwrap();
        let expr2 = store.read("'(.lurk.+)").unwrap();

        assert!(store.ptr_eq(&expr, &expr2).unwrap());
    }

    #[test]
    fn read_nil() {
        let mut store = Store::<Fr>::default();
        let expr = store.read(".lurk.nil").unwrap();
        let expr2 = store.read("nil").unwrap();
        assert!(expr.is_nil());
        assert!(expr2.is_nil());
    }

    #[test]
    fn read_num() {
        let test = |input, expected: u64| {
            let mut store = Store::<Fr>::default();
            let expr = store.read(input).unwrap();
            let expected = store.intern_num(expected);
            assert!(store.ptr_eq(&expected, &expr).unwrap());
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
            assert!(store.ptr_eq(&expected, &expr).unwrap());
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
            assert!(store.ptr_eq(&a_num, &b_num).unwrap());
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

        test(
            "-1",
            "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000",
        );
        test(
            "1/2",
            "0x39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff80000001",
        );
        test(
            "-1/2",
            "0x39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff80000000",
        );
        test("0xe/2", "7");
        test("-0xf/2", "-15/2");
    }

    #[test]
    fn read_u64() {
        let test = |input, expected: u64| {
            let mut store = Store::<Fr>::default();
            let expr = store.read(input).unwrap();
            let expected = store.get_u64(expected);
            assert!(store.ptr_eq(&expected, &expr).unwrap());
        };

        test("123u64", 123);
        test("0xffu64", 255);
        test("123U64", 123);
        test("0XFFU64", 255);

        // This is the largest U64.
        test("0xffffffffffffffffu64", 18446744073709551615);
    }

    #[test]
    fn read_u64_overflows() {
        let test = |input| {
            let mut store = Store::<Fr>::default();
            let expr = store.read(input);
            assert!(expr.is_err());
        };

        test("0xffffffffffffffffffu64");
        test("999999999999999999999999999999999999u64");
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

        let a = s.sym("pumpkin");
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

        assert_eq!(
            s.read("(123 321)").unwrap(),
            s.read("(123 . ( 321 ))").unwrap()
        )
    }
    #[test]
    fn read_print_expr() {
        let mut s = Store::<Fr>::default();
        let test = |store: &mut Store<Fr>, input| {
            let expr = store.read(input).unwrap();
            let output = expr.fmt_to_string(store);
            assert_eq!(input, output);
        };

        test(&mut s, "|α|");
        test(&mut s, "A");
        test(&mut s, "(A . B)");
        test(&mut s, "(A B C)");
        test(&mut s, "(A (B) C)");
        test(&mut s, "(A (B . C) (D E (F)) G)");
        // TODO: Writer should replace (quote a) with 'a.
        // test(&mut s, "'A");
        // test(&mut s, "'(A B)");
    }

    #[test]
    fn read_maybe_meta() {
        let mut s = Store::<Fr>::default();
        let package = Package::default();
        let test =
            |store: &mut Store<Fr>, input: &str, expected_ptr: Ptr<Fr>, expected_meta: bool| {
                let mut chars = input.chars().peekmore();

                let (ptr, meta) = store.read_maybe_meta(&mut chars, &package).unwrap();
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
        let kw = s.read(":uiop").unwrap();
        let kw2 = s.sym(":UIOP");
        let not_kw = s.sym(".UIOP");

        let kw_fetched = s.fetch(&kw).unwrap();
        let kw2_fetched = s.fetch(&kw2).unwrap();
        let not_kw_fetched = s.fetch(&not_kw).unwrap();

        assert!(kw_fetched.is_keyword_sym());
        assert!(kw2_fetched.is_keyword_sym());
        assert!(!not_kw_fetched.is_keyword_sym());
    }

    #[test]
    fn read_string() {
        let mut s = Store::<Fr>::default();

        let test =
            |store: &mut Store<Fr>, input: &str, expected: Option<Ptr<Fr>>, expr: Option<&str>| {
                let maybe_string = store.read_string(&mut input.chars().peekmore()).ok();
                assert_eq!(expected, maybe_string);
                if let Some(ptr) = maybe_string {
                    let res = store
                        .fetch(&ptr)
                        .unwrap_or_else(|| panic!("failed to fetch: {:?}", input));
                    assert_eq!(res.as_str(), expr);
                }
            };

        {
            let str = s.intern_str("asdf");
            test(&mut s, "\"asdf\"", Some(str), Some("asdf"));
            test(&mut s, "\"asdf", None, None);
            test(&mut s, "asdf", None, None);
        }
        {
            let input = "\"foo/bar/baz\"";
            let ptr = s.read_string(&mut input.chars().peekmore()).unwrap();
            let res = s
                .fetch(&ptr)
                .unwrap_or_else(|| panic!("failed to fetch: {:?}", input));
            assert_eq!(res.as_str().unwrap(), "foo/bar/baz");
        }

        {
            let str = s.intern_str(r#"Bob "Bugs" Murphy"#);
            test(
                &mut s,
                r#""Bob \"Bugs\" Murphy""#,
                Some(str),
                Some(r#"Bob "Bugs" Murphy"#),
            );
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
            let res = store.read(input).ok();
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

    #[test]
    fn read_non_fractions() {
        let mut s = Store::<Fr>::default();

        let test = |store: &mut Store<Fr>, a: &str, b: &str| {
            let res_a = store.read(a).unwrap();
            let res_b = store.read(b).unwrap();
            assert!(store.ptr_eq(&res_a, &res_b).unwrap());
        };
        // These tests demonstrate that '/' behaves like other arithmetic operators
        // when a fraction is not being parsed.

        test(&mut s, "'(1+ 2)", "'(1 + 2)");
        test(&mut s, "'(1/ 2)", "'(1 / 2)");

        test(&mut s, "'(0xa+ 2)", "'(0xa + 2)");
        test(&mut s, "'(0xa/ 2)", "'(0xa / 2)");

        test(&mut s, "1+", "1");
        test(&mut s, "1/", "1");

        test(&mut s, "0xa+", "0xa");
        test(&mut s, "0xa/", "0xa");
    }
}
