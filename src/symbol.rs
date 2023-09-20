use std::fmt;

use anyhow::{bail, Result};

use crate::{parser::LURK_WHITESPACE, state::State};
#[cfg(not(target_arch = "wasm32"))]
use lurk_macros::serde_test;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

/// Module for symbol type, Sym.
use serde::{Deserialize, Serialize};

pub const KEYWORD_MARKER: char = ':';
pub const SYM_SEPARATOR: char = '.';
pub const SYM_MARKER: char = '.';
pub const ESCAPE_CHARS: &str = "|(){}[],.:'\\\"";

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Serialize, Deserialize, Hash)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), serde_test)]
/// Type for hierarchical symbol names.
pub struct Symbol {
    path: Vec<String>,
    keyword: bool,
}

impl Symbol {
    #[inline]
    pub fn path(&self) -> &[String] {
        &self.path
    }

    #[inline]
    pub const fn is_keyword(&self) -> bool {
        self.keyword
    }

    #[inline]
    pub const fn root(keyword: bool) -> Self {
        Self {
            path: vec![],
            keyword,
        }
    }

    /// Creates a new `Symbol` with an empty path.
    #[inline]
    pub fn root_sym() -> Self {
        Self::root(false)
    }

    /// Creates a new `Symbol` with an empty path.
    #[inline]
    pub fn root_key() -> Self {
        Self::root(true)
    }

    #[inline]
    pub fn is_root(&self) -> bool {
        self.path.is_empty()
    }

    /// Returns true if the `Symbol` is the root symbol
    #[inline]
    pub fn is_root_sym(&self) -> bool {
        self.is_root() && !self.keyword
    }

    #[inline]
    pub fn is_root_key(&self) -> bool {
        self.is_root() && self.keyword
    }

    pub fn new<A: AsRef<str>>(path: &[A], keyword: bool) -> Self {
        Self {
            path: path.iter().map(|x| String::from(x.as_ref())).collect(),
            keyword,
        }
    }

    pub fn new_from_vec(path: Vec<String>, keyword: bool) -> Self {
        Self { path, keyword }
    }

    #[inline]
    pub fn sym<A: AsRef<str>>(path: &[A]) -> Self {
        Self::new(path, false)
    }

    #[inline]
    pub fn key<A: AsRef<str>>(path: &[A]) -> Self {
        Self::new(path, true)
    }

    #[inline]
    pub fn sym_from_vec(path: Vec<String>) -> Self {
        Self::new_from_vec(path, false)
    }

    #[inline]
    pub fn key_from_vec(path: Vec<String>) -> Self {
        Self::new_from_vec(path, true)
    }

    #[inline]
    pub fn set_as_keyword(&mut self) {
        self.keyword = true;
    }

    /// Creates a new Symbol with the path extended by the given vector of path segments.
    pub fn extend<A: AsRef<str>>(&self, child: &[A]) -> Self {
        let mut path = Vec::with_capacity(self.path.len() + child.len());
        for elt in self.path.iter() {
            path.push(elt.clone());
        }
        for elt in child.iter() {
            path.push(String::from(elt.as_ref()));
        }
        Self {
            path,
            keyword: self.keyword,
        }
    }

    pub fn has_parent(&self, parent: &Symbol) -> bool {
        // parent paths can't be longer than child paths
        if self.path.len() < parent.path.len() {
            false
        } else {
            // zip returns an iterator only as long as the shortest path,
            // in this case the parent
            self.path
                .iter()
                .zip(parent.path.iter())
                .all(|(a, b)| a == b)
        }
    }

    pub fn as_child(&self, parent: &Symbol) -> Option<Symbol> {
        // parent paths can't be longer than child paths
        if self.path.len() < parent.path.len() {
            None
        } else {
            let keyword = parent.keyword;
            let mut parent = parent.path.iter();
            let mut child = self.path.iter().peekable();

            // peek if there's more in the child path
            while child.peek().is_some() {
                // if there's more in the parent path, step through both together
                if let Some(next_parent) = parent.next() {
                    let next_child = child.next().unwrap();
                    // the parent path has to be a prefix of the child path
                    if next_child != next_parent {
                        return None;
                    }
                // if there's no more parent path
                } else {
                    let path = child.cloned().collect();
                    // return the remaining child path
                    return Some(Symbol { path, keyword });
                }
            }
            // only reachable if self == parent
            Some(Symbol {
                path: vec![],
                keyword,
            })
        }
    }

    pub fn is_whitespace(c: char) -> bool {
        LURK_WHITESPACE.iter().any(|x| *x == c)
    }

    pub fn fmt_path_component_to_string(xs: &str) -> String {
        let mut res = String::new();
        for x in xs.chars() {
            if ESCAPE_CHARS.chars().any(|c| c == x) {
                res.push_str(&format!("\\{x}"));
            } else if Self::is_whitespace(x) {
                res.push_str(&format!("{}", x.escape_unicode()));
            } else {
                res.push(x)
            }
        }
        res
    }

    pub fn fmt_path_to_string(&self) -> String {
        let mut res = String::new();
        let mut iter = self.path.iter().peekable();
        while let Some(next) = iter.next() {
            res.push_str(&Self::fmt_path_component_to_string(next));
            if iter.peek().is_some() || next.is_empty() {
                res.push('.');
            }
        }
        res
    }

    // TODO: needs some kind of whitespace escaping
    pub fn fmt_to_string_raw(&self) -> String {
        let mut res = String::from("~(");
        let mut iter = self.path.iter().peekable();
        while let Some(next) = iter.next() {
            res.push_str(next);
            match iter.peek() {
                Some(_) => res.push(' '),
                None => res.push(')'),
            }
        }
        res
    }

    pub fn prints_as_absolute(&self) -> bool {
        if self.path.is_empty() {
            false
        } else {
            let head = &self.path[0];
            head.is_empty()
                || head.starts_with([
                    '~', '#', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '.', ':', '[', ']',
                    '(', ')', '{', '}', '"', '\\',
                ])
                || head.starts_with("-1")
                || head.starts_with("-2")
                || head.starts_with("-3")
                || head.starts_with("-4")
                || head.starts_with("-5")
                || head.starts_with("-6")
                || head.starts_with("-7")
                || head.starts_with("-8")
                || head.starts_with("-9")
                || head.starts_with("-0")
                || head.starts_with(char::is_whitespace)
                || head.starts_with(char::is_control)
        }
    }

    pub fn direct_parent(&self) -> Option<Symbol> {
        if self.is_root() {
            None
        } else {
            Some(Self {
                // drop the last component of the path
                path: self.path[0..self.path.len() - 1].to_vec(),
                keyword: self.keyword,
            })
        }
    }

    pub fn direct_child(&self, child: &str) -> Symbol {
        let mut path = self.path.clone();
        path.push(child.into());
        Self {
            path,
            keyword: self.keyword,
        }
    }

    pub fn name(&self) -> Result<&str> {
        if self.is_root() {
            bail!("Root symbols don't have names")
        } else {
            Ok(&self.path[self.path.len() - 1])
        }
    }

    pub fn fmt_to_string(&self) -> String {
        if self.is_keyword() {
            if self.is_root() {
                "~:()".into()
            } else {
                format!(":{}", &self.fmt_path_to_string())
            }
        } else if self.is_root() {
            "~()".into()
        } else {
            format!(".{}", &self.fmt_path_to_string())
        }
    }

    pub fn from_str_impl(name: &str) -> Option<Self> {
        use crate::parser::{
            syntax::{parse_space, parse_symbol},
            Span,
        };
        use crate::syntax::Syntax;
        use nom::{sequence::preceded, Parser};
        use pasta_curves::pallas::Scalar;
        match preceded(
            parse_space::<Scalar>,
            parse_symbol(State::default().rccell(), true),
        )
        .parse(Span::new(name))
        {
            Ok((_, Syntax::Symbol(_, symbol))) => Some((*symbol).clone()),
            _ => None,
        }
    }
}

impl From<&'static str> for Symbol {
    fn from(value: &'static str) -> Self {
        Symbol::from_str_impl(value).unwrap()
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.fmt_to_string())
    }
}

#[macro_export]
macro_rules! sym {
    [$( $x:expr ),*] => {
        {
            let temp_vec = vec![ $( $x.to_string() ),* ];
            $crate::symbol::Symbol::sym(&temp_vec)
        }
    };
}

#[cfg(test)]
pub mod test {

    use super::*;

    #[test]
    fn test_parent_child() {
        let a = Symbol::sym(&["foo", "bar"]);
        let b = Symbol::sym(&["baz", "bam"]);
        let c = Symbol::sym(&["foo", "bar", "baz", "bam"]);

        assert_eq!(a.extend(&b.path), c);
        assert!(c.has_parent(&a));
        assert_eq!(c.as_child(&a), Some(b));
        assert_eq!(
            Symbol::sym(&["a", "b"]).as_child(&Symbol::sym(&["a"])),
            Some(Symbol::sym(&["b"]))
        );
        assert!(Symbol::sym(&["a", "b"]).has_parent(&Symbol::sym(&["a"])),);
        assert_eq!(
            Symbol::sym(&["a", "b", "c"]).as_child(&Symbol::sym(&["a"])),
            Some(Symbol::sym(&["b", "c"]))
        );
        assert!(Symbol::sym(&["a", "b", "c"]).has_parent(&Symbol::sym(&["a"])),);
        assert_eq!(
            Symbol::sym(&["a"]).as_child(&Symbol::root_sym()),
            Some(Symbol::sym(&["a"]))
        );
        assert!(Symbol::sym(&["a"]).has_parent(&Symbol::sym(&["a"])),);
        assert_eq!(
            Symbol::sym(&["a"]).as_child(&Symbol::sym(&["a"])),
            Some(Symbol::root_sym())
        );
        assert!(Symbol::root_sym().has_parent(&Symbol::root_sym(),));
        assert_eq!(
            Symbol::root_sym().as_child(&Symbol::root_sym()),
            Some(Symbol::root_sym())
        );
        assert_eq!(Symbol::sym(&["a"]).as_child(&Symbol::sym(&["b"])), None,);
        assert!(!Symbol::sym(&["a"]).has_parent(&Symbol::sym(&["b"])));
        assert_eq!(
            Symbol::sym(&["a"]).as_child(&Symbol::sym(&["a,", "b"])),
            None,
        );
        assert!(!Symbol::sym(&["a"]).has_parent(&Symbol::sym(&["a", "b"])));
    }

    #[test]
    fn test_prints_as_absolute() {
        assert!(!Symbol::root_sym().prints_as_absolute());
        assert!(Symbol::sym(&[""]).prints_as_absolute());
        assert!(Symbol::sym(&["~"]).prints_as_absolute());
        assert!(Symbol::sym(&["#"]).prints_as_absolute());
        assert!(Symbol::sym(&["1"]).prints_as_absolute());
        assert!(Symbol::sym(&["2"]).prints_as_absolute());
        assert!(Symbol::sym(&["3"]).prints_as_absolute());
        assert!(Symbol::sym(&["4"]).prints_as_absolute());
        assert!(Symbol::sym(&["5"]).prints_as_absolute());
        assert!(Symbol::sym(&["6"]).prints_as_absolute());
        assert!(Symbol::sym(&["7"]).prints_as_absolute());
        assert!(Symbol::sym(&["8"]).prints_as_absolute());
        assert!(Symbol::sym(&["9"]).prints_as_absolute());
        assert!(Symbol::sym(&["0"]).prints_as_absolute());
        assert!(Symbol::sym(&["."]).prints_as_absolute());
        assert!(Symbol::sym(&[":"]).prints_as_absolute());
        assert!(Symbol::sym(&["["]).prints_as_absolute());
        assert!(Symbol::sym(&["]"]).prints_as_absolute());
        assert!(Symbol::sym(&["("]).prints_as_absolute());
        assert!(Symbol::sym(&[")"]).prints_as_absolute());
        assert!(Symbol::sym(&["{"]).prints_as_absolute());
        assert!(Symbol::sym(&["}"]).prints_as_absolute());
        assert!(Symbol::sym(&["\""]).prints_as_absolute());
        assert!(Symbol::sym(&["\\"]).prints_as_absolute());
        assert!(Symbol::sym(&["-1"]).prints_as_absolute());
        assert!(Symbol::sym(&["-2"]).prints_as_absolute());
        assert!(Symbol::sym(&["-3"]).prints_as_absolute());
        assert!(Symbol::sym(&["-4"]).prints_as_absolute());
        assert!(Symbol::sym(&["-5"]).prints_as_absolute());
        assert!(Symbol::sym(&["-6"]).prints_as_absolute());
        assert!(Symbol::sym(&["-7"]).prints_as_absolute());
        assert!(Symbol::sym(&["-8"]).prints_as_absolute());
        assert!(Symbol::sym(&["-9"]).prints_as_absolute());
        assert!(Symbol::sym(&["-0"]).prints_as_absolute());
        assert!(Symbol::sym(&[" "]).prints_as_absolute());
        assert!(Symbol::sym(&["\x00"]).prints_as_absolute());
    }

    #[test]
    fn test_sym() {
        assert_eq!(".a.b.c", format!("{}", Symbol::sym(&["a", "b", "c"])));
        let root = Symbol::root_sym();
        let a = root.direct_child("a");
        let a_b = a.direct_child("b");
        let a_b_path = vec!["a", "b"];

        assert_eq!(".a", format!("{a}"));
        assert_eq!(".a.b", format!("{a_b}"));
        assert_eq!(&a_b_path, &a_b.path);
        assert_eq!(Some(a.clone()), a_b.direct_parent());
        assert_eq!(Some(root.clone()), a.direct_parent());
        assert_eq!(None, root.direct_parent());
    }

    #[test]
    fn test_keywords() {
        let root = Symbol::root_sym();
        let key_root = Symbol::root_key();

        let apple = root.direct_child("apple");
        let orange = key_root.direct_child("orange");

        assert!(!root.is_keyword());
        assert!(key_root.is_keyword());
        assert_eq!(".apple", format!("{apple}"));
        assert_eq!(":orange", format!("{orange}"));
        assert!(!apple.is_keyword());
        assert!(orange.is_keyword());
        assert_eq!(key_root, orange.direct_parent().unwrap());
        assert!(apple.direct_parent().unwrap() != key_root);
    }
}
