use std::fmt;

use crate::parser::whitespace;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
/// Module for symbol type, Sym.
use serde::{Deserialize, Serialize};

pub const KEYWORD_MARKER: char = ':';
pub const SYM_SEPARATOR: char = '.';
pub const SYM_MARKER: char = '.';
pub const ESCAPE_CHARS: &'static str = "(){}[]=,.:";

pub const LURK_SYMBOL_NAMES: &[&str] = &[
    "atom",
    "begin",
    "car",
    "cdr",
    "char",
    "comm",
    "commit",
    "cons",
    "current-env",
    "emit",
    "eval",
    "eq",
    "hide",
    "if",
    "lambda",
    "let",
    "letrec",
    "nil",
    "num",
    "u64",
    "open",
    "quote",
    "secret",
    "strcons",
    "t",
    "_",
    "+",
    "-",
    "*",
    "/",
    "%",
    "=",
    "<",
    ">",
    "<=",
    ">=",
];

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Serialize, Deserialize, Hash)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
/// Type for hieararchical symbol names
pub enum Symbol {
    Sym(Vec<String>),
    Key(Vec<String>),
}

impl Symbol {
    pub fn sym(path: Vec<&str>) -> Symbol {
        Symbol::Sym(path.iter().map(|x| x.to_string()).collect())
    }

    pub fn key(path: Vec<&str>) -> Symbol {
        Symbol::Key(path.iter().map(|x| x.to_string()).collect())
    }
    /// Creates a new Symbol with the root path `[""]`.
    pub fn root() -> Self {
        Self::Sym(vec![])
    }

    /// Returns true if the Symbol is the root sym or keyword, i.e. if it has a path of `[]`.
    pub fn path(&self) -> Vec<String> {
        match self {
            Self::Sym(path) => path.clone(),
            Self::Key(path) => path.clone(),
        }
    }

    /// Returns true if the Symbol is the root sym or keyword, i.e. if it has a path of `[]`.
    pub fn is_root(&self) -> bool {
        self.path().is_empty()
    }

    pub fn is_key(&self) -> bool {
        matches!(self, Self::Key(_))
    }

    /// Creates a new Symbol with the path extended by the given vector of path segments.
    pub fn extend(&self, path: &[String]) -> Self {
        let mut new_path = Vec::with_capacity(self.path().len() + path.len());
        for elt in self.path().iter() {
            new_path.push(elt.clone());
        }
        for elt in path.iter() {
            new_path.push(elt.clone());
        }

        if self.is_key() {
            Self::Key(new_path)
        } else {
            Self::Sym(new_path)
        }
    }

    pub fn marker(&self) -> char {
        match self {
            Self::Sym(_) => SYM_MARKER,
            Self::Key(_) => KEYWORD_MARKER,
        }
    }

    pub fn nil() -> Symbol {
        Symbol::Sym(vec!["LURK".to_string(), "NIL".to_string()])
    }

    pub fn lurk_sym(name: &str) -> Symbol {
        Symbol::Sym(vec!["LURK".to_string(), name.to_string()])
    }

    pub fn lurk_syms() -> Vec<Symbol> {
        let mut vec = Vec::new();
        for name in LURK_SYMBOL_NAMES {
            vec.push(Self::lurk_sym(name))
        }
        vec
    }

    pub fn is_whitespace(c: char) -> bool {
        whitespace().iter().any(|x| *x == c)
    }

    pub fn escape_symbol_element(xs: &str) -> String {
        let mut res = String::new();
        for x in xs.chars() {
            if ESCAPE_CHARS.chars().any(|c| c == x) {
                res.push_str(&format!("\\{}", x));
            } else if Self::is_whitespace(x) {
                res.push_str(&format!("{}", x.escape_unicode()));
            } else {
                res.push(x)
            }
        }
        res
    }

    pub fn print_root(&self) -> String {
        format!("_{}", self.marker())
    }

    pub fn print_escape(&self) -> String {
        if self.is_root() {
            return self.print_root();
        }
        let mut res = String::new();
        let xs = self.path();
        if Self::sym_needs_marker(self) {
            res.push(self.marker())
        }
        res.push_str(&Self::escape_symbol_element(&xs[0]));
        for x in xs[1..].iter() {
            res.push(SYM_SEPARATOR);
            res.push_str(&Self::escape_symbol_element(&x));
        }
        res
    }

    pub fn sym_needs_marker(&self) -> bool {
        let xs = self.path();
        if self.is_root()
            || self.is_key()
            || xs[0].is_empty()
            || xs[0] == "_"
            || xs[0] == self.print_root()
        {
            return true;
        };
        let c = xs[0].chars().next().unwrap();
        "1234567890.:'[](){}=,\"\\".chars().any(|x| x == c)
            || char::is_whitespace(c)
            || char::is_control(c)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_root() {
            write!(f, "_{}", self.marker())
        } else {
            write!(f, "{}", self.print_escape())
        }
    }
}

#[cfg(test)]
pub mod test {

    //use super::*;

    //#[test]
    //fn test_sym() {
    //    let root = Sym::root();
    //    dbg!(root.path());
    //    let a = root.child("a".into());
    //    let a_b = a.child("b".into());
    //    let a_b_path = vec!["", "a", "b"];

    //    assert_eq!(".|a|", a.full_name());
    //    assert_eq!(".|a|.|b|", a_b.full_name());
    //    assert_eq!(&a_b_path, a_b.path());
    //    assert_eq!(Some(a.clone()), a_b.parent());
    //    assert_eq!(Some(root.clone()), a.parent());
    //    assert_eq!(None, root.parent());
    //}

    //#[test]
    //fn test_keywords() {
    //    let root = Sym::root();
    //    let key_root = Sym::key_root();

    //    let apple = root.child("APPLE".into());
    //    let orange = key_root.child("ORANGE".into());

    //    assert_eq!("APPLE", apple.name());
    //    assert_eq!("ORANGE", orange.name());
    //    assert!(!apple.is_keyword());
    //    assert!(orange.is_keyword());
    //    assert_eq!(key_root, orange.parent().unwrap());
    //    assert!(apple.parent().unwrap() != key_root);
    //}
}
