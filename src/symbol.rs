use std::fmt;

use crate::parser::LURK_WHITESPACE;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
/// Module for symbol type, Sym.
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub const KEYWORD_MARKER: char = ':';
pub const SYM_SEPARATOR: char = '.';
pub const SYM_MARKER: char = '.';
pub const ESCAPE_CHARS: &str = "|(){}[],.:'\\\"";

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Serialize, Deserialize, Hash)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
/// Type for hierarchical symbol names
pub struct Symbol {
    pub path: Vec<String>,
}

impl Symbol {
    /// Creates a new Symbol::Sym with the root path `[]`.
    #[inline]
    pub fn root() -> Self {
        Self { path: vec![] }
    }

    /// Returns true if the Symbol is the root sym or keyword, i.e. if it has a path of `[]`.
    pub fn is_root(&self) -> bool {
        self.path.is_empty()
    }

    /// Creates a new Symbol with the path extended by the given vector of path segments.
    pub fn new<A: AsRef<str>>(path: &[A]) -> Self {
        Self {
            path: path.iter().map(|x| String::from(x.as_ref())).collect(),
        }
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
        Self { path }
    }

    pub fn nil() -> Symbol {
        Self::new(&["lurk", "nil"])
    }

    pub fn keyword<A: AsRef<str>>(key: &[A]) -> Symbol {
        Self::new(&["keyword"]).extend(key)
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
                    return Some(Symbol { path });
                }
            }
            // only reachable if self == parent
            Some(Symbol::root())
        }
    }

    pub fn is_keyword(&self) -> bool {
        self == &Self::new(&["keyword"]) || self.has_parent(&Self::new(&["keyword"]))
    }

    pub fn lurk_sym(name: &str) -> Symbol {
        Self::new(&["lurk", name])
    }

    pub fn is_lurk_sym(&self) -> bool {
        self.has_parent(&Self::new(&["lurk"]))
    }

    pub fn lurk_syms() -> HashMap<Symbol, LurkSym> {
        let mut syms = HashMap::new();
        for lurk_sym in LURK_SYMBOLS {
            syms.insert(Self::lurk_sym(&format!("{}", lurk_sym)), *lurk_sym);
        }
        syms
    }

    pub fn is_whitespace(c: char) -> bool {
        LURK_WHITESPACE.iter().any(|x| *x == c)
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

    pub fn print_path(&self) -> String {
        let mut res = String::new();
        let mut iter = self.path.iter().peekable();
        while let Some(next) = iter.next() {
            res.push_str(&Self::escape_symbol_element(next));
            if iter.peek().is_some() || next.is_empty() {
                res.push('.');
            }
        }
        res
    }

    // TODO: needs some kind of whitespace escaping
    pub fn print_raw(&self) -> String {
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
            self.path[0].is_empty()
                || self.path[0].starts_with([
                    '~', '#', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '.', ':', '[', ']',
                    '(', ')', '{', '}', '"', '\\',
                ])
                || self.path[0].starts_with("-1")
                || self.path[0].starts_with("-2")
                || self.path[0].starts_with("-3")
                || self.path[0].starts_with("-4")
                || self.path[0].starts_with("-5")
                || self.path[0].starts_with("-6")
                || self.path[0].starts_with("-7")
                || self.path[0].starts_with("-8")
                || self.path[0].starts_with("-9")
                || self.path[0].starts_with("-0")
                || self.path[0].starts_with(char::is_whitespace)
                || self.path[0].starts_with(char::is_control)
        }
    }

    pub fn direct_parent(&self) -> Option<Symbol> {
        if self.path.is_empty() {
            None
        } else {
            let mut path = self.path.clone();
            path.pop();
            Some(Self { path })
        }
    }
    pub fn direct_child(&self, child: &str) -> Symbol {
        let mut path = self.path.clone();
        path.push(child.into());
        Self { path }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(child) = self.as_child(&Symbol::new(&["keyword"])) {
            if child.path.is_empty() {
                write!(f, ".keyword")?;
            } else {
                write!(f, ":{}", child.print_path())?;
            }
        } else if self.is_root() {
            write!(f, "~()")?;
        } else if self.prints_as_absolute() {
            write!(f, ".{}", self.print_path())?;
        } else {
            write!(f, "{}", self.print_path())?;
        }
        Ok(())
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Symbol {
        let sym_path = &s[1..s.len()]
            .split(SYM_SEPARATOR)
            .map(|x| x.to_owned())
            .collect::<Vec<String>>();
        Self {
            path: sym_path.clone(),
        }
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Symbol {
        (&s as &str).into()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
pub enum LurkSym {
    Atom,
    Begin,
    Car,
    Cdr,
    Char,
    Comm,
    Commit,
    Cons,
    CurrentEnv,
    Emit,
    Eval,
    Eq,
    Hide,
    If,
    Lambda,
    Let,
    Letrec,
    Nil,
    Num,
    U64,
    Open,
    Quote,
    Secret,
    Strcons,
    T,
    OpAdd,
    OpSub,
    OpMul,
    OpDiv,
    OpMod,
    OpEql,
    OpLth,
    OpGth,
    OpLte,
    OpGte,
    Dummy,
}

impl fmt::Display for LurkSym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Atom => write!(f, "atom"),
            Self::Begin => write!(f, "begin"),
            Self::Car => write!(f, "car"),
            Self::Cdr => write!(f, "cdr"),
            Self::Char => write!(f, "char"),
            Self::Comm => write!(f, "comm"),
            Self::Commit => write!(f, "commit"),
            Self::Cons => write!(f, "cons"),
            Self::CurrentEnv => write!(f, "current-env"),
            Self::Emit => write!(f, "emit"),
            Self::Eval => write!(f, "eval"),
            Self::Eq => write!(f, "eq"),
            Self::Hide => write!(f, "hide"),
            Self::If => write!(f, "if"),
            Self::Lambda => write!(f, "lambda"),
            Self::Let => write!(f, "let"),
            Self::Letrec => write!(f, "letrec"),
            Self::Nil => write!(f, "nil"),
            Self::Num => write!(f, "num"),
            Self::U64 => write!(f, "u64"),
            Self::Open => write!(f, "open"),
            Self::Quote => write!(f, "quote"),
            Self::Secret => write!(f, "secret"),
            Self::Strcons => write!(f, "strcons"),
            Self::T => write!(f, "t"),
            Self::OpAdd => write!(f, "+"),
            Self::OpSub => write!(f, "-"),
            Self::OpMul => write!(f, "*"),
            Self::OpDiv => write!(f, "/"),
            Self::OpMod => write!(f, "%"),
            Self::OpEql => write!(f, "="),
            Self::OpLth => write!(f, "<"),
            Self::OpGth => write!(f, ">"),
            Self::OpLte => write!(f, "<="),
            Self::OpGte => write!(f, ">="),
            Self::Dummy => write!(f, "_"),
        }
    }
}

pub const LURK_SYMBOLS: &[LurkSym] = &[
    LurkSym::Atom,
    LurkSym::Begin,
    LurkSym::Car,
    LurkSym::Cdr,
    LurkSym::Char,
    LurkSym::Comm,
    LurkSym::Commit,
    LurkSym::Cons,
    LurkSym::CurrentEnv,
    LurkSym::Emit,
    LurkSym::Eval,
    LurkSym::Eq,
    LurkSym::Hide,
    LurkSym::If,
    LurkSym::Lambda,
    LurkSym::Let,
    LurkSym::Letrec,
    LurkSym::Nil,
    LurkSym::Num,
    LurkSym::U64,
    LurkSym::Open,
    LurkSym::Quote,
    LurkSym::Secret,
    LurkSym::Strcons,
    LurkSym::T,
    LurkSym::OpAdd,
    LurkSym::OpSub,
    LurkSym::OpMul,
    LurkSym::OpDiv,
    LurkSym::OpMod,
    LurkSym::OpEql,
    LurkSym::OpLth,
    LurkSym::OpGth,
    LurkSym::OpLte,
    LurkSym::OpGte,
    LurkSym::Dummy,
];

#[cfg(test)]
pub mod test {

    use super::*;

    #[test]
    fn test_new() {
        let a = Symbol::new(&["foo", "bar"]);
        let b = Symbol {
            path: vec!["foo".to_string(), "bar".to_string()],
        };

        assert_eq!(a, b)
    }

    #[test]
    fn test_parent_child() {
        let a = Symbol::new(&["foo", "bar"]);
        let b = Symbol::new(&["baz", "bam"]);
        let c = Symbol::new(&["foo", "bar", "baz", "bam"]);

        assert_eq!(a.extend(&b.path), c);
        assert!(c.has_parent(&a));
        assert_eq!(c.as_child(&a), Some(b));
        assert_eq!(
            Symbol::new(&["a", "b"]).as_child(&Symbol::new(&["a"])),
            Some(Symbol::new(&["b"]))
        );
        assert!(Symbol::new(&["a", "b"]).has_parent(&Symbol::new(&["a"])),);
        assert_eq!(
            Symbol::new(&["a", "b", "c"]).as_child(&Symbol::new(&["a"])),
            Some(Symbol::new(&["b", "c"]))
        );
        assert!(Symbol::new(&["a", "b", "c"]).has_parent(&Symbol::new(&["a"])),);
        assert_eq!(
            Symbol::new(&["a"]).as_child(&Symbol::root()),
            Some(Symbol::new(&["a"]))
        );
        assert!(Symbol::new(&["a"]).has_parent(&Symbol::new(&["a"])),);
        assert_eq!(
            Symbol::new(&["a"]).as_child(&Symbol::new(&["a"])),
            Some(Symbol::root())
        );
        assert!(Symbol::root().has_parent(&Symbol::root(),));
        assert_eq!(
            Symbol::root().as_child(&Symbol::root()),
            Some(Symbol::root())
        );
        assert_eq!(Symbol::new(&["a"]).as_child(&Symbol::new(&["b"])), None,);
        assert!(!Symbol::new(&["a"]).has_parent(&Symbol::new(&["b"])));
        assert_eq!(
            Symbol::new(&["a"]).as_child(&Symbol::new(&["a,", "b"])),
            None,
        );
        assert!(!Symbol::new(&["a"]).has_parent(&Symbol::new(&["a", "b"])));
    }

    #[test]
    fn test_prints_as_absolute() {
        assert!(!Symbol::root().prints_as_absolute());
        assert!(Symbol::new(&[""]).prints_as_absolute());
        assert!(Symbol::new(&["~"]).prints_as_absolute());
        assert!(Symbol::new(&["#"]).prints_as_absolute());
        assert!(Symbol::new(&["1"]).prints_as_absolute());
        assert!(Symbol::new(&["2"]).prints_as_absolute());
        assert!(Symbol::new(&["3"]).prints_as_absolute());
        assert!(Symbol::new(&["4"]).prints_as_absolute());
        assert!(Symbol::new(&["5"]).prints_as_absolute());
        assert!(Symbol::new(&["6"]).prints_as_absolute());
        assert!(Symbol::new(&["7"]).prints_as_absolute());
        assert!(Symbol::new(&["8"]).prints_as_absolute());
        assert!(Symbol::new(&["9"]).prints_as_absolute());
        assert!(Symbol::new(&["0"]).prints_as_absolute());
        assert!(Symbol::new(&["."]).prints_as_absolute());
        assert!(Symbol::new(&[":"]).prints_as_absolute());
        assert!(Symbol::new(&["["]).prints_as_absolute());
        assert!(Symbol::new(&["]"]).prints_as_absolute());
        assert!(Symbol::new(&["("]).prints_as_absolute());
        assert!(Symbol::new(&[")"]).prints_as_absolute());
        assert!(Symbol::new(&["{"]).prints_as_absolute());
        assert!(Symbol::new(&["}"]).prints_as_absolute());
        assert!(Symbol::new(&["\""]).prints_as_absolute());
        assert!(Symbol::new(&["\\"]).prints_as_absolute());
        assert!(Symbol::new(&["-1"]).prints_as_absolute());
        assert!(Symbol::new(&["-2"]).prints_as_absolute());
        assert!(Symbol::new(&["-3"]).prints_as_absolute());
        assert!(Symbol::new(&["-4"]).prints_as_absolute());
        assert!(Symbol::new(&["-5"]).prints_as_absolute());
        assert!(Symbol::new(&["-6"]).prints_as_absolute());
        assert!(Symbol::new(&["-7"]).prints_as_absolute());
        assert!(Symbol::new(&["-8"]).prints_as_absolute());
        assert!(Symbol::new(&["-9"]).prints_as_absolute());
        assert!(Symbol::new(&["-0"]).prints_as_absolute());
        assert!(Symbol::new(&[" "]).prints_as_absolute());
        assert!(Symbol::new(&["\x00"]).prints_as_absolute());
    }

    #[test]
    fn test_sym() {
        assert_eq!("a.b.c", format!("{}", Symbol::new(&["a", "b", "c"])));
        let root = Symbol::root();
        let a = root.direct_child("a");
        let a_b = a.direct_child("b");
        let a_b_path = vec!["a", "b"];

        assert_eq!("a", format!("{}", a));
        assert_eq!("a.b", format!("{}", a_b));
        assert_eq!(&a_b_path, &a_b.path);
        assert_eq!(Some(a.clone()), a_b.direct_parent());
        assert_eq!(Some(root.clone()), a.direct_parent());
        assert_eq!(None, root.direct_parent());
    }

    #[test]
    fn test_keywords() {
        let root = Symbol::root();
        let key_root = Symbol::new(&["keyword"]);

        let apple = root.direct_child("apple");
        let orange = key_root.direct_child("orange");

        assert_eq!("apple", format!("{}", apple));
        assert_eq!(":orange", format!("{}", orange));
        assert!(!apple.is_keyword());
        assert!(orange.is_keyword());
        assert_eq!(key_root, orange.direct_parent().unwrap());
        assert!(apple.direct_parent().unwrap() != key_root);
    }
}
