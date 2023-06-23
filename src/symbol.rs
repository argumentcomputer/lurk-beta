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
pub enum Symbol {
    Sym(Vec<String>),
    Key(Vec<String>),
}

impl Symbol {
    pub fn sym(path: Vec<&str>) -> Self {
        Symbol::Sym(path.iter().map(|x| x.to_string()).collect())
    }

    pub fn key(path: Vec<&str>) -> Self {
        Symbol::Key(path.iter().map(|x| x.to_string()).collect())
    }

    /// Creates a new Symbol::Sym with the root path `[]`.
    #[inline]
    pub fn root() -> Self {
        Self::Sym(vec![])
    }

    /// Creates a new Symbol::Key with the root path `[]`.
    #[inline]
    pub fn key_root() -> Self {
        Self::Key(vec![])
    }

    /// Retrieves the path of a `Symbol`
    pub fn path(&self) -> &Vec<String> {
        match self {
            Self::Sym(path) | Self::Key(path) => path,
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
    pub fn extend(&self, child: &[String]) -> Self {
        let parent = self.path();
        let mut new_path = Vec::with_capacity(parent.len() + child.len());
        for elt in parent.iter() {
            new_path.push(elt.clone());
        }
        for elt in child.iter() {
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
        Symbol::Sym(vec!["lurk".to_string(), "nil".to_string()])
    }

    pub fn lurk_sym(name: &str) -> Symbol {
        Symbol::Sym(vec!["lurk".to_string(), name.to_string()])
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

    pub fn print_root(&self) -> String {
        format!("#{}", self.marker())
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
            res.push_str(&Self::escape_symbol_element(x));
        }
        if xs[xs.len() - 1].is_empty() {
            res.push(SYM_SEPARATOR);
        }
        res
    }

    pub fn sym_needs_marker(&self) -> bool {
        let xs = self.path();
        if self.is_root()
            || self.is_key()
            || xs[0].is_empty()
            || xs[0] == "#"
            || xs[0] == "~"
            || xs[0] == self.print_root()
        {
            return true;
        };
        let c = xs[0].chars().next().unwrap();
        "~#1234567890.:'[](){},\"\\".chars().any(|x| x == c)
            || char::is_whitespace(c)
            || char::is_control(c)
    }

    pub fn parent(&self) -> Option<Symbol> {
        match self {
            Self::Key(path) => {
                if path.is_empty() {
                    None
                } else {
                    Some(Self::Key(path[0..path.len() - 1].to_vec()))
                }
            }
            Self::Sym(path) => {
                if path.is_empty() {
                    None
                } else {
                    Some(Self::Sym(path[0..path.len() - 1].to_vec()))
                }
            }
        }
    }

    pub fn child(&self, child: &str) -> Symbol {
        match self {
            Self::Key(path) => {
                let mut path = path.clone();
                path.push(child.into());
                Self::Key(path)
            }
            Self::Sym(path) => {
                let mut path = path.clone();
                path.push(child.into());
                Self::Sym(path)
            }
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Symbol::Sym(_) if self.is_root() => {
                write!(f, "~()")
            }
            Symbol::Key(_) if self.is_root() => {
                write!(f, "~:()")
            }
            _ => write!(f, "{}", self.print_escape()),
        }
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Symbol {
        let sym_path = &s[1..s.len()].split(SYM_SEPARATOR).collect::<Vec<&str>>();
        if s.starts_with(SYM_MARKER) {
            Self::sym(sym_path.clone())
        } else if s.starts_with(KEYWORD_MARKER) {
            Self::key(sym_path.clone())
        } else {
            panic!("Invalid starter char for Symbol")
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
    fn test_sym() {
        let root = Symbol::root();
        dbg!(root.path());
        let a = root.child("a".into());
        let a_b = a.child("b".into());
        let a_b_path = vec!["a", "b"];

        assert_eq!("a", a.print_escape());
        assert_eq!("a.b", a_b.print_escape());
        assert_eq!(&a_b_path, a_b.path());
        assert_eq!(Some(a.clone()), a_b.parent());
        assert_eq!(Some(root.clone()), a.parent());
        assert_eq!(None, root.parent());
    }

    #[test]
    fn test_keywords() {
        let root = Symbol::root();
        let key_root = Symbol::key_root();

        let apple = root.child("APPLE".into());
        let orange = key_root.child("ORANGE".into());

        assert_eq!("APPLE", apple.print_escape());
        assert_eq!(":ORANGE", orange.print_escape());
        assert!(!apple.is_key());
        assert!(orange.is_key());
        assert_eq!(key_root, orange.parent().unwrap());
        assert!(apple.parent().unwrap() != key_root);
    }
}
