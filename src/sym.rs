use crate::parser::{
    maybe_quote_symbol_name_string, read_symbol_path, KEYWORD_MARKER, SYM_SEPARATOR,
};

use peekmore::PeekMore;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
/// Module for symbol type, Sym.
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Serialize, Deserialize, Hash)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
/// Type for hieararchical symbol names
///
/// # Example
///
/// ```
/// # use lurk::Symbol;
/// let r = Symbol::root();
/// let a_b = r.child("a".into()).child("b".into());
/// assert_eq!(a_b.full_name(), "|a|.|b|");
/// assert_eq!(a_b.path(), &vec!["", "a", "b"]);
/// ```
pub struct Symbol {
    pub path: Vec<String>,
    // It would be better not to have this here, but it simplifies things in the Store, at least for now.
    pub opaque: bool,
}

/// Enumeration type for symbol names, which can either be a Symbol or a Keyword Symbol.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Serialize, Deserialize, Hash)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
pub enum Sym {
    Sym(Symbol),
    Key(Symbol),
}

trait SymbolTrait {}

impl Symbol {
    /// Creates a new Symbol with the root path `[""]`.
    pub fn root() -> Self {
        Self::new_from_path(vec!["".into()])
    }

    /// Creates a new Symbol with the given name and a path derived from it.
    pub fn new(name: String) -> Self {
        let path = Self::path_from_name(&name);
        Self {
            path,
            opaque: false,
        }
    }

    /// Creates a new Symbol with an absolute path derived from the given name.
    pub fn new_absolute(name: String) -> Self {
        let path = Self::root_path_from_name(&name);
        Self {
            path,
            opaque: false,
        }
    }

    /// Returns true if the Symbol is marked as opaque.
    pub fn is_opaque(&self) -> bool {
        self.opaque
    }

    /// Returns true if the Symbol is the root Symbol, i.e. if it has a path of `[""]`.
    pub fn is_root(&self) -> bool {
        !self.is_opaque() && self.path.len() == 1 && self.path[0].is_empty()
    }

    /// Returns true if the Symbol is a top-level Symbol, i.e. if it has more than one path segment and its first segment is empty.
    pub fn is_toplevel(&self) -> bool {
        self.path.len() > 1 && self.path[0].is_empty()
    }

    /// Returns the name of the Symbol.
    pub fn name(&self) -> String {
        let path = self.path();
        let l = path.len();
        path[l - 1].clone()
    }

    /// Returns the full name of the Symbol.
    pub fn full_name(&self) -> String {
        Self::name_from_path(&self.path)
    }

    /// Returns the parent Symbol of the Symbol, if there is one.
    pub fn parent(&self) -> Option<Self> {
        let path = self.path();
        let rest_path = &path[..path.len() - 1];
        if rest_path.is_empty() {
            None
        } else {
            Some(Self::new_from_path(rest_path.to_vec()))
        }
    }

    /// Creates a new Symbol with a child path segment added to the path of the original Symbol.
    pub fn child(&self, name: String) -> Self {
        assert!(!name.contains(SYM_SEPARATOR));
        let mut path = self.path().clone();
        path.push(name);

        Self::new_from_path(path)
    }

    /// Creates a new Symbol with the path extended by the given vector of path segments.
    pub fn extend(&self, path: &[String]) -> Self {
        let mut new_path = Vec::with_capacity(self.path.len() + path.len());
        for elt in self.path().iter() {
            new_path.push(elt.clone());
        }
        for elt in path.iter() {
            new_path.push(elt.clone());
        }

        Self::new_from_path(new_path)
    }

    /// Creates a new opaque Symbol with an empty path.
    pub fn new_opaque() -> Self {
        Symbol {
            path: Default::default(),
            opaque: true,
        }
    }

    /// Returns a reference to the path vector of the Symbol.
    pub fn path(&self) -> &Vec<String> {
        &self.path
    }

    /// Derives a Symbol path vector from a string name.
    fn new_from_path(path: Vec<String>) -> Self {
        Symbol {
            path,
            opaque: false,
        }
    }

    // This is the function that normalizes full names by converting all path segments to their quoted forms if and only if needed.
    fn name_from_path(path: &[String]) -> String {
        assert!(!path.is_empty());

        let mut p = path.iter();

        if path[0].is_empty() {
            p.next();
        };

        p.map(|name| maybe_quote_symbol_name_string(name).unwrap())
            .collect::<Vec<_>>()
            .join(SYM_SEPARATOR)
    }

    /// Derives a Symbol path vector from a string name, ensuring that the path starts with a root segment `""`.
    fn root_path_from_name(name: &str) -> Vec<String> {
        let mut chars = name.chars().peekmore();

        let (_is_keyword, p) = read_symbol_path(&mut chars)
            .unwrap_or_else(|_| panic!("does not name a valid path: {}", name));

        // Ensure path is a root path, beginning with a single "".
        if p[0].is_empty() {
            p
        } else {
            let mut path = Vec::with_capacity(p.len() + 1);
            path.push("".into());
            path.extend(p);
            path
        }
    }

    /// Derives a Symbol path vector from a string name.
    fn path_from_name(name: &str) -> Vec<String> {
        let mut chars = name.chars().peekmore();
        let (_is_keyword, path) = read_symbol_path(&mut chars)
            .unwrap_or_else(|_| panic!("does not name a valid path: {}", name));

        path
    }

    pub fn is_keyword(&self) -> bool {
        self.path().len() == 2
    }
}

impl Sym {
    /// Creates a new Sym with the given name.
    // Name here might include an initial ':'.
    pub fn new(name: String) -> Self {
        let mut chars = name.chars();
        match chars.next() {
            Some(c) if c == KEYWORD_MARKER => Self::Key(Symbol::new(chars.collect::<String>())),
            _ => Self::Sym(Symbol::new(name)),
        }
    }

    /// Creates a new absolute Sym with the given name.
    pub fn new_absolute(name: String) -> Self {
        let mut chars = name.chars();
        match chars.next() {
            Some(c) if c == KEYWORD_MARKER => {
                Self::Key(Symbol::new_absolute(chars.collect::<String>()))
            }
            _ => Self::Sym(Symbol::new(name)),
        }
    }

    /// Creates a new Sym from a path vector and a boolean flag indicating whether the Sym is a keyword.
    pub fn new_from_path(is_keyword: bool, path: Vec<String>) -> Self {
        assert!(!path.is_empty());

        if is_keyword {
            Self::Key(Symbol::new_from_path(path))
        } else {
            Self::Sym(Symbol::new_from_path(path))
        }
    }

    /// Creates a new Sym with a name derived from the given string.
    pub fn new_sym(name: String) -> Self {
        Self::Sym(Symbol::new(format!(".{name}")))
    }

    /// Creates a new Keyword Sym with a name derived from the given string.
    pub fn new_key(name: String) -> Self {
        Self::Key(Symbol::new(format!(":{name}")))
    }

    /// Creates a new opaque Sym.
    pub fn new_opaque(keyword: bool) -> Self {
        let s = Symbol::new_opaque();
        if keyword {
            Self::Key(s)
        } else {
            Self::Sym(s)
        }
    }

    /// Returns the root Symbol.
    pub fn root() -> Self {
        Self::Sym(Symbol::root())
    }

    /// Returns the root Keyword Symbol.
    pub fn key_root() -> Self {
        Self::Key(Symbol::root())
    }

    /// Returns the full name of the Symbol or Keyword symbol.
    // This should parse to the symbol or keyword it self.
    pub fn full_name(&self) -> String {
        match self {
            Self::Sym(s) => {
                if self.is_root() {
                    "".into()
                } else if self.is_toplevel() {
                    format!(".{}", s.full_name())
                } else {
                    s.full_name()
                }
            }
            Self::Key(s) => {
                assert!(
                    self.is_root() || self.is_toplevel(),
                    "keywords must be fully-qualified."
                );
                format!(":{}", s.full_name())
            }
        }
    }

    /// The full name corresponding to the symbol or keyword's hash.
    pub fn full_sym_name(&self) -> String {
        match self {
            Self::Sym(s) => s.full_name(),
            Self::Key(s) => s.full_name(),
        }
    }

    // The name part (i.e. last path segment) of the symbol or keyword.
    pub fn name(&self) -> String {
        match self {
            Self::Sym(s) => s.name(),
            Self::Key(s) => s.name(),
        }
    }

    /// The full name corresponding to a Sym, if it is a keyword.
    pub fn keyword_name(&self) -> Option<String> {
        match self {
            Self::Key(_) => Some(self.name()),
            Self::Sym(_) => None,
        }
    }

    /// The simple name corresponding to a Sym, if it is a keyword and not at the top level.
    pub fn simple_keyword_name(&self) -> Option<String> {
        if !self.is_toplevel() {
            None
        } else {
            match self {
                Self::Key(_) => Some(self.name()),
                Self::Sym(_) => None,
            }
        }
    }

    /// Returns a reference to the path vector of the Sym.
    pub fn path(&self) -> &Vec<String> {
        match self {
            Self::Sym(s) => &s.path,
            Self::Key(s) => &s.path,
        }
    }

    /// Creates a new Sym with a child path segment added to the path of the original Symbol.
    pub fn child(&self, name: String) -> Self {
        match self {
            Self::Sym(s) => Self::Sym(s.child(name)),
            Self::Key(s) => Self::Key(s.child(name)),
        }
    }

    /// Returns the parent of the Sym or Keyword, if there is one.
    pub fn parent(&self) -> Option<Self> {
        match self {
            Self::Sym(s) => s.parent().map(Self::Sym),
            Self::Key(s) => s.parent().map(Self::Key),
        }
    }

    /// Creates a new Sym with the path extended by the given vector of path segments.
    pub fn extend(&self, path: &[String]) -> Self {
        match self {
            Self::Sym(s) => Self::Sym(s.extend(path)),
            Self::Key(s) => Self::Key(s.extend(path)),
        }
    }

    /// Returns true if the Sym is a keyword.
    pub fn is_keyword(&self) -> bool {
        matches!(self, Self::Key(_))
    }

    /// Returns true if the Sym is toplevel
    pub fn is_toplevel(&self) -> bool {
        self.symbol().is_toplevel()
    }

    /// Returns true if the Sym is the root symbol.
    pub fn is_root(&self) -> bool {
        self.symbol().is_root()
    }

    /// Returns true if the Sym is a symbol.
    pub fn symbol(&self) -> &Symbol {
        match self {
            Self::Sym(s) => s,
            Self::Key(s) => s,
        }
    }
}

impl From<&str> for Sym {
    fn from(s: &str) -> Sym {
        Sym::new(s.into())
    }
}

impl From<String> for Sym {
    fn from(s: String) -> Sym {
        Sym::new(s)
    }
}

#[cfg(test)]
pub mod test {

    use super::*;

    #[test]
    fn test_sym() {
        let root = Sym::root();
        dbg!(root.path());
        let a = root.child("a".into());
        let a_b = a.child("b".into());
        let a_b_path = vec!["", "a", "b"];

        assert_eq!(".|a|", a.full_name());
        assert_eq!(".|a|.|b|", a_b.full_name());
        assert_eq!(&a_b_path, a_b.path());
        assert_eq!(Some(a.clone()), a_b.parent());
        assert_eq!(Some(root.clone()), a.parent());
        assert_eq!(None, root.parent());
    }

    #[test]
    fn test_keywords() {
        let root = Sym::root();
        let key_root = Sym::key_root();

        let apple = root.child("APPLE".into());
        let orange = key_root.child("ORANGE".into());

        assert_eq!("APPLE", apple.name());
        assert_eq!("ORANGE", orange.name());
        assert!(!apple.is_keyword());
        assert!(orange.is_keyword());
        assert_eq!(key_root, orange.parent().unwrap());
        assert!(apple.parent().unwrap() != key_root);
    }
}
