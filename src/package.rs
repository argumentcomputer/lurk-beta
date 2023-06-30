use std::collections::HashSet;

use crate::field::LurkField;
use crate::symbol::Symbol;

#[derive(Clone, Debug)]
pub struct Path {
    path: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Package<F: LurkField> {
    pub name: Symbol,
    // declares symbolic constants
    // builtins like `.lurk.nil` are declared as themselves via the public
    // keywords are `.keyword.foo` and have special syntax `:foo`
    pub syms: HashMap<Symbol, F>,
}

// (.package .foo.bar
//   ( (.foo.bar.baz 0xdead.beef...)
//     (.foo.bar.bam 0xdead.beef...)
//   )
//  )

#[derive(Clone, Debug)]
pub struct Package {
    pub name: Symbol,
    pub external_symbols: HashSet<Symbol>,
}

pub const LURK_EXTERNAL_SYMBOL_NAMES: &[&str] = &[
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

impl Package {
    pub fn new(name: Symbol) -> Self {
        Self {
            name,
            external_symbols: Default::default(),
        }
    }

    pub fn root() -> Self {
        Self::new(Symbol::root())
    }

    pub fn name(&self) -> &Symbol {
        &self.name
    }

    pub fn add_external_symbol<T: AsRef<str>>(&mut self, name: T) {
        let root = &self.name;
        let sym = root.child(name.as_ref().into());

        self.external_symbols.insert(sym);
    }

    pub fn add_external_symbols(&mut self, names: &[&str]) {
        let root = &self.name;

        for name in names.iter() {
            let sym = root.child((*name).into());
            self.external_symbols.insert(sym);
        }
    }

    pub fn remove_external_symbol(&mut self, sym: &Symbol) {
        self.external_symbols.remove(sym);
    }

    pub fn remove_external_symbols(&mut self, syms: &[Symbol]) {
        for sym in syms.iter() {
            self.external_symbols.remove(sym);
        }
    }

    pub fn local_symbol(&self, sym: &Symbol) -> Option<&Symbol> {
        self.external_symbols.get(sym)
    }

    pub fn relative_abbreviation(&self, sym: &Symbol) -> Symbol {
        let name = &self.name;
        let name_path = name.path();
        let sym_path = sym.path();

        if sym.is_key() != name.is_key() {
            return sym.clone();
        }

        if sym_path.len() < name_path.len() {
            return sym.clone();
        }

        let name_is_prefix = sym_path.iter().zip(name.path()).all(|(a, b)| *a == b);

        if name_is_prefix && sym_path != name_path {
            Symbol::Sym(sym_path[name_path.len()..].to_vec())
        } else {
            sym.clone()
        }
    }

    pub fn lurk() -> Self {
        let lurk_sym = Symbol::new(vec!["LURK"]);
        let mut package = Package::new(lurk_sym);

        package.add_external_symbols(LURK_EXTERNAL_SYMBOL_NAMES);

        package
    }
}

impl Default for Package {
    fn default() -> Self {
        Self::lurk()
    }
}
