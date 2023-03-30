use std::collections::HashSet;

use crate::sym::Sym;

#[derive(Clone, Debug)]
pub struct Package {
    pub name: Sym,
    pub external_symbols: HashSet<Sym>,
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
    pub fn new(name: Sym) -> Self {
        Self {
            name,
            external_symbols: Default::default(),
        }
    }

    pub fn root() -> Self {
        Self::new(Sym::root())
    }

    pub fn name(&self) -> &Sym {
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

    pub fn remove_external_symbol(&mut self, sym: &Sym) {
        self.external_symbols.remove(sym);
    }

    pub fn remove_external_symbols(&mut self, syms: &[Sym]) {
        for sym in syms.iter() {
            self.external_symbols.remove(sym);
        }
    }

    pub fn local_symbol(&self, sym: &Sym) -> Option<&Sym> {
        self.external_symbols.get(sym)
    }

    pub fn relative_abbreviation(&self, sym: &Sym) -> Sym {
        let name = &self.name;
        let name_path = name.path();
        let sym_path = sym.path();

        if sym.is_keyword() != name.is_keyword() {
            return sym.clone();
        }

        if sym_path.len() < name_path.len() {
            return sym.clone();
        }

        let name_is_prefix = sym_path.iter().zip(name.path()).all(|(a, b)| a == b);

        if name_is_prefix && sym_path != name_path {
            Sym::new_from_path(false, sym_path[name_path.len()..].to_vec())
        } else {
            sym.clone()
        }
    }

    pub fn lurk() -> Self {
        let lurk_sym = Sym::new_from_path(false, vec!["".into(), "LURK".into()]);
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
