use std::collections::{HashMap, HashSet};

use crate::Symbol;

pub struct Package {
    name: Symbol,
    interned: HashSet<String>,
    imported: HashMap<Symbol, HashSet<String>>,
}

impl Package {
    #[inline]
    pub fn new(name: Symbol) -> Self {
        Self {
            name,
            interned: Default::default(),
            imported: Default::default(),
        }
    }

    #[inline]
    pub fn root() -> Self {
        Self::new(Symbol::root())
    }

    #[inline]
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    #[inline]
    pub fn intern(&mut self, symbol_name: String) {
        self.interned.insert(symbol_name);
    }

    pub fn import_symbols(&mut self, package_name: Symbol, symbol_names: &[String]) {
        match self.imported.get_mut(&package_name) {
            None => {
                let set = symbol_names
                    .iter()
                    .fold(HashSet::default(), |mut acc, symbol_name| {
                        acc.insert(symbol_name.clone());
                        acc
                    });
                self.imported.insert(package_name, set);
            }
            Some(pkg) => {
                symbol_names.iter().for_each(|symbol_name| {
                    pkg.insert(symbol_name.clone());
                });
            }
        }
    }
}
