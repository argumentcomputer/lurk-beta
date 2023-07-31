use std::collections::{HashMap, HashSet};

use crate::Symbol;

pub struct Package {
    name: Symbol,
    interned: HashSet<String>,
    mappings: HashMap<String, Symbol>,
}

impl Package {
    #[inline]
    pub fn new(name: Symbol) -> Self {
        Self {
            name,
            interned: Default::default(),
            mappings: Default::default(),
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
    pub fn resolve(&self, symbol_name: &str) -> Option<&Symbol> {
        self.mappings.get(symbol_name)
    }

    pub fn intern(&mut self, symbol_name: &str) -> &Symbol {
        if self.interned.contains(symbol_name) {
            self.resolve(&symbol_name)
                .expect("symbol must have been interned")
        } else {
            let symbol_name_clone = symbol_name.to_string();
            let symbol = self.name.direct_child(symbol_name_clone.clone());
            self.interned.insert(symbol_name_clone.clone());
            self.mappings.insert(symbol_name_clone, symbol.clone());
            self.resolve(symbol_name).unwrap()
        }
    }

    pub fn import_symbols(&mut self, package_name: &Symbol, symbol_names: &[String]) {
        symbol_names.iter().for_each(|symbol_name| {
            let symbol_name = symbol_name.to_string();
            let symbol = package_name.direct_child(symbol_name.clone());
            self.mappings.insert(symbol_name, symbol);
        })
    }

    // pub fn use_package(&mut self, )

    // #[inline]
    // pub fn intern(&mut self, symbol_name: String) {
    //     self.interned.insert(symbol_name);
    // }

    // pub fn import_symbols(&mut self, package_name: Symbol, symbol_names: &[String]) {
    //     match self.imported.get_mut(&package_name) {
    //         None => {
    //             let set = symbol_names
    //                 .iter()
    //                 .fold(HashSet::default(), |mut acc, symbol_name| {
    //                     acc.insert(symbol_name.clone());
    //                     acc
    //                 });
    //             self.imported.insert(package_name, set);
    //         }
    //         Some(pkg) => {
    //             symbol_names.iter().for_each(|symbol_name| {
    //                 pkg.insert(symbol_name.clone());
    //             });
    //         }
    //     }
    // }
}
