use std::collections::{HashMap, HashSet};

use crate::Symbol;

pub struct Package {
    name: Symbol,
    interned: HashSet<String>,
    resolved: HashMap<String, Symbol>,
    resolvable: HashSet<Symbol>,
}

impl Package {
    #[inline]
    pub fn new(name: Symbol) -> Self {
        Self {
            name,
            interned: Default::default(),
            resolved: Default::default(),
            resolvable: Default::default(),
        }
    }

    #[inline]
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    #[inline]
    pub fn resolve(&self, symbol_name: &str) -> Option<&Symbol> {
        self.resolved.get(symbol_name)
    }

    pub fn intern(&mut self, symbol_name: String) -> &Symbol {
        let symbol = self
            .resolved
            .entry(symbol_name)
            .or_insert_with_key(|symbol_name| {
                self.interned.insert(symbol_name.into());
                self.name.direct_child(symbol_name)
            });
        self.resolvable.insert(symbol.clone());
        symbol
    }

    #[inline]
    fn can_resolve(&self, symbol: &Symbol) -> bool {
        self.resolvable.contains(symbol)
    }

    pub fn import(&mut self, symbols: &[Symbol]) {
        symbols.iter().for_each(|symbol| {
            if !self.can_resolve(symbol) {
                let symbol_name = if symbol.is_root() {
                    // is this correct?
                    String::default()
                } else {
                    symbol.path[symbol.path.len() - 1].clone()
                };
                self.resolved.insert(symbol_name, symbol.clone());
                self.resolvable.insert(symbol.clone());
            }
        })
    }
}
