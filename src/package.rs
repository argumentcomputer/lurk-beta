use anyhow::{bail, Result};
use std::collections::{HashMap, HashSet};

use crate::Symbol;

pub struct Package {
    name: Symbol,
    to_symbol: HashMap<String, Symbol>,
    internal: HashSet<Symbol>,
}

impl Package {
    #[inline]
    pub fn new(name: Symbol) -> Self {
        Self {
            name,
            to_symbol: Default::default(),
            internal: Default::default(),
        }
    }

    #[inline]
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    #[inline]
    pub fn resolve(&self, symbol_name: &str) -> Option<&Symbol> {
        self.to_symbol.get(symbol_name)
    }

    pub fn intern(&mut self, symbol_name: String) -> &Symbol {
        self.to_symbol
            .entry(symbol_name)
            .or_insert_with_key(|symbol_name| {
                let symbol = self.name.direct_child(symbol_name);
                self.internal.insert(symbol.clone());
                symbol
            })
    }

    pub fn import(&mut self, symbols: &[Symbol]) -> Result<()> {
        let mut symbols_names = Vec::with_capacity(symbols.len());
        // first we look for potential errors
        for symbol in symbols {
            let symbol_name = symbol.name()?;
            // check conflicts with accessible symbols
            if let Some(symbol_resolved) = self.to_symbol.get(symbol_name) {
                if symbol != symbol_resolved {
                    bail!("Conflicting symbol for {symbol_name}")
                }
            }
            // memoize the symbols' names for efficiency
            symbols_names.push(symbol_name);
        }
        // now we finally import as an atomic operation
        for (symbol, symbol_name) in symbols.iter().zip(symbols_names) {
            self.to_symbol.insert(symbol_name.clone(), symbol.clone());
        }
        Ok(())
    }
}
