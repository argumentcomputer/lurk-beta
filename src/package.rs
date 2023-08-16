use anyhow::{bail, Result};
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::Symbol;

pub type SymbolRef = Arc<Symbol>;

pub struct Package {
    name: SymbolRef,
    symbols: HashMap<String, SymbolRef>,
    names: HashMap<SymbolRef, String>,
    local: HashSet<SymbolRef>,
}

impl Package {
    #[inline]
    pub fn new(name: SymbolRef) -> Self {
        Self {
            name,
            symbols: Default::default(),
            names: Default::default(),
            local: Default::default(),
        }
    }

    #[inline]
    pub const fn name(&self) -> &SymbolRef {
        &self.name
    }

    #[inline]
    pub fn resolve(&self, symbol_name: &str) -> Option<&SymbolRef> {
        self.symbols.get(symbol_name)
    }

    /// Given a symbol name, returns the corresponding symbol if it's accessible
    /// in the package. If it's not, make it so by creating a new symbol prefixed
    /// by the package's name.
    pub fn intern(&mut self, symbol_name: String) -> SymbolRef {
        self.symbols
            .entry(symbol_name)
            .or_insert_with_key(|symbol_name| {
                let symbol: SymbolRef = self.name.direct_child(symbol_name).into();
                self.names.insert(symbol.clone(), symbol_name.clone());
                self.local.insert(symbol.clone());
                symbol
            })
            .clone()
    }

    /// Tries to import a list of symbols so they become accessible in the package.
    /// If some symbol can't be imported due to an error (i.e. it conflicts with
    /// another accessible symbol), none of the symbols are effectively imported.
    /// In other words, importing is an atomic operation.
    pub fn import(&mut self, symbols: &[SymbolRef]) -> Result<()> {
        let mut symbols_names = Vec::with_capacity(symbols.len());
        // first we look for potential errors
        for symbol in symbols {
            let symbol_name = symbol.name()?;
            // check conflicts with accessible symbols
            if let Some(symbol_resolved) = self.resolve(symbol_name) {
                if symbol != symbol_resolved {
                    bail!("{symbol} conflicts with {symbol_resolved}, which is already accessible")
                }
            }
            // memoize the symbols' names for efficiency
            symbols_names.push(symbol_name);
        }
        // now we finally import as an atomic operation
        for (symbol, symbol_name) in symbols.iter().zip(symbols_names) {
            self.symbols.insert(symbol_name.to_string(), symbol.clone());
            self.names.insert(symbol.clone(), symbol_name.to_string());
        }
        Ok(())
    }

    /// Import the local symbols of another package
    pub fn use_package(&mut self, package: &Package) -> Result<()> {
        self.import(&package.local.iter().cloned().collect::<Vec<_>>())
    }

    pub fn fmt_to_string(&self, symbol: &SymbolRef) -> String {
        match self.names.get(symbol) {
            None => symbol.fmt_to_string(),
            Some(name) => Symbol::fmt_path_component_to_string(name),
        }
    }
}
