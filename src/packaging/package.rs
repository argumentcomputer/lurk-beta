use anyhow::{bail, Result};
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::Symbol;

pub struct Package {
    name: Symbol,
    symbols: HashMap<String, Rc<Symbol>>,
    local: HashSet<Symbol>,
}

impl Package {
    #[inline]
    pub fn new(name: Symbol) -> Self {
        Self {
            name,
            symbols: Default::default(),
            local: Default::default(),
        }
    }

    #[inline]
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    #[inline]
    pub fn resolve(&self, symbol_name: &str) -> Option<&Rc<Symbol>> {
        self.symbols.get(symbol_name)
    }

    /// Given a symbol name, returns the corresponding symbol if it's accessible
    /// in the package. If it's not, make it so by creating a new symbol prefixed
    /// by the package's name.
    pub fn intern(&mut self, symbol_name: String) -> &Symbol {
        self.symbols
            .entry(symbol_name)
            .or_insert_with_key(|symbol_name| {
                let symbol = self.name.direct_child(symbol_name);
                self.local.insert(symbol.clone());
                symbol.into()
            })
    }

    /// Tries to import a list of symbols so they become accessible in the package.
    /// If some symbol can't be imported due to an error (i.e. it conflicts with
    /// another accessible symbol), none of the symbols are effectively imported.
    /// In other words, importing is an atomic operation.
    pub fn import(&mut self, symbols: &[Rc<Symbol>]) -> Result<()> {
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
            self.symbols.insert(symbol_name.clone(), symbol.clone());
        }
        Ok(())
    }
}
