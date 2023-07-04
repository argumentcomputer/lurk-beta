use anyhow::{bail, Result};
use std::collections::HashMap;

use super::Var;

/// `VarMap` is a wrapper around a `HashMap` whose keys are `Var`s. It's meant
/// to be more ergonomic under the assumption that a LEM must always define
/// variables before using them, so we don't expect to need some piece of
/// information from a variable that hasn't been defined.
#[derive(Clone)]
pub struct VarMap<V>(HashMap<Var, V>);

impl<V> VarMap<V> {
    /// Creates an empty `VarMap`
    #[inline]
    pub(crate) fn new() -> VarMap<V> {
        VarMap(HashMap::default())
    }

    /// Inserts new data into a `VarMap`
    #[inline]
    pub(crate) fn insert(&mut self, var: Var, v: V) {
        self.0.insert(var, v);
    }

    /// Retrieves data from a `VarMap`. Errors if there's no data for the `Var`
    pub(crate) fn get(&self, var: &Var) -> Result<&V> {
        match self.0.get(var) {
            Some(v) => Ok(v),
            None => bail!("Data for variable {var} not found"),
        }
    }

    pub(crate) fn get_many(&self, args: &[Var]) -> Result<Vec<&V>> {
        args.iter().map(|arg| self.get(arg)).collect()
    }
}

impl<V: Clone> VarMap<V> {
    #[inline]
    pub(crate) fn get_cloned(&self, var: &Var) -> Result<V> {
        self.get(var).cloned()
    }

    pub(crate) fn get_many_cloned(&self, args: &[Var]) -> Result<Vec<V>> {
        args.iter().map(|arg| self.get_cloned(arg)).collect()
    }
}
