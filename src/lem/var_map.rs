use anyhow::{bail, Result};
use std::collections::{hash_map::Entry, HashMap};

use super::Var;

/// `VarMap` is a wrapper around a `HashMap` whose keys are `Var`s. It's meant
/// to be more ergonomic under the following assumptions for LEM:
///
/// 1. A LEM must be in SSA, so we don't want to bind some information to the
/// same `Var` twice;
/// 2. A LEM must always define variables before using them, so we don't expect
/// to need some piece of information from a variable that hasn't been defined.
#[derive(Clone)]
pub struct VarMap<V>(HashMap<Var, V>);

impl<V> VarMap<V> {
    /// Creates an empty `VarMap`
    #[inline]
    pub(crate) fn new() -> VarMap<V> {
        VarMap(HashMap::default())
    }

    /// Inserts new data into a `VarMap`
    ///
    /// Panics if some data already exists for the key
    pub(crate) fn insert(&mut self, var: Var, v: V) -> Result<()> {
        match self.0.entry(var) {
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(v);
                Ok(())
            }
            Entry::Occupied(o) => bail!(
                "Variable {} has previously been defined. LEMs are supposed to be SSA.",
                o.key()
            ),
        }
    }

    /// Retrieves data from a `VarMap`
    ///
    /// Panics if the data doesn't exist for the key
    pub(crate) fn get(&self, var: &Var) -> Result<&V> {
        match self.0.get(var) {
            Some(v) => Ok(v),
            None => bail!("Data for variable {var} not found"),
        }
    }

    pub(crate) fn get_many(&self, args: &[Var]) -> Result<Vec<&V>> {
        let mut vec = vec![];
        for arg in args {
            vec.push(self.get(arg)?);
        }
        Ok(vec)
    }
}

impl<V: Clone> VarMap<V> {
    #[inline]
    pub(crate) fn get_cloned(&self, var: &Var) -> Result<V> {
        self.get(var).cloned()
    }

    pub(crate) fn get_many_cloned(&self, args: &[Var]) -> Result<Vec<V>> {
        let mut vec = vec![];
        for arg in args {
            vec.push(self.get_cloned(arg)?);
        }
        Ok(vec)
    }
}
