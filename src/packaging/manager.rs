use anyhow::{bail, Result};
use std::{collections::HashMap, rc::Rc};

use crate::Symbol;

use super::package::Package;

pub struct PackageManager {
    current: Rc<Symbol>,
    packages: HashMap<Rc<Symbol>, Package>,
}

impl PackageManager {
    pub fn init(package: Package) -> Self {
        let current = Rc::new(package.name().clone());
        let mut packages = HashMap::default();
        packages.insert(current.clone(), package);
        Self { current, packages }
    }

    fn get_current(&self) -> &Package {
        self.packages
            .get(&self.current)
            .expect("current package must be in the hashmap")
    }

    fn get_current_mut(&mut self) -> &mut Package {
        self.packages
            .get_mut(&self.current)
            .expect("current package must be in the hashmap")
    }

    pub fn set_current(&mut self, package_name: Rc<Symbol>) -> Result<()> {
        if self.packages.contains_key(&package_name) {
            self.current = package_name;
            Ok(())
        } else {
            bail!("Package {package_name} not found")
        }
    }

    pub fn add_package(&mut self, package: Package) {
        let package_name = Rc::new(package.name().clone());
        self.packages.insert(package_name, package);
    }

    pub fn resolve(&self, symbol_name: &str) -> Option<&Rc<Symbol>> {
        self.get_current().resolve(symbol_name)
    }

    pub fn intern(&mut self, symbol_name: String) -> &Symbol {
        self.get_current_mut().intern(symbol_name)
    }

    pub fn import(&mut self, symbols: &[Rc<Symbol>]) -> Result<()> {
        self.get_current_mut().import(symbols)
    }
}
