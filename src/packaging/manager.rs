use anyhow::{bail, Result};
use std::collections::HashMap;

use super::package::{Package, SymbolRef};

pub struct PackageManager {
    current: SymbolRef,
    packages: HashMap<SymbolRef, Package>,
}

impl PackageManager {
    pub fn init(package: Package) -> Self {
        let current = package.name().clone();
        let mut packages = HashMap::default();
        packages.insert(current.clone(), package);
        Self { current, packages }
    }

    pub fn add_package(&mut self, package: Package) {
        self.packages.insert(package.name().clone(), package);
    }

    pub fn set_current(&mut self, package_name: SymbolRef) -> Result<()> {
        if self.packages.contains_key(&package_name) {
            self.current = package_name;
            Ok(())
        } else {
            bail!("Package {package_name} not found")
        }
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

    pub fn resolve(&self, symbol_name: &str) -> Option<SymbolRef> {
        self.get_current().resolve(symbol_name)
    }

    pub fn intern(&mut self, symbol_name: String) -> SymbolRef {
        self.get_current_mut().intern(symbol_name)
    }

    pub fn import(&mut self, symbols: &[SymbolRef]) -> Result<()> {
        self.get_current_mut().import(symbols)
    }
}
