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

    pub fn format(&self, symbol: &SymbolRef) -> String {
        self.get_current().format(symbol)
    }
}

impl Default for PackageManager {
    fn default() -> Self {
        let root_package_name = SymbolRef::new(crate::Symbol::root());
        let mut root_package = Package::new(root_package_name);

        // bootstrap the keyword package
        let keyword_package_name = root_package.intern("keyword".into());
        let keyword_package = Package::new(keyword_package_name);

        // bootstrap the lurk package
        let lurk_package_name = root_package.intern("lurk".into());
        let mut lurk_package = Package::new(lurk_package_name);
        LURK_PACKAGE_SYMBOLS_NAMES.iter().for_each(|symbol_name| {
            lurk_package.intern(symbol_name.to_string());
        });

        // initiate the package manager with the root package and add the keyword
        // and the lurk packages
        let mut manager = Self::init(root_package);
        manager.add_package(keyword_package);
        manager.add_package(lurk_package);
        manager
    }
}

const LURK_PACKAGE_SYMBOLS_NAMES: [&str; 36] = [
    "atom",
    "begin",
    "car",
    "cdr",
    "char",
    "comm",
    "commit",
    "cons",
    "current-env",
    "emit",
    "eval",
    "eq",
    "hide",
    "if",
    "lambda",
    "let",
    "letrec",
    "nil",
    "num",
    "u64",
    "open",
    "quote",
    "secret",
    "strcons",
    "t",
    "+",
    "-",
    "*",
    "/",
    "%",
    "=",
    "<",
    ">",
    "<=",
    ">=",
    "_",
];
