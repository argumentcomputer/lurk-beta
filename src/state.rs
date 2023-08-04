use anyhow::{bail, Result};
use std::collections::HashMap;

use crate::Symbol;

use super::package::{Package, SymbolRef};

pub struct State {
    current_package: SymbolRef,
    symbol_packages: HashMap<SymbolRef, Package>,
}

impl State {
    pub fn new_with_package(package: Package) -> Self {
        let current_package = package.name().clone();
        let mut symbol_packages = HashMap::default();
        symbol_packages.insert(current_package.clone(), package);
        Self {
            current_package,
            symbol_packages,
        }
    }

    pub fn add_package(&mut self, package: Package) {
        self.symbol_packages.insert(package.name().clone(), package);
    }

    pub fn set_current_package(&mut self, package_name: SymbolRef) -> Result<()> {
        if self.symbol_packages.contains_key(&package_name) {
            self.current_package = package_name;
            Ok(())
        } else {
            bail!("Package {package_name} not found")
        }
    }

    fn get_current_package(&self) -> &Package {
        self.symbol_packages
            .get(&self.current_package)
            .expect("current package must be in the hashmap")
    }

    fn get_current_package_mut(&mut self) -> &mut Package {
        self.symbol_packages
            .get_mut(&self.current_package)
            .expect("current package must be in the hashmap")
    }

    pub fn resolve(&self, symbol_name: &str) -> Option<&SymbolRef> {
        self.get_current_package().resolve(symbol_name)
    }

    pub fn intern(&mut self, symbol_name: String) -> SymbolRef {
        self.get_current_package_mut().intern(symbol_name)
    }

    pub fn import(&mut self, symbols: &[SymbolRef]) -> Result<()> {
        self.get_current_package_mut().import(symbols)
    }

    pub fn use_package(&mut self, package: &Package) -> Result<()> {
        self.get_current_package_mut().use_package(package)
    }

    pub fn print_to_string(&self, symbol: &SymbolRef) -> String {
        self.get_current_package().print_to_string(symbol)
    }

    pub fn intern_path<A: AsRef<str>>(&mut self, path: &[A], keyword: bool) -> Result<SymbolRef> {
        path.iter()
            .try_fold(Symbol::new(keyword).into(), |acc, s| {
                match self.symbol_packages.get_mut(&acc) {
                    Some(package) => Ok(package.intern(String::from(s.as_ref()))),
                    None => bail!("Package {acc} not found"),
                }
            })
    }

    #[inline]
    pub fn minimal() -> Self {
        Self::new_with_package(Package::new(SymbolRef::new(Symbol::root_sym())))
    }

    pub fn initial_lurk_state() -> Self {
        let mut root_package = Package::new(SymbolRef::new(Symbol::root_sym()));

        // bootstrap the keyword package
        let keyword_package = Package::new(SymbolRef::new(Symbol::root_key()));

        // bootstrap the lurk package
        let mut lurk_package = Package::new(root_package.intern("lurk".into()));
        LURK_PACKAGE_SYMBOLS_NAMES.iter().for_each(|symbol_name| {
            lurk_package.intern(symbol_name.to_string());
        });

        // bootstrap the lurk user package
        let mut lurk_user_package = Package::new(root_package.intern("lurk-user".into()));
        lurk_user_package
            .use_package(&lurk_package)
            .expect("all symbols in the lurk package are importable");

        // initiate the state with the lurk user package then add the others
        let mut state = Self::new_with_package(lurk_user_package);
        state.add_package(root_package);
        state.add_package(keyword_package);
        state.add_package(lurk_package);
        state
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

#[cfg(test)]
pub mod test {
    use super::{State, LURK_PACKAGE_SYMBOLS_NAMES};
    use crate::{
        package::{Package, SymbolRef},
        Symbol,
    };

    #[inline]
    fn test_printing_helper(state: &State, symbol: SymbolRef, expected: &str) {
        assert_eq!(state.print_to_string(&symbol), expected.to_string());
    }

    #[test]
    fn test_lurk_state_printing() {
        let mut state = State::initial_lurk_state();

        LURK_PACKAGE_SYMBOLS_NAMES
            .iter()
            .for_each(|s| test_printing_helper(&state, Symbol::lurk_sym(s).into(), s));

        let user_sym = state.intern("user-sym".into());
        test_printing_helper(&state, user_sym.clone(), "user-sym");

        let my_package_name = SymbolRef::new(Symbol::sym(&["my-package"]));
        let mut my_package = Package::new(my_package_name.clone());
        let my_symbol = my_package.intern("my-symbol".into());
        state.add_package(my_package);

        test_printing_helper(&state, my_symbol.clone(), ".my-package.my-symbol");

        let lambda_sym = SymbolRef::new(Symbol::lurk_sym("lambda"));

        state.set_current_package(my_package_name).unwrap();
        test_printing_helper(&state, my_symbol, "my-symbol");
        test_printing_helper(&state, lambda_sym.clone(), ".lurk.lambda");

        state.import(&[lambda_sym.clone()]).unwrap();
        test_printing_helper(&state, lambda_sym, "lambda");
        test_printing_helper(&state, user_sym, ".lurk-user.user-sym");

        let path = ["my-package", "my-other-symbol"];
        state.intern_path(&path, false).unwrap();
        test_printing_helper(
            &state,
            SymbolRef::new(Symbol::sym(&path)),
            "my-other-symbol",
        );
    }
}
