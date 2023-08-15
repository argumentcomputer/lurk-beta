#![deny(missing_docs)]

//! This module implements an abstraction for the Lurk state, which changes as
//! Lurk code is evaluated

use anyhow::{bail, Result};
use once_cell::sync::OnceCell;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::Symbol;

use super::package::{Package, SymbolRef};

/// Keeps track of the current package for symbol resolution when reading and printing
pub struct State {
    current_package: SymbolRef,
    symbol_packages: HashMap<SymbolRef, Package>,
}

impl State {
    /// Wraps a state with `Rc<RefCell<...>>`
    #[inline]
    pub fn rccell(self) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(self))
    }

    /// Creates a new state with a given package as the current one
    pub fn new_with_package(package: Package) -> Self {
        let current_package = package.name().clone();
        let mut symbol_packages = HashMap::default();
        symbol_packages.insert(current_package.clone(), package);
        Self {
            current_package,
            symbol_packages,
        }
    }

    /// Adds a package to a state
    pub fn add_package(&mut self, package: Package) {
        self.symbol_packages.insert(package.name().clone(), package);
    }

    /// Sets the current package of the state
    pub fn set_current_package(&mut self, package_name: SymbolRef) -> Result<()> {
        if self.symbol_packages.contains_key(&package_name) {
            self.current_package = package_name;
            Ok(())
        } else {
            bail!("Package {package_name} not found")
        }
    }

    /// Returns the name of the current package
    #[inline]
    pub const fn get_current_package_name(&self) -> &SymbolRef {
        &self.current_package
    }

    /// Returns a reference to the current package
    fn get_current_package(&self) -> &Package {
        self.symbol_packages
            .get(&self.current_package)
            .expect("current package must be in the hashmap")
    }

    /// Returns a mutable reference to the current package
    fn get_current_package_mut(&mut self) -> &mut Package {
        self.symbol_packages
            .get_mut(&self.current_package)
            .expect("current package must be in the hashmap")
    }

    /// Returns the resolved (fully-qualified) symbol given a symbol name
    pub fn resolve(&self, symbol_name: &str) -> Option<&SymbolRef> {
        self.get_current_package().resolve(symbol_name)
    }

    /// Interns a symbol into the current package
    pub fn intern<A: AsRef<str>>(&mut self, symbol_name: A) -> SymbolRef {
        self.get_current_package_mut()
            .intern(String::from(symbol_name.as_ref()))
    }

    /// Imports a set of symbols to the current package
    pub fn import(&mut self, symbols: &[SymbolRef]) -> Result<()> {
        self.get_current_package_mut().import(symbols)
    }

    /// Imports all symbols from a certain package
    pub fn use_package(&mut self, package: &Package) -> Result<()> {
        self.get_current_package_mut().use_package(package)
    }

    /// Formats a symbol to string w.r.t. the current package
    pub fn fmt_to_string(&self, symbol: &SymbolRef) -> String {
        self.get_current_package().fmt_to_string(symbol)
    }

    /// Sequentially intern a symbol into the potentially nested packages according
    /// to its path
    fn intern_fold<A: AsRef<str>>(
        &mut self,
        init: SymbolRef,
        path: &[A],
        create_unknown_packges: bool,
    ) -> Result<SymbolRef> {
        path.iter()
            .try_fold(init, |acc, s| match self.symbol_packages.get_mut(&acc) {
                Some(package) => Ok(package.intern(String::from(s.as_ref()))),
                None => {
                    if create_unknown_packges {
                        let mut package = Package::new(acc);
                        let symbol = package.intern(String::from(s.as_ref()));
                        self.add_package(package);
                        Ok(symbol)
                    } else {
                        bail!("Package {acc} not found")
                    }
                }
            })
    }

    /// Call `intern_fold` w.r.t. the root package
    #[inline]
    pub fn intern_path<A: AsRef<str>>(
        &mut self,
        path: &[A],
        keyword: bool,
        create_unknown_packges: bool,
    ) -> Result<SymbolRef> {
        self.intern_fold(Symbol::root(keyword).into(), path, create_unknown_packges)
    }

    /// Call `intern_fold` w.r.t. the current package
    #[inline]
    pub fn intern_relative_path<A: AsRef<str>>(
        &mut self,
        path: &[A],
        create_unknown_packges: bool,
    ) -> Result<SymbolRef> {
        self.intern_fold(self.current_package.clone(), path, create_unknown_packges)
    }

    /// Initiates the Lurk state with the appropriate structure of packages
    pub fn init_lurk_state() -> Self {
        let mut root_package = Package::new(SymbolRef::new(Symbol::root_sym()));

        // bootstrap the keyword package
        let keyword_package = Package::new(SymbolRef::new(Symbol::root_key()));

        // bootstrap the lurk package
        let mut lurk_package = Package::new(root_package.intern(LURK_PACKAGE_SYMBOL_NAME.into()));
        LURK_PACKAGE_SYMBOLS_NAMES.iter().for_each(|symbol_name| {
            lurk_package.intern(symbol_name.to_string());
        });

        // bootstrap the meta package
        let mut meta_package = Package::new(lurk_package.intern(META_PACKAGE_SYMBOL_NAME.into()));
        META_PACKAGE_SYMBOLS_NAMES.iter().for_each(|symbol_name| {
            meta_package.intern(symbol_name.to_string());
        });

        // bootstrap the user package
        let mut user_package = Package::new(lurk_package.intern(USER_PACKAGE_SYMBOL_NAME.into()));
        user_package
            .use_package(&lurk_package)
            .expect("all symbols in the lurk package are importable");

        // initiate the state with the lurk user package then add the others
        let mut state = Self::new_with_package(user_package);
        state.add_package(root_package);
        state.add_package(keyword_package);
        state.add_package(lurk_package);
        state.add_package(meta_package);
        state
    }
}

impl Default for State {
    fn default() -> Self {
        Self {
            current_package: SymbolRef::new(Symbol::root_sym()),
            symbol_packages: Default::default(),
        }
    }
}

/// Returns the symbol in the Lurk package given the symbol name
#[inline]
pub fn lurk_sym(name: &str) -> Symbol {
    Symbol::sym(&[LURK_PACKAGE_SYMBOL_NAME, name])
}

/// Returns the symbol corresponding to the name of the meta package
#[inline]
pub fn meta_package_symbol() -> Symbol {
    lurk_sym(META_PACKAGE_SYMBOL_NAME)
}

/// Returns the symbol in the user package given the symbol name
#[inline]
pub fn user_sym(name: &str) -> Symbol {
    Symbol::sym(&[LURK_PACKAGE_SYMBOL_NAME, USER_PACKAGE_SYMBOL_NAME, name])
}

static INITIAL_LURK_STATE_CELL: OnceCell<State> = OnceCell::new();

/// Returns a shared reference to the initial Lurk state
pub fn initial_lurk_state() -> &'static State {
    INITIAL_LURK_STATE_CELL.get_or_init(State::init_lurk_state)
}

const LURK_PACKAGE_SYMBOL_NAME: &str = "lurk";
const USER_PACKAGE_SYMBOL_NAME: &str = "user";
const META_PACKAGE_SYMBOL_NAME: &str = "meta";

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

const META_PACKAGE_SYMBOLS_NAMES: [&str; 18] = [
    "def",
    "defrec",
    "load",
    "assert",
    "assert-eq",
    "assert-emitted",
    "assert-error",
    "commit",
    "hide",
    "fetch",
    "open",
    "clear",
    "set-env",
    "prove",
    "verify",
    "defpackage",
    "import",
    "in-package",
];

#[cfg(test)]
pub mod test {
    use super::{lurk_sym, State, LURK_PACKAGE_SYMBOLS_NAMES};
    use crate::{
        package::{Package, SymbolRef},
        Symbol,
    };

    #[inline]
    fn test_printing_helper(state: &State, symbol: SymbolRef, expected: &str) {
        assert_eq!(state.fmt_to_string(&symbol), expected.to_string());
    }

    #[test]
    fn test_lurk_state_printing() {
        let mut state = State::init_lurk_state();

        LURK_PACKAGE_SYMBOLS_NAMES
            .iter()
            .for_each(|s| test_printing_helper(&state, lurk_sym(s).into(), s));

        let user_sym = state.intern("user-sym");
        test_printing_helper(&state, user_sym.clone(), "user-sym");

        let my_package_name = SymbolRef::new(Symbol::sym(&["my-package"]));
        let mut my_package = Package::new(my_package_name.clone());
        let my_symbol = my_package.intern("my-symbol".into());
        state.add_package(my_package);

        test_printing_helper(&state, my_symbol.clone(), ".my-package.my-symbol");

        let lambda_sym = SymbolRef::new(lurk_sym("lambda"));

        state.set_current_package(my_package_name).unwrap();
        test_printing_helper(&state, my_symbol, "my-symbol");
        test_printing_helper(&state, lambda_sym.clone(), ".lurk.lambda");

        state.import(&[lambda_sym.clone()]).unwrap();
        test_printing_helper(&state, lambda_sym, "lambda");
        test_printing_helper(&state, user_sym, ".lurk.user.user-sym");

        let path = ["my-package", "my-other-symbol"];
        state.intern_path(&path, false, false).unwrap();
        test_printing_helper(
            &state,
            SymbolRef::new(Symbol::sym(&path)),
            "my-other-symbol",
        );
    }
}
