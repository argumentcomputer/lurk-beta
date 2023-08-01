use super::package::Package;

const LURK_PACKAGE_NAME_PATH: [&str; 1] = ["lurk"];

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

pub fn create_lurk_package() -> Package {
    let mut package = Package::new(crate::Symbol::new(&LURK_PACKAGE_NAME_PATH));
    LURK_PACKAGE_SYMBOLS_NAMES.iter().for_each(|symbol_name| {
        package.intern(symbol_name.to_string());
    });
    package
}
