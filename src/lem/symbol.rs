#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Symbol {
    Sym(Vec<String>),
    Key(Vec<String>),
}

impl Symbol {
    pub fn sym(path: &[String]) -> Symbol {
        Symbol::Sym(path.into())
    }

    pub fn key(path: &[String]) -> Symbol {
        Symbol::Key(path.into())
    }

    #[inline]
    pub fn root() -> Self {
        Self::Sym(vec![])
    }

    #[inline]
    pub fn path(&self) -> &Vec<String> {
        match self {
            Self::Sym(path) | Self::Key(path) => path,
        }
    }

    #[inline]
    pub fn lurk_sym_path(name: &str) -> Vec<String> {
        vec!["lurk".to_string(), name.to_string()]
    }

    #[inline]
    pub fn lurk_sym(name: &str) -> Symbol {
        Symbol::Sym(Self::lurk_sym_path(name))
    }
}
