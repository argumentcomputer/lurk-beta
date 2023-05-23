#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Symbol {
    Sym(Vec<String>),
    Key(Vec<String>),
}

impl Symbol {
    pub fn sym(path: Vec<&str>) -> Symbol {
        Symbol::Sym(path.iter().map(|x| x.to_string()).collect())
    }

    pub fn key(path: Vec<&str>) -> Symbol {
        Symbol::Key(path.iter().map(|x| x.to_string()).collect())
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
