use super::AString;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Symbol {
    Sym(Vec<AString>),
    Key(Vec<AString>),
}

impl Symbol {
    pub fn sym(path: &[AString]) -> Symbol {
        Symbol::Sym(path.into())
    }

    pub fn key(path: &[AString]) -> Symbol {
        Symbol::Key(path.into())
    }

    #[inline]
    pub fn root() -> Self {
        Self::Sym(vec![])
    }

    #[inline]
    pub fn path(&self) -> &Vec<AString> {
        match self {
            Self::Sym(path) | Self::Key(path) => path,
        }
    }

    #[inline]
    pub fn lurk_sym_path(name: AString) -> Vec<AString> {
        vec!["lurk".into(), name]
    }

    #[inline]
    pub fn lurk_sym(name: AString) -> Symbol {
        Symbol::Sym(Self::lurk_sym_path(name))
    }
}
