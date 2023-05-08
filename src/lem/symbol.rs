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
    /// Creates a new Symbol with the root path `[""]`.
    pub fn root() -> Self {
        Self::Sym(vec![])
    }

    /// Returns true if the Symbol is the root sym or keyword, i.e. if it has a path of `[]`.
    pub fn path(&self) -> Vec<String> {
        match self {
            Self::Sym(path) => path.clone(),
            Self::Key(path) => path.clone(),
        }
    }
}
