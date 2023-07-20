use std::collections::HashSet;

use super::{symbol::Symbol, tag::Tag, Block, Ctrl, Func, Op};

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum PathNode {
    Tag(Tag),
    Symbol(Symbol),
    Bool(bool),
    Default,
}

impl std::fmt::Display for PathNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Tag(tag) => write!(f, "Tag({})", tag),
            Self::Symbol(symbol) => write!(f, "Symbol({})", symbol),
            Self::Bool(b) => write!(f, "Bool({})", b),
            Self::Default => write!(f, "Default"),
        }
    }
}

#[derive(Default, Clone, PartialEq, Eq, Hash)]
pub struct Path(Vec<PathNode>);

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let strings = self.0.iter().map(|x| format!("{}", x)).collect::<Vec<_>>();
        write!(f, "{}", strings.join("."))
    }
}

impl Path {
    pub fn push_tag(&self, tag: &Tag) -> Path {
        let mut path = self.0.clone();
        path.push(PathNode::Tag(*tag));
        Path(path)
    }

    pub fn push_bool(&self, b: bool) -> Path {
        let mut path = self.0.clone();
        path.push(PathNode::Bool(b));
        Path(path)
    }

    pub fn push_symbol(&self, symbol: &Symbol) -> Path {
        let mut path = self.0.clone();
        path.push(PathNode::Symbol(symbol.clone()));
        Path(path)
    }

    pub fn push_default(&self) -> Path {
        let mut path = self.0.clone();
        path.push(PathNode::Default);
        Path(path)
    }

    #[inline]
    pub fn push_tag_inplace(&mut self, tag: &Tag) {
        self.0.push(PathNode::Tag(*tag));
    }

    #[inline]
    pub fn push_bool_inplace(&mut self, b: bool) {
        self.0.push(PathNode::Bool(b));
    }

    #[inline]
    pub fn push_symbol_inplace(&mut self, symbol: &Symbol) {
        self.0.push(PathNode::Symbol(symbol.clone()));
    }

    #[inline]
    pub fn push_default_inplace(&mut self) {
        self.0.push(PathNode::Default);
    }

    #[inline]
    pub fn extend_from_path(&mut self, path: &Path) {
        self.0.extend_from_slice(&path.0)
    }

    /// Computes the number of different paths taken given a list of paths
    pub fn num_paths_taken(paths: &[Self]) -> usize {
        let mut all_paths: HashSet<Self> = HashSet::default();
        paths.iter().for_each(|path| {
            all_paths.insert(path.clone());
        });
        all_paths.len()
    }
}

impl Func {
    /// Computes the number of possible paths in a `Func` can take
    pub fn num_paths(&self) -> usize {
        self.body.num_paths()
    }

    /// Asserts that all paths were visited by a set of frames. This is mostly
    /// for testing purposes.
    pub fn assert_all_paths_taken(&self, paths: &[Path]) {
        assert_eq!(Path::num_paths_taken(paths), self.num_paths());
    }
}

impl Block {
    fn num_paths(&self) -> usize {
        let mut num_paths = 1;
        for op in &self.ops {
            if let Op::Call(_, func, _) = op {
                num_paths *= func.num_paths()
            }
        }
        num_paths *= match &self.ctrl {
            Ctrl::MatchTag(_, cases, def) => {
                let init = def.as_ref().map_or(0, |def| def.num_paths());
                cases
                    .values()
                    .fold(init, |acc, block| acc + block.num_paths())
            }
            Ctrl::MatchSymbol(_, cases, def) => {
                let init = def.as_ref().map_or(0, |def| def.num_paths());
                cases
                    .values()
                    .fold(init, |acc, block| acc + block.num_paths())
            }
            Ctrl::IfEq(_, _, eq_block, else_block) => eq_block.num_paths() + else_block.num_paths(),
            Ctrl::Return(..) => 1,
        };
        num_paths
    }
}
