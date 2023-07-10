use anyhow::Result;
use indexmap::IndexMap;
use std::collections::HashSet;

use super::{symbol::Symbol, tag::Tag, var_map::VarMap, Block, Ctrl, Op, Var};

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum PathNode {
    Tag(Tag),
    Symbol(Symbol),
    Default,
}

impl std::fmt::Display for PathNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Tag(tag) => write!(f, "Tag({})", tag),
            Self::Symbol(symbol) => write!(f, "Symbol({})", symbol),
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
    pub fn push_symbol_inplace(&mut self, symbol: &Symbol) {
        self.0.push(PathNode::Symbol(symbol.clone()));
    }

    #[inline]
    pub fn push_default_inplace(&mut self) {
        self.0.push(PathNode::Default);
    }
}

#[inline]
fn insert_one(map: &mut VarMap<Var>, path: &Path, ptr: &Var) -> Result<Var> {
    let new_ptr = Var(format!("{}.{}", path, ptr.name()).into());
    map.insert(ptr.clone(), new_ptr.clone())?;
    Ok(new_ptr)
}

fn insert_many(map: &mut VarMap<Var>, path: &Path, ptrs: &[Var]) -> Result<Vec<Var>> {
    ptrs.iter().map(|ptr| insert_one(map, path, ptr)).collect()
}

impl Block {
    pub fn deconflict(
        &self,
        path: &Path,
        // `map` keeps track of the updated names of variables
        map: &mut VarMap<Var>, // name -> path.name
    ) -> Result<Self> {
        let mut ops = vec![];
        for op in &self.ops {
            match op {
                Op::Null(ptr, tag) => {
                    ops.push(Op::Null(insert_one(map, path, ptr)?, *tag))
                }
                Op::Hash2(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, img)?;
                    ops.push(Op::Hash2(img, *tag, preimg))
                }
                Op::Hash3(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, img)?;
                    ops.push(Op::Hash3(img, *tag, preimg))
                }
                Op::Hash4(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, img)?;
                    ops.push(Op::Hash4(img, *tag, preimg))
                }
                Op::Unhash2(preimg, img) => {
                    let img = map.get_cloned(img)?;
                    let preimg = insert_many(map, path, preimg)?;
                    ops.push(Op::Unhash2(preimg.try_into().unwrap(), img))
                }
                Op::Unhash3(preimg, img) => {
                    let img = map.get_cloned(img)?;
                    let preimg = insert_many(map, path, preimg)?;
                    ops.push(Op::Unhash3(preimg.try_into().unwrap(), img))
                }
                Op::Unhash4(preimg, img) => {
                    let img = map.get_cloned(img)?;
                    let preimg = insert_many(map, path, preimg)?;
                    ops.push(Op::Unhash4(preimg.try_into().unwrap(), img))
                }
                Op::Hide(..) => todo!(),
                Op::Open(..) => todo!(),
            }
        }
        let ctrl = self.ctrl.deconflict(path, map)?;
        Ok(Block{ ops, ctrl })

    }
}

impl Ctrl {
    /// Removes conflicting names in parallel logical LEM paths. While these
    /// conflicting names shouldn't be an issue for interpretation, they are
    /// problematic when we want to generate the constraints for the LEM, since
    /// conflicting names would cause different allocations to be bound the same
    /// name.
    ///
    /// The conflict resolution is achieved by changing variables so that
    /// their names are prepended by the paths where they're declared.
    ///
    /// Note: this function is not supposed to be called manually. It's used by
    /// `LEM::new`, which is the API that should be used directly.
    pub fn deconflict(
        &self,
        path: &Path,
        // `map` keeps track of the updated names of variables
        map: &mut VarMap<Var>, // name -> path.name
    ) -> Result<Self> {
        match self {
            Ctrl::MatchTag(var, cases) => {
                let mut new_cases = vec![];
                for (tag, case) in cases {
                    let new_case = case.deconflict(&path.push_tag(tag), &mut map.clone())?;
                    new_cases.push((*tag, new_case));
                }
                Ok(Ctrl::MatchTag(
                    map.get_cloned(var)?,
                    IndexMap::from_iter(new_cases),
                ))
            }
            Ctrl::MatchSymbol(var, cases, def) => {
                let mut new_cases = vec![];
                for (symbol, case) in cases {
                    let new_case = case.deconflict(&path.push_symbol(symbol), &mut map.clone())?;
                    new_cases.push((symbol.clone(), new_case));
                }
                Ok(Ctrl::MatchSymbol(
                    map.get_cloned(var)?,
                    IndexMap::from_iter(new_cases),
                    Box::new(def.deconflict(&path.push_default(), map)?),
                ))
            }
            Ctrl::Return(o) => Ok(Ctrl::Return(map.get_many_cloned(o)?)),
        }
    }

    /// Computes the number of possible paths in a `LEMOP`
    pub fn num_paths(&self) -> usize {
        match self {
            Ctrl::MatchTag(_, cases) => {
                cases.values().fold(0, |acc, block| acc + block.ctrl.num_paths())
            }
            Ctrl::MatchSymbol(_, cases, _) => {
                cases.values().fold(0, |acc, block| acc + block.ctrl.num_paths())
            }
            Ctrl::Return(..) => 1,
        }
    }

    /// Computes the number of paths taken within a `LEMOP` given a set of frames
    pub fn num_paths_taken(&self, paths: &[Path]) -> Result<usize> {
        let mut all_paths: HashSet<Path> = HashSet::default();
        paths.iter().for_each(|path| {
            all_paths.insert(path.clone());
        });
        Ok(all_paths.len())
    }
}
