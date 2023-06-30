use anyhow::{bail, Result};
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

use crate::field::LurkField;

use super::{interpreter::Frame, symbol::Symbol, tag::Tag, Var, LEMCTL, LEMOP};

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

fn insert_one(map: &mut HashMap<Var, Var>, path: &Path, ptr: &Var) -> Result<Var> {
    let new_ptr = Var(format!("{}.{}", path, ptr.name()).into());
    if map.insert(ptr.clone(), new_ptr.clone()).is_some() {
        bail!("{} already defined", ptr.name());
    };
    Ok(new_ptr)
}

fn insert_many(map: &mut HashMap<Var, Var>, path: &Path, ptr: &[Var]) -> Result<Vec<Var>> {
    ptr.iter()
        .map(|ptr| insert_one(map, path, ptr))
        .collect::<Result<Vec<_>>>()
}

fn retrieve_one(map: &HashMap<Var, Var>, ptr: &Var) -> Result<Var> {
    let Some(new_ptr) = map.get(ptr).cloned() else {
        bail!("{} not defined", ptr.name());
    };
    Ok(new_ptr)
}

fn retrieve_many(map: &HashMap<Var, Var>, args: &[Var]) -> Result<Vec<Var>> {
    args.iter()
        .map(|ptr| retrieve_one(map, ptr))
        .collect::<Result<Vec<_>>>()
}

impl LEMCTL {
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
        map: &mut HashMap<Var, Var>, // name -> path.name
    ) -> Result<Self> {
        match self {
            LEMCTL::MatchTag(var, cases) => {
                let mut new_cases = vec![];
                for (tag, case) in cases {
                    let new_case = case.deconflict(&path.push_tag(tag), &mut map.clone())?;
                    new_cases.push((*tag, new_case));
                }
                Ok(LEMCTL::MatchTag(
                    retrieve_one(map, var)?,
                    IndexMap::from_iter(new_cases),
                ))
            }
            LEMCTL::MatchSymbol(var, cases, def) => {
                let mut new_cases = vec![];
                for (symbol, case) in cases {
                    let new_case = case.deconflict(&path.push_symbol(symbol), &mut map.clone())?;
                    new_cases.push((symbol.clone(), new_case));
                }
                Ok(LEMCTL::MatchSymbol(
                    retrieve_one(map, var)?,
                    IndexMap::from_iter(new_cases),
                    Box::new(def.deconflict(&path.push_default(), &mut map.clone())?),
                ))
            }
            LEMCTL::Seq(ops, rest) => {
                let mut new_ops = vec![];
                for op in ops {
                    match op {
                        LEMOP::Null(ptr, tag) => {
                            new_ops.push(LEMOP::Null(insert_one(map, path, ptr)?, *tag))
                        }
                        LEMOP::Hash2(img, tag, preimg) => {
                            let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                            let img = insert_one(map, path, img)?;
                            new_ops.push(LEMOP::Hash2(img, *tag, preimg))
                        }
                        LEMOP::Hash3(img, tag, preimg) => {
                            let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                            let img = insert_one(map, path, img)?;
                            new_ops.push(LEMOP::Hash3(img, *tag, preimg))
                        }
                        LEMOP::Hash4(img, tag, preimg) => {
                            let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                            let img = insert_one(map, path, img)?;
                            new_ops.push(LEMOP::Hash4(img, *tag, preimg))
                        }
                        LEMOP::Unhash2(preimg, img) => {
                            let img = retrieve_one(map, img)?;
                            let preimg = insert_many(map, path, preimg)?;
                            new_ops.push(LEMOP::Unhash2(preimg.try_into().unwrap(), img))
                        }
                        LEMOP::Unhash3(preimg, img) => {
                            let img = retrieve_one(map, img)?;
                            let preimg = insert_many(map, path, preimg)?;
                            new_ops.push(LEMOP::Unhash3(preimg.try_into().unwrap(), img))
                        }
                        LEMOP::Unhash4(preimg, img) => {
                            let img = retrieve_one(map, img)?;
                            let preimg = insert_many(map, path, preimg)?;
                            new_ops.push(LEMOP::Unhash4(preimg.try_into().unwrap(), img))
                        }
                        LEMOP::Hide(..) => todo!(),
                        LEMOP::Open(..) => todo!(),
                    }
                }
                let new_rest = Box::new(rest.deconflict(path, map)?);
                Ok(LEMCTL::Seq(new_ops, new_rest))
            }
            LEMCTL::Return(o) => Ok(LEMCTL::Return(retrieve_many(map, o)?.try_into().unwrap())),
        }
    }

    /// Computes the number of possible paths in a `LEMOP`
    pub fn num_paths(&self) -> usize {
        match self {
            LEMCTL::MatchTag(_, cases) => {
                cases.values().fold(0, |acc, block| acc + block.num_paths())
            }
            LEMCTL::MatchSymbol(_, cases, _) => {
                cases.values().fold(0, |acc, block| acc + block.num_paths())
            }
            LEMCTL::Seq(_, rest) => rest.num_paths(),
            LEMCTL::Return(..) => 1,
        }
    }

    /// Computes the number of paths taken within a `LEMOP` given a set of frames
    pub fn num_paths_taken<F: LurkField>(&self, frames: &[Frame<F>]) -> Result<usize> {
        let mut all_paths: HashSet<Path> = HashSet::default();
        frames.iter().for_each(|frame| {
            all_paths.insert(frame.path.clone());
        });
        Ok(all_paths.len())
    }
}
