use anyhow::Result;
use indexmap::IndexMap;
use std::collections::HashSet;

use super::{symbol::Symbol, tag::Tag, var_map::VarMap, Block, Ctrl, Func, Op, Var};

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

    /// Computes the number of different paths taken given a list of paths
    pub fn num_paths_taken(paths: &[Self]) -> usize {
        let mut all_paths: HashSet<Self> = HashSet::default();
        paths.iter().for_each(|path| {
            all_paths.insert(path.clone());
        });
        all_paths.len()
    }
}

#[inline]
fn insert_one(map: &mut VarMap<Var>, path: &Path, ptr: &Var) -> Var {
    let new_ptr = Var(format!("{}.{}", path, ptr.name()).into());
    map.insert(ptr.clone(), new_ptr.clone());
    new_ptr
}

fn insert_many(map: &mut VarMap<Var>, path: &Path, ptrs: &[Var]) -> Vec<Var> {
    ptrs.iter().map(|ptr| insert_one(map, path, ptr)).collect()
}

impl Block {
    fn deconflict(
        self,
        path: &Path,
        // `map` keeps track of the updated names of variables
        map: &mut VarMap<Var>, // name -> path.name
    ) -> Result<Self> {
        let mut ops = Vec::with_capacity(self.ops.len());
        for op in self.ops {
            match op {
                Op::Call(out, func, inp) => {
                    let out = map.get_many_cloned(&out)?;
                    let inp = map.get_many_cloned(&inp)?;
                    // We will always assume previously defined `Func`s to already be deconflicted.
                    // As of now, we won't deconflict the inner variables of the `func`.
                    // See the comment in the `Op::Call` case of `synthesize` in circuit.rs
                    ops.push(Op::Call(out, func, inp))
                }
                Op::Null(ptr, tag) => ops.push(Op::Null(insert_one(map, path, &ptr), tag)),
                Op::Hash2(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, &img);
                    ops.push(Op::Hash2(img, tag, preimg))
                }
                Op::Hash3(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, &img);
                    ops.push(Op::Hash3(img, tag, preimg))
                }
                Op::Hash4(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, &img);
                    ops.push(Op::Hash4(img, tag, preimg))
                }
                Op::Unhash2(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, path, &preimg);
                    ops.push(Op::Unhash2(preimg.try_into().unwrap(), img))
                }
                Op::Unhash3(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, path, &preimg);
                    ops.push(Op::Unhash3(preimg.try_into().unwrap(), img))
                }
                Op::Unhash4(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, path, &preimg);
                    ops.push(Op::Unhash4(preimg.try_into().unwrap(), img))
                }
                Op::Hide(..) => todo!(),
                Op::Open(..) => todo!(),
            }
        }
        let ctrl = match self.ctrl {
            Ctrl::MatchTag(var, cases) => {
                let mut new_cases = Vec::with_capacity(cases.len());
                for (tag, case) in cases {
                    let new_case = case.deconflict(&path.push_tag(&tag), &mut map.clone())?;
                    new_cases.push((tag, new_case));
                }
                Ctrl::MatchTag(map.get_cloned(&var)?, IndexMap::from_iter(new_cases))
            }
            Ctrl::MatchSymbol(var, cases, def) => {
                let mut new_cases = Vec::with_capacity(cases.len());
                for (symbol, case) in cases {
                    let new_case = case.deconflict(&path.push_symbol(&symbol), &mut map.clone())?;
                    new_cases.push((symbol.clone(), new_case));
                }
                Ctrl::MatchSymbol(
                    map.get_cloned(&var)?,
                    IndexMap::from_iter(new_cases),
                    Box::new(def.deconflict(&path.push_default(), map)?),
                )
            }
            Ctrl::Return(o) => Ctrl::Return(map.get_many_cloned(&o)?),
        };
        Ok(Block { ops, ctrl })
    }

    /// Computes the number of possible paths in a `Block`. `Func`s withen `Call`s are
    /// treated as black boxes, therefore we do not count paths within a call.
    fn num_paths(&self) -> usize {
        match &self.ctrl {
            Ctrl::MatchTag(_, cases) => {
                cases.values().fold(0, |acc, block| acc + block.num_paths())
            }
            Ctrl::MatchSymbol(_, cases, def) => cases
                .values()
                .fold(def.num_paths(), |acc, block| acc + block.num_paths()),
            Ctrl::Return(..) => 1,
        }
    }
}

// impl Ctrl {
//     fn deconflict(
//         self,
//         path: &Path,
//         // `map` keeps track of the updated names of variables
//         map: &mut VarMap<Var>, // name -> path.name
//     ) -> Result<Self> {
//     }
// }

impl Func {
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
    pub(crate) fn deconflict(mut self) -> Result<Self> {
        let mut map = VarMap::new();
        for i in self.input_params.iter() {
            map.insert(i.clone(), i.clone());
        }
        self.block = self.block.deconflict(&Path::default(), &mut map)?;
        Ok(self)
    }

    /// Asserts that all paths were visited by a set of frames. This is mostly
    /// for testing purposes.
    pub fn assert_all_paths_taken(&self, paths: &[Path]) {
        assert_eq!(Path::num_paths_taken(paths), self.block.num_paths());
    }
}
