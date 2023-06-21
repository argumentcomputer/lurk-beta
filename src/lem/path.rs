use anyhow::{bail, Result};
use std::collections::{HashMap, HashSet};

use crate::field::LurkField;

use super::{interpreter::Frame, store::Store, symbol::Symbol, tag::Tag, MetaPtr, LEMCTL, LEMOP, AString};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Path(AString);
impl Default for Path {
    fn default() -> Self { Path("".into()) }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Path {
    #[inline]
    pub fn push_tag(&self, tag: &Tag) -> Path {
        Path(format!("{self}.Tag({tag})").into())
    }

    #[inline]
    pub fn push_symbol(&self, symbol: &Symbol) -> Path {
        Path(format!("{self}.Symbol({symbol})").into())
    }

    #[inline]
    pub fn push_default(&self) -> Path {
        Path(format!("{self}.Default").into())
    }

    #[inline]
    pub fn push_tag_inplace(&mut self, tag: &Tag) {
        self.0 = format!("{self}.Tag({tag})").into();
    }

    #[inline]
    pub fn push_symbol_inplace(&mut self, symbol: &Symbol) {
        self.0 = format!("{self}.Symbol({symbol})").into();
    }
}

impl LEMCTL {
    /// Removes conflicting names in parallel logical LEM paths. While these
    /// conflicting names shouldn't be an issue for interpretation, they are
    /// problematic when we want to generate the constraints for the LEM, since
    /// conflicting names would cause different allocations to be bound the same
    /// name.
    ///
    /// The conflict resolution is achieved by changing meta pointers so that
    /// their names are prepended by the paths where they're declared.
    ///
    /// Note: this function is not supposed to be called manually. It's used by
    /// `LEM::new`, which is the API that should be used directly.
    pub fn deconflict(
        &self,
        path: &Path,
        map: &mut HashMap<AString, AString>, // name -> path/name
    ) -> Result<Self> {
        fn insert_many(map: &mut HashMap<AString, AString>, path: &str, ptr: &[MetaPtr]) -> Result<Vec<MetaPtr>> {
            ptr.iter()
                .map(|ptr| {
                    let new_name: AString = format!("{}.{}", path, ptr.name()).into();
                    if map.insert(ptr.name().clone(), new_name.clone()).is_some() {
                        bail!("{} already defined", ptr.name());
                    };
                    Ok(MetaPtr(new_name))
                })
                .collect::<Result<Vec<_>>>()
        }

        fn insert_one(map: &mut HashMap<AString, AString>, path: &str, ptr: &MetaPtr) -> Result<MetaPtr> {
            let new_name: AString = format!("{}.{}", path, ptr.name()).into();
            if map.insert(ptr.name().clone(), new_name.clone()).is_some() {
                bail!("{} already defined", ptr.name());
            };
            Ok(MetaPtr(new_name))
        }

        fn retrieve_many(map: &HashMap<AString, AString>, args: &[MetaPtr]) -> Result<Vec<MetaPtr>> {
            args.iter()
                .map(|ptr| {
                    let Some(src_path) = map.get(ptr.name()).cloned() else {
                        bail!("{} not defined", ptr.name());
                    };
                    Ok(MetaPtr(src_path))
                })
                .collect::<Result<Vec<_>>>()
        }

        fn retrieve_one(map: &HashMap<AString, AString>, ptr: &MetaPtr) -> Result<MetaPtr> {
            let Some(src_path) = map.get(ptr.name()).cloned() else {
                bail!("{} not defined", ptr.name());
            };
            Ok(MetaPtr(src_path))
        }

        fn deconflict_op(map: &mut HashMap<AString, AString>, path: &str, op: &LEMOP) -> Result<LEMOP> {
            match op {
                LEMOP::Null(ptr, tag) => {
                    let new_name: AString = format!("{}.{}", path, ptr.name()).into();
                    if map.insert(ptr.name().clone(), new_name.clone()).is_some() {
                        bail!("{} already defined", ptr.name());
                    };
                    Ok(LEMOP::Null(MetaPtr(new_name), *tag))
                }
                LEMOP::Hash2(img, tag, preimg) => {
                    let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, img)?;
                    Ok(LEMOP::Hash2(img, *tag, preimg))
                }
                LEMOP::Hash3(img, tag, preimg) => {
                    let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, img)?;
                    Ok(LEMOP::Hash3(img, *tag, preimg))
                }
                LEMOP::Hash4(img, tag, preimg) => {
                    let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                    let img = insert_one(map, path, img)?;
                    Ok(LEMOP::Hash4(img, *tag, preimg))
                }
                LEMOP::Unhash2(preimg, img) => {
                    let img = retrieve_one(map, img)?;
                    let preimg = insert_many(map, path, preimg)?;
                    Ok(LEMOP::Unhash2(preimg.try_into().unwrap(), img))
                }
                LEMOP::Unhash3(preimg, img) => {
                    let img = retrieve_one(map, img)?;
                    let preimg = insert_many(map, path, preimg)?;
                    Ok(LEMOP::Unhash3(preimg.try_into().unwrap(), img))
                }
                LEMOP::Unhash4(preimg, img) => {
                    let img = retrieve_one(map, img)?;
                    let preimg = insert_many(map, path, preimg)?;
                    Ok(LEMOP::Unhash4(preimg.try_into().unwrap(), img))
                }
                LEMOP::Hide(..) => todo!(),
                LEMOP::Open(..) => todo!(),
            }
        }

        match self {
            LEMCTL::MatchTag(ptr, cases) => {
                let mut new_cases = vec![];
                for (tag, case) in cases {
                    let new_case = case.deconflict(&path.push_tag(tag), &mut map.clone())?;
                    new_cases.push((*tag, new_case));
                }
                Ok(LEMCTL::MatchTag(
                    retrieve_one(map, ptr)?,
                    HashMap::from_iter(new_cases),
                ))
            }
            LEMCTL::MatchSymbol(ptr, cases, def) => {
                let mut new_cases = vec![];
                for (symbol, case) in cases {
                    let new_case =
                        case.deconflict(&path.push_symbol(symbol), &mut map.clone())?;
                    new_cases.push((symbol.clone(), new_case));
                }
                Ok(LEMCTL::MatchSymbol(
                    retrieve_one(map, ptr)?,
                    HashMap::from_iter(new_cases),
                    Box::new(def.deconflict(&path.push_default(), &mut map.clone())?),
                ))
            }
            LEMCTL::Seq(op, rest) => {
                let new_op = deconflict_op(map, &path.0, op)?;
                let new_rest = Box::new(rest.deconflict(path, map)?);
                Ok(LEMCTL::Seq(new_op, new_rest))
            }
            LEMCTL::Return(o) => Ok(LEMCTL::Return(retrieve_many(map, o)?.try_into().unwrap())),
        }
    }

    /// Computes the number of possible paths in a `LEMOP`
    pub fn num_paths(&self) -> usize {
        match self {
            LEMCTL::MatchTag(_, cases) => cases.values().fold(0, |acc, code| acc + code.num_paths()),
            LEMCTL::MatchSymbol(_, cases, _) => cases.values().fold(0, |acc, code| acc + code.num_paths()),
            LEMCTL::Seq(_, rest) => rest.num_paths(),
            LEMCTL::Return(..) => 1,
       }
    }

    /// Computes the path taken through a `LEMOP` given a frame
    fn path_taken<F: LurkField>(&self, frame: &Frame<F>, store: &mut Store<F>) -> Result<Path> {
        let mut path = Path::default();
        let mut stack = vec![self];
        let binds = &frame.binds;
        while let Some(code) = stack.pop() {
            match code {
                Self::MatchTag(match_ptr, cases) => {
                    let ptr = match_ptr.get_ptr(binds)?;
                    let tag = ptr.tag();
                    let Some(code) = cases.get(tag) else {
                        bail!("No match for tag {}", tag)
                    };
                    path.push_tag_inplace(tag);
                    stack.push(code);
                }
                Self::MatchSymbol(match_ptr, cases, def) => {
                    let ptr = match_ptr.get_ptr(binds)?;
                    let Some(symbol) = store.fetch_symbol(ptr) else {
                        bail!("Symbol not found for {}", match_ptr.name());
                    };
                    path.push_symbol_inplace(&symbol);
                    match cases.get(&symbol) {
                        Some(code) => stack.push(code),
                        None => stack.push(def),
                    }
                }
                Self::Seq(_, rest) => stack.push(rest),
                Self::Return(..) => (),
            }
        }
        Ok(path)
    }

    /// Computes the number of paths taken within a `LEMOP` given a set of frames
    pub fn num_paths_taken<F: LurkField>(
        &self,
        frames: &Vec<Frame<F>>,
        store: &mut Store<F>,
    ) -> Result<usize> {
        let mut all_paths: HashSet<Path> = HashSet::default();
        for frame in frames {
            all_paths.insert(self.path_taken(frame, store)?);
        }
        Ok(all_paths.len())
    }
}
