use anyhow::{bail, Result};
use std::collections::{HashMap, HashSet};

use crate::field::LurkField;

use super::{interpreter::Frame, store::Store, tag::Tag, MetaPtr, LEMOP};

#[derive(Default, Clone, PartialEq, Eq, Hash)]
pub struct Path(String);

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Path {
    #[inline]
    pub fn push_tag(&self, tag: &Tag) -> Path {
        Path(format!("{self}.Tag({tag})"))
    }

    #[inline]
    pub fn push_sym_path(&self, sym_path: &[String]) -> Path {
        Path(format!("{self}.SymPath({})", sym_path.join(".")))
    }

    #[inline]
    pub fn push_default(&self) -> Path {
        Path(format!("{self}.Default"))
    }

    #[inline]
    pub fn push_tag_inplace(&mut self, tag: &Tag) {
        self.0 = format!("{self}.Tag({tag})");
    }

    #[inline]
    pub fn push_sym_path_inplace(&mut self, sym_path: &[String]) {
        self.0 = format!("{self}.SymPath({})", sym_path.join("."));
    }
}

impl LEMOP {
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
        map: &mut HashMap<String, String>, // name -> path/name
    ) -> Result<Self> {
        let insert_many =
            |map: &mut HashMap<String, String>, ptr: &[MetaPtr]| -> Result<Vec<MetaPtr>> {
                ptr.iter()
                    .map(|ptr| {
                        let new_name = format!("{}.{}", path, ptr.name());
                        if map.insert(ptr.name().clone(), new_name.clone()).is_some() {
                            bail!("{} already defined", ptr.name());
                        };
                        Ok(MetaPtr(new_name))
                    })
                    .collect::<Result<Vec<_>>>()
            };

        let insert_one = |map: &mut HashMap<String, String>, ptr: &MetaPtr| -> Result<MetaPtr> {
            let new_name = format!("{}.{}", path, ptr.name());
            if map.insert(ptr.name().clone(), new_name.clone()).is_some() {
                bail!("{} already defined", ptr.name());
            };
            Ok(MetaPtr(new_name))
        };

        let retrieve_many =
            |map: &HashMap<String, String>, args: &[MetaPtr]| -> Result<Vec<MetaPtr>> {
                args.iter()
                    .map(|ptr| {
                        let Some(src_path) = map.get(ptr.name()).cloned() else {
                        bail!("{} not defined", ptr.name());
                    };
                        Ok(MetaPtr(src_path))
                    })
                    .collect::<Result<Vec<_>>>()
            };

        let retrieve_one = |map: &HashMap<String, String>, ptr: &MetaPtr| -> Result<MetaPtr> {
            let Some(src_path) = map.get(ptr.name()).cloned() else {
                bail!("{} not defined", ptr.name());
            };
            Ok(MetaPtr(src_path))
        };

        match self {
            Self::Null(ptr, tag) => {
                let new_name = format!("{}.{}", path, ptr.name());
                if map.insert(ptr.name().clone(), new_name.clone()).is_some() {
                    bail!("{} already defined", ptr.name());
                };
                Ok(Self::Null(MetaPtr(new_name), *tag))
            }
            Self::Hash2(img, tag, preimg) => {
                let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                let img = insert_one(map, img)?;
                Ok(Self::Hash2(img, *tag, preimg))
            }
            Self::Hash3(img, tag, preimg) => {
                let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                let img = insert_one(map, img)?;
                Ok(Self::Hash3(img, *tag, preimg))
            }
            Self::Hash4(img, tag, preimg) => {
                let preimg = retrieve_many(map, preimg)?.try_into().unwrap();
                let img = insert_one(map, img)?;
                Ok(Self::Hash4(img, *tag, preimg))
            }
            LEMOP::Unhash2(preimg, img) => {
                let img = retrieve_one(map, img)?;
                let preimg = insert_many(map, preimg)?;
                Ok(Self::Unhash2(preimg.try_into().unwrap(), img))
            }
            LEMOP::Unhash3(preimg, img) => {
                let img = retrieve_one(map, img)?;
                let preimg = insert_many(map, preimg)?;
                Ok(Self::Unhash3(preimg.try_into().unwrap(), img))
            }
            LEMOP::Unhash4(preimg, img) => {
                let img = retrieve_one(map, img)?;
                let preimg = insert_many(map, preimg)?;
                Ok(Self::Unhash4(preimg.try_into().unwrap(), img))
            }
            LEMOP::MatchTag(ptr, cases) => {
                let mut new_cases = vec![];
                for (tag, case) in cases {
                    // each case needs it's own clone of `map`
                    let new_case = case.deconflict(&path.push_tag(tag), &mut map.clone())?;
                    new_cases.push((*tag, new_case));
                }
                Ok(LEMOP::MatchTag(
                    retrieve_one(map, ptr)?,
                    HashMap::from_iter(new_cases),
                ))
            }
            LEMOP::MatchSymPath(ptr, cases, def) => {
                let mut new_cases = vec![];
                for (sym_path, case) in cases {
                    // each case needs it's own clone of `map`
                    let new_case =
                        case.deconflict(&path.push_sym_path(sym_path), &mut map.clone())?;
                    new_cases.push((sym_path.clone(), new_case));
                }
                Ok(LEMOP::MatchSymPath(
                    retrieve_one(map, ptr)?,
                    HashMap::from_iter(new_cases),
                    Box::new(def.deconflict(&path.push_sym_path(&[]), &mut map.clone())?),
                ))
            }
            LEMOP::Seq(ops) => {
                let mut new_ops = vec![];
                for op in ops {
                    new_ops.push(op.deconflict(path, map)?);
                }
                Ok(LEMOP::Seq(new_ops))
            }
            LEMOP::Return(o) => Ok(LEMOP::Return(retrieve_many(map, o)?.try_into().unwrap())),
            _ => todo!(),
        }
    }

    /// Computes the number of possible paths in a `LEMOP`
    pub fn num_paths(&self) -> usize {
        macro_rules! mul_num_paths {
            ( $foldable_ops: expr ) => {
                $foldable_ops.fold(1, |acc, op| acc * op.num_paths())
            };
        }
        macro_rules! sum_num_paths {
            ( $foldable_ops: expr ) => {
                $foldable_ops.fold(0, |acc, op| acc + op.num_paths())
            };
        }
        match self {
            LEMOP::MatchTag(_, cases) => sum_num_paths!(cases.values()),
            LEMOP::MatchSymPath(_, cases, _) => sum_num_paths!(cases.values()),
            LEMOP::Seq(ops) => mul_num_paths!(ops.iter()),
            // It's safer to be exaustive here and avoid missing new LEMOPs
            Self::Null(..)
            | Self::Hash2(..)
            | Self::Hash3(..)
            | Self::Hash4(..)
            | Self::Unhash2(..)
            | Self::Unhash3(..)
            | Self::Unhash4(..)
            | Self::Hide(..)
            | Self::Open(..)
            | Self::Return(..) => 1,
        }
    }

    /// Computes the path taken through a `LEMOP` given a frame
    fn path_taken<F: LurkField>(&self, frame: &Frame<F>, store: &mut Store<F>) -> Result<Path> {
        let mut path = Path::default();
        let mut stack = vec![self];
        let ptrs = &frame.ptrs;
        while let Some(op) = stack.pop() {
            match op {
                Self::MatchTag(match_ptr, cases) => {
                    let ptr = match_ptr.get_ptr(ptrs)?;
                    let tag = ptr.tag();
                    let Some(op) = cases.get(tag) else {
                        bail!("No match for tag {}", tag)
                    };
                    path.push_tag_inplace(tag);
                    stack.push(op);
                }
                Self::MatchSymPath(match_ptr, cases, def) => {
                    let ptr = match_ptr.get_ptr(ptrs)?;
                    let Some(sym_path) = store.fetch_sym_path(ptr) else {
                        bail!("Symbol path not found for {}", match_ptr.name());
                    };
                    path.push_sym_path_inplace(sym_path);
                    match cases.get(sym_path) {
                        Some(op) => stack.push(op),
                        None => stack.push(def),
                    }
                }
                Self::Seq(ops) => stack.extend(ops.iter().rev()),
                // It's safer to be exaustive here and avoid missing new LEMOPs
                Self::Null(..)
                | Self::Hash2(..)
                | Self::Hash3(..)
                | Self::Hash4(..)
                | Self::Unhash2(..)
                | Self::Unhash3(..)
                | Self::Unhash4(..)
                | Self::Hide(..)
                | Self::Open(..)
                | Self::Return(..) => (),
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
