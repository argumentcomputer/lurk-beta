use crate::field::{FWrap, LurkField};
use anyhow::{bail, Result};

use super::{
    path::Path, pointers::Ptr, store::Store, tag::Tag, var_map::VarMap, Block, Ctrl, Func, Op,
};

#[derive(Clone, Default)]
pub struct Preimages<F: LurkField> {
    pub hash2_ptrs: Vec<Vec<Ptr<F>>>,
    pub hash3_ptrs: Vec<Vec<Ptr<F>>>,
    pub hash4_ptrs: Vec<Vec<Ptr<F>>>,
}

/// A `Frame` carries the data that results from interpreting a LEM. That is,
/// it contains the input, the output and all the assignments resulting from
/// running one iteration as a HashMap of variables to pointers.
///
/// This information is used to generate the witness.
#[derive(Clone)]
pub struct Frame<F: LurkField> {
    pub input: Vec<Ptr<F>>,
    pub output: Vec<Ptr<F>>,
    pub preimages: Preimages<F>,
}

impl Block {
    /// Interprets a LEM while i) modifying a `Store`, ii) binding `Var`s to
    /// `Ptr`s and iii) collecting the preimages from visited slots (more on this
    /// in `circuit.rs`)
    fn run_step<F: LurkField>(
        &self,
        input: Vec<Ptr<F>>,
        store: &mut Store<F>,
        mut bindings: VarMap<Ptr<F>>,
        mut preimages: Preimages<F>,
        path: Path,
    ) -> Result<(Frame<F>, Path)> {
        for op in &self.ops {
            match op {
                Op::Null(tgt, tag) => {
                    bindings.insert(tgt.clone(), Ptr::null(*tag));
                }
                Op::Hash2(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr = store.intern_2_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1]);
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages.hash2_ptrs.push(preimg_ptrs);
                }
                Op::Hash3(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr =
                        store.intern_3_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1], preimg_ptrs[2]);
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages.hash3_ptrs.push(preimg_ptrs);
                }
                Op::Hash4(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr = store.intern_4_ptrs(
                        *tag,
                        preimg_ptrs[0],
                        preimg_ptrs[1],
                        preimg_ptrs[2],
                        preimg_ptrs[3],
                    );
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages.hash4_ptrs.push(preimg_ptrs);
                }
                Op::Unhash2(preimg, img) => {
                    let img_ptr = bindings.get(img)?;
                    let Some(idx) = img_ptr.get_index2() else {
                        bail!("{img} isn't a Tree2 pointer");
                    };
                    let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    let preimg_ptrs = [*a, *b];
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert(var.clone(), *ptr);
                    }
                    preimages.hash2_ptrs.push(preimg_ptrs.to_vec());
                }
                Op::Unhash3(preimg, img) => {
                    let img_ptr = bindings.get(img)?;
                    let Some(idx) = img_ptr.get_index3() else {
                        bail!("{img} isn't a Tree3 pointer");
                    };
                    let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    let preimg_ptrs = [*a, *b, *c];
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert(var.clone(), *ptr);
                    }
                    preimages.hash3_ptrs.push(preimg_ptrs.to_vec());
                }
                Op::Unhash4(preimg, img) => {
                    let img_ptr = bindings.get(img)?;
                    let Some(idx) = img_ptr.get_index4() else {
                        bail!("{img} isn't a Tree4 pointer");
                    };
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    let preimg_ptrs = [*a, *b, *c, *d];
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert(var.clone(), *ptr);
                    }
                    preimages.hash4_ptrs.push(preimg_ptrs.to_vec());
                }
                Op::Hide(tgt, sec, src) => {
                    let src_ptr = bindings.get(src)?;
                    let Ptr::Leaf(Tag::Num, secret) = bindings.get(sec)? else {
                        bail!("{sec} is not a numeric pointer")
                    };
                    let z_ptr = store.hash_ptr(src_ptr)?;
                    let hash =
                        store
                            .poseidon_cache
                            .hash3(&[*secret, z_ptr.tag.to_field(), z_ptr.hash]);
                    let tgt_ptr = Ptr::comm(hash);
                    store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                    bindings.insert(tgt.clone(), tgt_ptr);
                }
                Op::Open(tgt_secret, tgt_ptr, comm_or_num) => match bindings.get(comm_or_num)? {
                    Ptr::Leaf(Tag::Num, hash) | Ptr::Leaf(Tag::Comm, hash) => {
                        let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                            bail!("No committed data for hash {}", &hash.hex_digits())
                        };
                        bindings.insert(tgt_ptr.clone(), *ptr);
                        bindings.insert(tgt_secret.clone(), Ptr::Leaf(Tag::Num, *secret));
                    }
                    _ => {
                        bail!("{comm_or_num} is not a num/comm pointer")
                    }
                },
            }
        }
        self.ctrl.run_step(input, store, bindings, preimages, path)
    }
}

impl Ctrl {
    /// Interprets a LEM while i) modifying a `Store`, ii) binding `Var`s to
    /// `Ptr`s and iii) collecting the preimages from visited slots (more on this
    /// in `circuit.rs`)
    fn run_step<F: LurkField>(
        &self,
        input: Vec<Ptr<F>>,
        store: &mut Store<F>,
        bindings: VarMap<Ptr<F>>,
        preimages: Preimages<F>,
        mut path: Path,
    ) -> Result<(Frame<F>, Path)> {
        match self {
            Ctrl::MatchTag(match_var, cases) => {
                let ptr = bindings.get(match_var)?;
                let tag = ptr.tag();
                match cases.get(tag) {
                    Some(block) => {
                        path.push_tag_inplace(tag);
                        block.run_step(input, store, bindings, preimages, path)
                    }
                    None => bail!("No match for tag {}", tag),
                }
            }
            Ctrl::MatchSymbol(match_var, cases, def) => {
                let ptr = bindings.get(match_var)?;
                let Some(symbol) = store.fetch_symbol(ptr) else {
                    bail!("Symbol not found for {match_var}");
                };
                match cases.get(&symbol) {
                    Some(block) => {
                        path.push_symbol_inplace(&symbol);
                        block.run_step(input, store, bindings, preimages, path)
                    }
                    None => {
                        path.push_default_inplace();
                        def.run_step(input, store, bindings, preimages, path)
                    }
                }
            }
            Ctrl::Return(output_vars) => {
                let mut output = Vec::with_capacity(output_vars.len());
                for var in output_vars.iter() {
                    output.push(*bindings.get(var)?)
                }
                Ok((
                    Frame {
                        input,
                        output,
                        preimages,
                    },
                    path,
                ))
            }
        }
    }
}

impl Func {
    /// Calls `run_step` until the stop contidion is satisfied, using the output of one
    /// iteration as the input of the next one.
    pub fn run<F: LurkField, Stop: Fn(&[Ptr<F>]) -> bool>(
        &self,
        mut input: Vec<Ptr<F>>,
        store: &mut Store<F>,
        stop_cond: Stop,
    ) -> Result<(Vec<Frame<F>>, Vec<Path>)> {
        if self.input_vars.len() != self.output_size {
            bail!(
                "Function's input size {} is different from its output size {}",
                self.input_vars.len(),
                self.output_size
            )
        }
        if self.input_vars.len() != input.len() {
            bail!(
                "The number of inputs {} differs from the function's input size {}",
                input.len(),
                self.input_vars.len()
            )
        }

        // Initial path vector and frames
        let mut frames = vec![];
        let mut paths = vec![];

        loop {
            // Map of names to pointers (its key/val pairs should never be overwritten)
            let mut bindings = VarMap::new();
            for (i, var) in self.input_vars.iter().enumerate() {
                bindings.insert(var.clone(), input[i]);
            }

            let preimages = Preimages::default();
            let (frame, path) =
                self.block
                    .run_step(input, store, bindings, preimages, Path::default())?;
            if stop_cond(&frame.output) {
                frames.push(frame);
                paths.push(path);
                break;
            }
            // Should frames take borrowed vectors instead, as to avoid cloning?
            // Using AVec is a possibility, but to create a dynamic AVec, currently,
            // requires 2 allocations since it must be created from a Vec and
            // Vec<T> -> Arc<[T]> uses `copy_from_slice`.
            input = frame.output.clone();
            frames.push(frame);
            paths.push(path);
        }
        Ok((frames, paths))
    }
}
