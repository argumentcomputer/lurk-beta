use crate::field::{FWrap, LurkField};
use anyhow::{bail, Result};

use super::{
    path::Path, pointers::Ptr, store::Store, symbol::Symbol, tag::Tag, var_map::VarMap, Var, LEM,
    LEMCTL, LEMOP,
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
/// This information is used to generte the witness.
#[derive(Clone)]
pub struct Frame<F: LurkField> {
    pub input: [Ptr<F>; 3],
    pub output: [Ptr<F>; 3],
    pub preimages: Preimages<F>,
}

fn retrieve_many<F: LurkField>(map: &VarMap<Ptr<F>>, args: &[Var]) -> Vec<Ptr<F>> {
    args.iter().map(|var| *map.get(var)).collect::<Vec<_>>()
}

impl LEMOP {
    fn run<F: LurkField>(
        &self,
        store: &mut Store<F>,
        bindings: &mut VarMap<Ptr<F>>,
        preimages: &mut Preimages<F>,
    ) -> Result<()> {
        match self {
            LEMOP::Null(tgt, tag) => {
                bindings.insert(tgt.clone(), Ptr::null(*tag));
                Ok(())
            }
            LEMOP::Hash2(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(bindings, preimg);
                let tgt_ptr = store.intern_2_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1]);
                bindings.insert(img.clone(), tgt_ptr);
                preimages.hash2_ptrs.push(preimg_ptrs);
                Ok(())
            }
            LEMOP::Hash3(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(bindings, preimg);
                let tgt_ptr =
                    store.intern_3_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1], preimg_ptrs[2]);
                bindings.insert(img.clone(), tgt_ptr);
                preimages.hash3_ptrs.push(preimg_ptrs);
                Ok(())
            }
            LEMOP::Hash4(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(bindings, preimg);
                let tgt_ptr = store.intern_4_ptrs(
                    *tag,
                    preimg_ptrs[0],
                    preimg_ptrs[1],
                    preimg_ptrs[2],
                    preimg_ptrs[3],
                );
                bindings.insert(img.clone(), tgt_ptr);
                preimages.hash4_ptrs.push(preimg_ptrs);
                Ok(())
            }
            LEMOP::Unhash2(preimg, img) => {
                let img_ptr = bindings.get(img);
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
                Ok(())
            }
            LEMOP::Unhash3(preimg, img) => {
                let img_ptr = bindings.get(img);
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
                Ok(())
            }
            LEMOP::Unhash4(preimg, img) => {
                let img_ptr = bindings.get(img);
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
                Ok(())
            }
            LEMOP::Hide(tgt, sec, src) => {
                let src_ptr = bindings.get(src);
                let Ptr::Leaf(Tag::Num, secret) = bindings.get(sec) else {
                    bail!("{sec} is not a numeric pointer")
                };
                let z_ptr = store.hash_ptr(src_ptr)?;
                let hash = store
                    .poseidon_cache
                    .hash3(&[*secret, z_ptr.tag.to_field(), z_ptr.hash]);
                let tgt_ptr = Ptr::comm(hash);
                store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                bindings.insert(tgt.clone(), tgt_ptr);
                Ok(())
            }
            LEMOP::Open(tgt_secret, tgt_ptr, comm_or_num) => match bindings.get(comm_or_num) {
                Ptr::Leaf(Tag::Num, hash) | Ptr::Leaf(Tag::Comm, hash) => {
                    let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                            bail!("No committed data for hash {}", &hash.hex_digits())
                        };
                    bindings.insert(tgt_ptr.clone(), *ptr);
                    bindings.insert(tgt_secret.clone(), Ptr::Leaf(Tag::Num, *secret));
                    Ok(())
                }
                _ => {
                    bail!("{comm_or_num} is not a num/comm pointer")
                }
            },
        }
    }
}

impl LEMCTL {
    /// Interprets a LEM while i) modifying a `Store`, ii) binding `Var`s to
    /// `Ptr`s and iii) collecting the preimages from visited slots (more on this
    /// in `circuit.rs`)
    fn run<F: LurkField>(
        &self,
        input: [Ptr<F>; 3],
        store: &mut Store<F>,
        mut bindings: VarMap<Ptr<F>>,
        mut preimages: Preimages<F>,
        mut path: Path,
    ) -> Result<(Frame<F>, Path)> {
        match self {
            LEMCTL::MatchTag(match_var, cases) => {
                let ptr = bindings.get(match_var);
                let tag = ptr.tag();
                match cases.get(tag) {
                    Some(ctl) => {
                        path.push_tag_inplace(tag);
                        ctl.run(input, store, bindings, preimages, path)
                    }
                    None => bail!("No match for tag {}", tag),
                }
            }
            LEMCTL::MatchSymbol(match_var, cases, def) => {
                let ptr = bindings.get(match_var);
                let Some(symbol) = store.fetch_symbol(ptr) else {
                    bail!("Symbol not found for {match_var}");
                };
                match cases.get(&symbol) {
                    Some(ctl) => {
                        path.push_symbol_inplace(&symbol);
                        ctl.run(input, store, bindings, preimages, path)
                    }
                    None => {
                        path.push_default_inplace();
                        def.run(input, store, bindings, preimages, path)
                    }
                }
            }
            LEMCTL::Seq(ops, rest) => {
                for op in ops {
                    op.run(store, &mut bindings, &mut preimages)?;
                }
                rest.run(input, store, bindings, preimages, path)
            }
            LEMCTL::Return(o) => {
                let output = [
                    *bindings.get(&o[0]),
                    *bindings.get(&o[1]),
                    *bindings.get(&o[2]),
                ];
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

impl LEM {
    /// Calls `run` until the stop contidion is satisfied, using the output of one
    /// iteration as the input of the next one.
    pub fn eval<F: LurkField>(
        &self,
        expr: Ptr<F>,
        store: &mut Store<F>,
    ) -> Result<(Vec<Frame<F>>, Vec<Path>)> {
        // Lurk constants
        let outermost = Ptr::null(Tag::Outermost);
        let terminal = &Ptr::null(Tag::Terminal);
        let error = &Ptr::null(Tag::Error);
        let nil = store.intern_symbol(&Symbol::lurk_sym("nil"));

        // Initial input and initial frames
        let mut input = [expr, nil, outermost];
        let mut frames = vec![];
        let mut paths = vec![];

        loop {
            // Map of names to pointers (its key/val pairs should never be overwritten)
            let mut bindings = VarMap::new();
            for (i, var) in self.input_vars.iter().enumerate() {
                bindings.insert(var.clone(), input[i]);
            }

            let preimages = Preimages::default();
            let (frame, path) = self
                .ctl
                .run(input, store, bindings, preimages, Path::default())?;
            if &frame.output[2] == terminal || &frame.output[2] == error {
                frames.push(frame);
                paths.push(path);
                break;
            }
            input = frame.output;
            frames.push(frame);
            paths.push(path);
        }
        Ok((frames, paths))
    }
}
