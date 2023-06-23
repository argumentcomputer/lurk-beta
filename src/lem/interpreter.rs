use crate::field::{FWrap, LurkField};
use anyhow::{bail, Result};
use std::collections::HashMap;

use super::{pointers::Ptr, store::Store, symbol::Symbol, tag::Tag, MetaPtr, LEM, LEMCTL, LEMOP};

#[derive(Clone, Default)]
pub struct Preimages<F: LurkField> {
    pub hash2: Vec<Vec<Ptr<F>>>,
    pub hash3: Vec<Vec<Ptr<F>>>,
    pub hash4: Vec<Vec<Ptr<F>>>,
}

/// A `Frame` carries the data that results from interpreting a LEM. That is,
/// it contains the input, the output and all the assignments resulting from
/// running one iteration as a HashMap of meta pointers to pointers.
///
/// Finally, `preimages` contains the data collected from visiting the slots.
/// This information is used to generte the witness.
#[derive(Clone)]
pub struct Frame<F: LurkField> {
    pub input: [Ptr<F>; 3],
    pub output: [Ptr<F>; 3],
    pub bindings: HashMap<MetaPtr, Ptr<F>>,
    pub preimages: Preimages<F>,
}

fn retrieve_many<F: LurkField>(
    map: &HashMap<MetaPtr, Ptr<F>>,
    args: &[MetaPtr],
) -> Result<Vec<Ptr<F>>> {
    args.iter()
        .map(|mptr| {
            let Some(ptr) = map.get(mptr).cloned() else {
                bail!("{} not defined", mptr.name());
            };
            Ok(ptr)
        })
        .collect::<Result<Vec<_>>>()
}

#[inline(always)]
fn bind<F: LurkField>(
    bindings: &mut HashMap<MetaPtr, Ptr<F>>,
    mptr: MetaPtr,
    ptr: Ptr<F>,
) -> Result<()> {
    if bindings.insert(mptr.clone(), ptr).is_some() {
        bail!("{} already defined", mptr)
    }
    Ok(())
}

impl LEMOP {
    fn run<F: LurkField>(
        &self,
        store: &mut Store<F>,
        bindings: &mut HashMap<MetaPtr, Ptr<F>>,
        preimages: &mut Preimages<F>,
    ) -> Result<()> {
        match self {
            LEMOP::Null(tgt, tag) => {
                let tgt_ptr = Ptr::null(*tag);
                bind(bindings, tgt.clone(), tgt_ptr)
            }
            LEMOP::Hash2(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(bindings, preimg)?;
                let tgt_ptr = store.intern_2_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1]);
                bind(bindings, img.clone(), tgt_ptr)?;
                preimages.hash2.push(preimg_ptrs);
                Ok(())
            }
            LEMOP::Hash3(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(bindings, preimg)?;
                let tgt_ptr =
                    store.intern_3_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1], preimg_ptrs[2]);
                bind(bindings, img.clone(), tgt_ptr)?;
                preimages.hash3.push(preimg_ptrs);
                Ok(())
            }
            LEMOP::Hash4(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(bindings, preimg)?;
                let tgt_ptr = store.intern_4_ptrs(
                    *tag,
                    preimg_ptrs[0],
                    preimg_ptrs[1],
                    preimg_ptrs[2],
                    preimg_ptrs[3],
                );
                bind(bindings, img.clone(), tgt_ptr)?;
                preimages.hash4.push(preimg_ptrs);
                Ok(())
            }
            LEMOP::Unhash2(preimg, img) => {
                let img_ptr = img.get_ptr(bindings)?;
                let Some(idx) = img_ptr.get_index2() else {
                    bail!("{img} isn't a Tree2 pointer");
                };
                let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                let vec = [*a, *b];
                for (mptr, ptr) in preimg.iter().zip(vec.iter()) {
                    bind(bindings, mptr.clone(), *ptr)?;
                }
                preimages.hash2.push(vec.to_vec());
                Ok(())
            }
            LEMOP::Unhash3(preimg, img) => {
                let img_ptr = img.get_ptr(bindings)?;
                let Some(idx) = img_ptr.get_index3() else {
                    bail!("{img} isn't a Tree3 pointer");
                };
                let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                let vec = [*a, *b, *c];
                for (mptr, ptr) in preimg.iter().zip(vec.iter()) {
                    bind(bindings, mptr.clone(), *ptr)?;
                }
                preimages.hash3.push(vec.to_vec());
                Ok(())
            }
            LEMOP::Unhash4(preimg, img) => {
                let img_ptr = img.get_ptr(bindings)?;
                let Some(idx) = img_ptr.get_index4() else {
                    bail!("{img} isn't a Tree4 pointer");
                };
                let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                let vec = [*a, *b, *c, *d];
                for (mptr, ptr) in preimg.iter().zip(vec.iter()) {
                    bind(bindings, mptr.clone(), *ptr)?;
                }
                preimages.hash4.push(vec.to_vec());
                Ok(())
            }
            LEMOP::Hide(tgt, sec, src) => {
                let src_ptr = src.get_ptr(bindings)?;
                let Ptr::Leaf(Tag::Num, secret) = sec.get_ptr(bindings)? else {
                    bail!("{sec} is not a numeric pointer")
                };
                let z_ptr = store.hash_ptr(src_ptr)?;
                let hash = store
                    .poseidon_cache
                    .hash3(&[*secret, z_ptr.tag.to_field(), z_ptr.hash]);
                let tgt_ptr = Ptr::comm(hash);
                store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                bind(bindings, tgt.clone(), tgt_ptr)
            }
            LEMOP::Open(tgt_secret, tgt_ptr, comm_or_num) => match comm_or_num.get_ptr(bindings)? {
                Ptr::Leaf(Tag::Num, hash) | Ptr::Leaf(Tag::Comm, hash) => {
                    let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                            bail!("No committed data for hash {}", &hash.hex_digits())
                        };
                    bind(bindings, tgt_ptr.clone(), *ptr)?;
                    bind(bindings, tgt_secret.clone(), Ptr::Leaf(Tag::Num, *secret))
                }
                _ => {
                    bail!("{comm_or_num} is not a num/comm pointer")
                }
            },
        }
    }
}

impl LEMCTL {
    /// Interprets a LEM using a stack of operations to be popped and executed.
    /// It modifies a `Store` and binds `MetaPtr`s to `Ptr`s as it goes. We also
    /// want to collect data from visited slots.
    fn run<F: LurkField>(
        &self,
        input: [Ptr<F>; 3],
        store: &mut Store<F>,
        mut bindings: HashMap<MetaPtr, Ptr<F>>,
        mut preimages: Preimages<F>,
    ) -> Result<Frame<F>> {
        match self {
            LEMCTL::MatchTag(ptr, cases) => {
                let ptr = ptr.get_ptr(&bindings)?;
                let ptr_tag = ptr.tag();
                match cases.get(ptr_tag) {
                    Some(op) => op.run(input, store, bindings, preimages),
                    None => bail!("No match for tag {}", ptr_tag),
                }
            }
            LEMCTL::MatchSymbol(match_ptr, cases, def) => {
                let ptr = match_ptr.get_ptr(&bindings)?;
                let Some(symbol) = store.fetch_symbol(ptr) else {
                    bail!("Symbol not found for {match_ptr}");
                };
                match cases.get(&symbol) {
                    Some(op) => op.run(input, store, bindings, preimages),
                    None => def.run(input, store, bindings, preimages),
                }
            }
            LEMCTL::Seq(ops, rest) => {
                for op in ops {
                    op.run(store, &mut bindings, &mut preimages)?;
                }
                rest.run(input, store, bindings, preimages)
            }
            LEMCTL::Return(o) => {
                let output = [
                    *o[0].get_ptr(&bindings)?,
                    *o[1].get_ptr(&bindings)?,
                    *o[2].get_ptr(&bindings)?,
                ];
                Ok(Frame {
                    input,
                    output,
                    bindings,
                    preimages,
                })
            }
        }
    }
}

impl LEM {
    /// Calls `run` until the stop contidion is satisfied, using the output of one
    /// iteration as the input of the next one.
    pub fn eval<F: LurkField>(&self, expr: Ptr<F>, store: &mut Store<F>) -> Result<Vec<Frame<F>>> {
        // Lurk constants
        let outermost = Ptr::null(Tag::Outermost);
        let terminal = &Ptr::null(Tag::Terminal);
        let error = &Ptr::null(Tag::Error);
        let nil = store.intern_symbol(&Symbol::lurk_sym("nil"));

        // Initial input and initial frames
        let mut input = [expr, nil, outermost];
        let mut frames = vec![];

        loop {
            // Map of names to pointers (its key/val pairs should never be overwritten)
            let mut bindings = HashMap::default();
            for (i, name) in self.input_vars.iter().enumerate() {
                bind(&mut bindings, MetaPtr(name.clone()), input[i])?;
            }

            let preimages = Preimages::default();
            let frame = self.lem.run(input, store, bindings, preimages)?;
            if &frame.output[2] == terminal || &frame.output[2] == error {
                frames.push(frame);
                break;
            }
            input = frame.output;
            frames.push(frame);
        }
        Ok(frames)
    }
}
