use crate::field::{FWrap, LurkField};
use anyhow::{bail, Result};
use std::collections::HashMap;

use super::{pointers::Ptr, store::Store, symbol::Symbol, tag::Tag, MetaPtr, LEMPLUS, LEM, LEMOP, AString};

/// Contains preimage and image.
/// REMARK: this structure will be populated in the second LEM traversal, which
/// corresponds to STEP 2 of the hash slots mechanism. In particular, STEP 2
/// happens during interpretation of LEM and stores the hash witnesses in the
/// order they appear during interpretation
#[derive(Clone, Default)]
pub struct Preimages {
    pub hash2: Vec<[MetaPtr; 2]>,
    pub hash3: Vec<[MetaPtr; 3]>,
    pub hash4: Vec<[MetaPtr; 4]>,
}

/// A `Frame` carries the data that results from interpreting LEM. That is,
/// it contains the input, the output and all the assignments resulting from
/// running one iteration as a HashMap of pointers indexed by variable names.
///
/// Finally, `preimages` contains the sequence of hash witnesses visited
/// during interpretation. This information is needed to generate the witness.
#[derive(Clone)]
pub struct Frame<F: LurkField> {
    pub input: [Ptr<F>; 3],
    pub output: [Ptr<F>; 3],
    pub ptrs: HashMap<AString, Ptr<F>>,
    pub preimages: Preimages,
}

fn insert_into_ptrs<F: LurkField>(
    ptrs: &mut HashMap<AString, Ptr<F>>,
    name: &AString,
    ptr: Ptr<F>,
) -> Result<()> {
    if ptrs.insert(name.clone(), ptr).is_some() {
        let mut msg = "Already defined: ".to_owned();
        msg.push_str(name);
        bail!("{msg}");
    }
    Ok(())
}

impl LEMOP {
    fn run<F: LurkField>(
        &self,
        store: &mut Store<F>,
        ptrs: &mut HashMap<AString, Ptr<F>>,
        preimages: &mut Preimages,
    ) -> Result<()> {
        match self {
            LEMOP::Null(tgt, tag) => {
                let tgt_ptr = Ptr::null(*tag);
                insert_into_ptrs(ptrs, tgt.name(), tgt_ptr)
            }
            LEMOP::Hash2(tgt, tag, src) => {
                let src_ptr1 = src[0].get_ptr(ptrs)?;
                let src_ptr2 = src[1].get_ptr(ptrs)?;
                let tgt_ptr = store.intern_2_ptrs(*tag, *src_ptr1, *src_ptr2);
                insert_into_ptrs(ptrs, tgt.name(), tgt_ptr)?;
                preimages.hash2.push(src.clone());
                Ok(())
            }
            LEMOP::Hash3(tgt, tag, src) => {
                let src_ptr1 = src[0].get_ptr(ptrs)?;
                let src_ptr2 = src[1].get_ptr(ptrs)?;
                let src_ptr3 = src[2].get_ptr(ptrs)?;
                let tgt_ptr = store.intern_3_ptrs(*tag, *src_ptr1, *src_ptr2, *src_ptr3);
                insert_into_ptrs(ptrs, tgt.name(), tgt_ptr)?;
                preimages.hash3.push(src.clone());
                Ok(())
            }
            LEMOP::Hash4(tgt, tag, src) => {
                let src_ptr1 = src[0].get_ptr(ptrs)?;
                let src_ptr2 = src[1].get_ptr(ptrs)?;
                let src_ptr3 = src[2].get_ptr(ptrs)?;
                let src_ptr4 = src[3].get_ptr(ptrs)?;
                let tgt_ptr =
                    store.intern_4_ptrs(*tag, *src_ptr1, *src_ptr2, *src_ptr3, *src_ptr4);
                insert_into_ptrs(ptrs, tgt.name(), tgt_ptr)?;
                preimages.hash4.push(src.clone());
                Ok(())
            }
            LEMOP::Unhash2(tgts, src) => {
                let src_ptr = src.get_ptr(ptrs)?;
                let Some(idx) = src_ptr.get_index2() else {
                    bail!("{src} isn't a Tree2 pointer");
                };
                let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                    bail!("Couldn't fetch {src}'s children")
                };
                insert_into_ptrs(ptrs, tgts[0].name(), *a)?;
                insert_into_ptrs(ptrs, tgts[1].name(), *b)?;
                // STEP 2: Update hash_witness with preimage and image
                preimages.hash2.push(tgts.clone());
                Ok(())
            }
            LEMOP::Unhash3(tgts, src) => {
                let src_ptr = src.get_ptr(ptrs)?;
                let Some(idx) = src_ptr.get_index3() else {
                    bail!("{src} isn't a Tree3 pointer");
                };
                let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                    bail!("Couldn't fetch {src}'s children")
                };
                insert_into_ptrs(ptrs, tgts[0].name(), *a)?;
                insert_into_ptrs(ptrs, tgts[1].name(), *b)?;
                insert_into_ptrs(ptrs, tgts[2].name(), *c)?;
                // STEP 2: Update hash_witness with preimage and image
                preimages.hash3.push(tgts.clone());
                Ok(())
            }
            LEMOP::Unhash4(tgts, src) => {
                let src_ptr = src.get_ptr(ptrs)?;
                let Some(idx) = src_ptr.get_index4() else {
                    bail!("{src} isn't a Tree4 pointer");
                };
                let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                    bail!("Couldn't fetch {src}'s children")
                };
                insert_into_ptrs(ptrs, tgts[0].name(), *a)?;
                insert_into_ptrs(ptrs, tgts[1].name(), *b)?;
                insert_into_ptrs(ptrs, tgts[2].name(), *c)?;
                insert_into_ptrs(ptrs, tgts[3].name(), *d)?;
                // STEP 2: Update hash_witness with preimage and image
                preimages.hash4.push(tgts.clone());
                Ok(())
            }
            LEMOP::Hide(tgt, sec, src) => {
                let src_ptr = src.get_ptr(ptrs)?;
                let Ptr::Leaf(Tag::Num, secret) = sec.get_ptr(ptrs)? else {
                    bail!("{sec} is not a numeric pointer")
                };
                let z_ptr = store.hash_ptr(src_ptr)?;
                let hash =
                    store
                    .poseidon_cache
                    .hash3(&[*secret, z_ptr.tag.to_field(), z_ptr.hash]);
                let tgt_ptr = Ptr::comm(hash);
                store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                insert_into_ptrs(ptrs, tgt.name(), tgt_ptr)
            }
            LEMOP::Open(tgt_secret, tgt_ptr, comm_or_num) => {
                match comm_or_num.get_ptr(ptrs)? {
                    Ptr::Leaf(Tag::Num, hash) | Ptr::Leaf(Tag::Comm, hash) => {
                        let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                            bail!("No committed data for hash {}", &hash.hex_digits())
                        };
                        insert_into_ptrs(ptrs, tgt_ptr.name(), *ptr)?;
                        insert_into_ptrs(
                            ptrs,
                            tgt_secret.name(),
                            Ptr::Leaf(Tag::Num, *secret),
                        )
                    }
                    _ => {
                        bail!("{comm_or_num} is not a num/comm pointer")
                    }
                }
            }
        }
    }
}

impl LEM {
    /// Interprets a LEM using a stack of operations to be popped and executed.
    /// It modifies a `Store` and assigns `Ptr`s to `MetaPtr`s as it goes.
    fn run<F: LurkField>(
        &self,
        input: [Ptr<F>; 3],
        store: &mut Store<F>,
        mut ptrs: HashMap<AString, Ptr<F>>,
        mut preimages: Preimages,
    ) -> Result<Frame<F>> {
        match self {
            LEM::MatchTag(var, cases) => {
                let ptr = var.get_ptr(&ptrs)?;
                match cases.get(ptr.tag()) {
                    Some(code) => code.run(input, store, ptrs, preimages),
                    None => bail!("No match for tag {}", ptr.tag()),
                }
            }
            LEM::MatchSymPath(var, cases, def) => {
                let ptr = var.get_ptr(&ptrs)?;
                let Some(sym_path) = store.fetch_sym_path(ptr) else {
                    bail!("Symbol path not found for {var}");
                };
                match cases.get(&**sym_path) {
                    Some(code) => code.run(input, store, ptrs, preimages),
                    None => def.run(input, store, ptrs, preimages),
                }
            }
            LEM::Seq(op, rest) => {
                op.run(store, &mut ptrs, &mut preimages)?;
                rest.run(input, store, ptrs, preimages)
            },
            LEM::Return(o) => {
                let output = [
                    *o[0].get_ptr(&ptrs)?,
                    *o[1].get_ptr(&ptrs)?,
                    *o[2].get_ptr(&ptrs)?,
                ];
                Ok(Frame {
                    input,
                    output,
                    ptrs,
                    preimages,
                })
            }
        }
    }
}

impl LEMPLUS {
    /// Calls `run` until the stop contidion is satisfied, using the output of one
    /// iteration as the input of the next one.
    pub fn eval<F: LurkField>(&self, expr: Ptr<F>, store: &mut Store<F>) -> Result<Vec<Frame<F>>> {
        // Lurk constants
        let outermost = Ptr::null(Tag::Outermost);
        let terminal = &Ptr::null(Tag::Terminal);
        let error = &Ptr::null(Tag::Error);
        let nil = store.intern_symbol(&Symbol::lurk_sym("nil".into()));

        // Initial input and initial frames
        let mut input = [expr, nil, outermost];
        let mut frames = vec![];

        loop {
            // Map of names to pointers (its key/val pairs should never be overwritten)
            let mut ptrs = HashMap::default();
            input.iter().enumerate().try_for_each(|(index, value)| {
                insert_into_ptrs(&mut ptrs, &self.input[index], *value)
            })?;
            // Lists of preimages of hashes
            let preimages = Preimages::default();

            let frame = self.lem.run(input, store, ptrs, preimages)?;
            if &frame.output[2] == terminal || &frame.output[2] == error {
                break;
            }
            input = frame.output;
            frames.push(frame);
        }
        Ok(frames)
    }
}
