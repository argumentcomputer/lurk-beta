use crate::field::{FWrap, LurkField};
use anyhow::{bail, Result};
use std::collections::HashMap;

use super::{
    constrainer::SlotsIndices, pointers::Ptr, store::Store, symbol::Symbol, tag::Tag, LEM, LEMOP,
};

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum SlotArity {
    A2,
    A3,
    A4,
}

impl SlotArity {
    pub(crate) fn preimg_size(&self) -> usize {
        match self {
            Self::A2 => 4,
            Self::A3 => 6,
            Self::A4 => 8,
        }
    }
}

/// This hashmap is populated during interpretation, telling which **slots** were
/// visited. Knowing which LEMOPs were visited is not enough because different
/// LEMOPs on parallel paths can ocupy the same slot
pub(crate) type Visits<F> = HashMap<(SlotArity, usize), Vec<Ptr<F>>>;

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
    pub ptrs: HashMap<String, Ptr<F>>,
    pub visits: Visits<F>,
}

fn insert_into_ptrs<F: LurkField>(
    ptrs: &mut HashMap<String, Ptr<F>>,
    name: String,
    ptr: Ptr<F>,
) -> Result<()> {
    let mut msg = "Already defined: ".to_owned();
    msg.push_str(&name);
    if ptrs.insert(name, ptr).is_some() {
        bail!("{msg}");
    }
    Ok(())
}

impl LEM {
    /// Interprets a LEM using a stack of operations to be popped and executed.
    /// It modifies a `Store` and assigns `Ptr`s to `MetaPtr`s as it goes.
    fn run<F: LurkField>(
        &self,
        input: [Ptr<F>; 3],
        store: &mut Store<F>,
        slots_indices: &SlotsIndices,
    ) -> Result<Frame<F>> {
        // key/val pairs on this map should never be overwritten
        let mut ptrs = HashMap::default();
        ptrs.insert(self.input[0].clone(), input[0]);
        insert_into_ptrs(&mut ptrs, self.input[1].clone(), input[1])?;
        insert_into_ptrs(&mut ptrs, self.input[2].clone(), input[2])?;
        let mut visits = Visits::default();
        let mut stack = vec![&self.lem_op];
        while let Some(op) = stack.pop() {
            match op {
                LEMOP::Null(tgt, tag) => {
                    let tgt_ptr = Ptr::null(*tag);
                    insert_into_ptrs(&mut ptrs, tgt.name().clone(), tgt_ptr)?;
                }
                LEMOP::Hash2(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?.to_owned();
                    let src_ptr2 = src[1].get_ptr(&ptrs)?.to_owned();
                    let tgt_ptr = store.intern_2_ptrs(*tag, src_ptr1, src_ptr2);
                    insert_into_ptrs(&mut ptrs, tgt.name().clone(), tgt_ptr)?;
                    visits.insert(
                        (SlotArity::A2, *slots_indices.get(op).unwrap()),
                        vec![src_ptr1, src_ptr2],
                    );
                }
                LEMOP::Hash3(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?.to_owned();
                    let src_ptr2 = src[1].get_ptr(&ptrs)?.to_owned();
                    let src_ptr3 = src[2].get_ptr(&ptrs)?.to_owned();
                    let tgt_ptr = store.intern_3_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3);
                    insert_into_ptrs(&mut ptrs, tgt.name().clone(), tgt_ptr)?;
                    visits.insert(
                        (SlotArity::A3, *slots_indices.get(op).unwrap()),
                        vec![src_ptr1, src_ptr2, src_ptr3],
                    );
                }
                LEMOP::Hash4(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?.to_owned();
                    let src_ptr2 = src[1].get_ptr(&ptrs)?.to_owned();
                    let src_ptr3 = src[2].get_ptr(&ptrs)?.to_owned();
                    let src_ptr4 = src[3].get_ptr(&ptrs)?.to_owned();
                    let tgt_ptr = store.intern_4_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3, src_ptr4);
                    insert_into_ptrs(&mut ptrs, tgt.name().clone(), tgt_ptr)?;
                    visits.insert(
                        (SlotArity::A4, *slots_indices.get(op).unwrap()),
                        vec![src_ptr1, src_ptr2, src_ptr3, src_ptr4],
                    );
                }
                LEMOP::Unhash2(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index2() else {
                        bail!("{src} isn't a Tree2 pointer");
                    };
                    let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                        bail!("Couldn't fetch {src}'s children")
                    };
                    insert_into_ptrs(&mut ptrs, tgts[0].name().clone(), *a)?;
                    insert_into_ptrs(&mut ptrs, tgts[1].name().clone(), *b)?;
                    // STEP 2: Update hash_witness with preimage and image
                    visits.insert(
                        (SlotArity::A2, *slots_indices.get(op).unwrap()),
                        vec![*a, *b],
                    );
                }
                LEMOP::Unhash3(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index3() else {
                        bail!("{src} isn't a Tree3 pointer");
                    };
                    let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                        bail!("Couldn't fetch {src}'s children")
                    };
                    insert_into_ptrs(&mut ptrs, tgts[0].name().clone(), *a)?;
                    insert_into_ptrs(&mut ptrs, tgts[1].name().clone(), *b)?;
                    insert_into_ptrs(&mut ptrs, tgts[2].name().clone(), *c)?;
                    // STEP 2: Update hash_witness with preimage and image
                    visits.insert(
                        (SlotArity::A3, *slots_indices.get(op).unwrap()),
                        vec![*a, *b, *c],
                    );
                }
                LEMOP::Unhash4(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index4() else {
                        bail!("{src} isn't a Tree4 pointer");
                    };
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                        bail!("Couldn't fetch {src}'s children")
                    };
                    insert_into_ptrs(&mut ptrs, tgts[0].name().clone(), *a)?;
                    insert_into_ptrs(&mut ptrs, tgts[1].name().clone(), *b)?;
                    insert_into_ptrs(&mut ptrs, tgts[2].name().clone(), *c)?;
                    insert_into_ptrs(&mut ptrs, tgts[3].name().clone(), *d)?;
                    // STEP 2: Update hash_witness with preimage and image
                    visits.insert(
                        (SlotArity::A4, *slots_indices.get(op).unwrap()),
                        vec![*a, *b, *c, *d],
                    );
                }
                LEMOP::Hide(tgt, sec, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Ptr::Leaf(Tag::Num, secret) = sec.get_ptr(&ptrs)? else {
                        bail!("{sec} is not a numeric pointer")
                    };
                    let z_ptr = store.hash_ptr(src_ptr)?;
                    let hash =
                        store
                            .poseidon_cache
                            .hash3(&[*secret, z_ptr.tag.to_field(), z_ptr.hash]);
                    let tgt_ptr = Ptr::comm(hash);
                    store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                    insert_into_ptrs(&mut ptrs, tgt.name().clone(), tgt_ptr)?;
                }
                LEMOP::Open(tgt_secret, tgt_ptr, comm_or_num) => {
                    match comm_or_num.get_ptr(&ptrs)? {
                        Ptr::Leaf(Tag::Num, hash) | Ptr::Leaf(Tag::Comm, hash) => {
                            let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                                bail!("No committed data for hash {}", &hash.hex_digits())
                            };
                            insert_into_ptrs(&mut ptrs, tgt_ptr.name().clone(), *ptr)?;
                            insert_into_ptrs(
                                &mut ptrs,
                                tgt_secret.name().clone(),
                                Ptr::Leaf(Tag::Num, *secret),
                            )?;
                        }
                        _ => {
                            bail!("{comm_or_num} is not a num/comm pointer")
                        }
                    }
                }
                LEMOP::MatchTag(ptr, cases) => {
                    let ptr = ptr.get_ptr(&ptrs)?;
                    let ptr_tag = ptr.tag();
                    match cases.get(ptr_tag) {
                        Some(op) => stack.push(op),
                        None => bail!("No match for tag {}", ptr_tag),
                    }
                }
                LEMOP::MatchSymPath(match_ptr, cases, def) => {
                    let ptr = match_ptr.get_ptr(&ptrs)?;
                    let Some(sym_path) = store.fetch_sym_path(ptr) else {
                        bail!("Symbol path not found for {match_ptr}");
                    };
                    match cases.get(sym_path) {
                        Some(op) => stack.push(op),
                        None => stack.push(def),
                    }
                }
                LEMOP::Seq(ops) => stack.extend(ops.iter().rev()),
                LEMOP::Return(o) => {
                    let output = [
                        *o[0].get_ptr(&ptrs)?,
                        *o[1].get_ptr(&ptrs)?,
                        *o[2].get_ptr(&ptrs)?,
                    ];
                    return Ok(Frame {
                        input,
                        output,
                        ptrs,
                        visits,
                    });
                }
            }
        }
        bail!("Output not reached");
    }

    /// Calls `run` until the stop contidion is satisfied, using the output of one
    /// iteration as the input of the next one.
    pub fn eval<F: LurkField>(
        &self,
        expr: Ptr<F>,
        store: &mut Store<F>,
        slots_indices: &SlotsIndices,
    ) -> Result<Vec<Frame<F>>> {
        let mut expr = expr;
        let mut env = store.intern_symbol(&Symbol::lurk_sym("nil"));
        let mut cont = Ptr::null(Tag::Outermost);
        let mut frames = vec![];
        let terminal = &Ptr::null(Tag::Terminal);
        let error = &Ptr::null(Tag::Error);
        loop {
            let frame = self.run([expr, env, cont], store, slots_indices)?;
            frames.push(frame.clone());
            if &frame.output[2] == terminal || &frame.output[2] == error {
                break;
            } else {
                [expr, env, cont] = frame.output;
            }
        }
        Ok(frames)
    }
}
