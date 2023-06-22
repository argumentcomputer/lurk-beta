use crate::field::{FWrap, LurkField};
use anyhow::{bail, Result};
use std::collections::HashMap;

use super::{
    circuit::SlotsInfo, pointers::Ptr, store::Store, symbol::Symbol, tag::Tag, MetaPtr, LEM, LEMCTL, LEMOP,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum SlotType {
    Hash2,
    Hash3,
    Hash4,
}

impl SlotType {
    pub(crate) fn preimg_size(&self) -> usize {
        match self {
            Self::Hash2 => 4,
            Self::Hash3 => 6,
            Self::Hash4 => 8,
        }
    }
}

impl std::fmt::Display for SlotType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Hash2 => write!(f, "Hash2"),
            Self::Hash3 => write!(f, "Hash3"),
            Self::Hash4 => write!(f, "Hash4"),
        }
    }
}

/// A `Slot` is characterized by an index and a type
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Slot {
    pub idx: usize,
    pub typ: SlotType,
}

impl std::fmt::Display for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Slot({}, {})", self.idx, self.typ)
    }
}

/// This hashmap is populated during interpretation, telling which slots were
/// visited and the data that was collected for each of them. The example below
/// has 5 slots, 3 of which have been visited during interpretation.
///
///```text
///            Slot index
///      ┌┬┬┬┬┬───┬───┬───┐
///      ├┼┼┼┼┤ 0 │ 1 │ 2 │
///      ├┴┴┴┴┼───┼───┼───┤
/// Slot │ H2 │ a │ b │   │
/// type ├────┼───┼───┼───┘
///      │ H3 │ c │   │
///      └────┴───┴───┘
///```
/// `a`, `b` and `c` are the `Vec<Ptr<F>>` that were collected. The slots that
/// weren't visited don't have key/value pairs present on `Visits`.
pub(crate) type Visits<F> = HashMap<Slot, Vec<Ptr<F>>>;

/// A `Frame` carries the data that results from interpreting a LEM. That is,
/// it contains the input, the output and all the assignments resulting from
/// running one iteration as a HashMap of meta pointers to pointers.
///
/// Finally, `visits` contains the data collected from visiting the slots. This
/// information is used to generte the witness.
#[derive(Clone)]
pub struct Frame<F: LurkField> {
    pub input: [Ptr<F>; 3],
    pub output: [Ptr<F>; 3],
    pub binds: HashMap<MetaPtr, Ptr<F>>,
    pub visits: Visits<F>,
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
fn bind<F: LurkField>(binds: &mut HashMap<MetaPtr, Ptr<F>>, mptr: MetaPtr, ptr: Ptr<F>) -> Result<()> {
    if binds.insert(mptr.clone(), ptr).is_some() {
        bail!("{} already defined", mptr)
    }
    Ok(())
}

impl LEMOP {
    fn run<F: LurkField>(
        &self,
        store: &mut Store<F>,
        binds: &mut HashMap<MetaPtr, Ptr<F>>,
        visits: &mut Visits<F>,
        slots_info: &SlotsInfo,
    ) -> Result<()> {
        match self {
            LEMOP::Null(tgt, tag) => {
                let tgt_ptr = Ptr::null(*tag);
                bind(binds, tgt.clone(), tgt_ptr)
            }
            LEMOP::Hash2(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(&binds, preimg)?;
                let tgt_ptr = store.intern_2_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1]);
                bind(binds, img.clone(), tgt_ptr)?;
                visits.insert(*slots_info.get_slot(self)?, preimg_ptrs);
                Ok(())
            }
            LEMOP::Hash3(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(&binds, preimg)?;
                let tgt_ptr =
                    store.intern_3_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1], preimg_ptrs[2]);
                bind(binds, img.clone(), tgt_ptr)?;
                visits.insert(*slots_info.get_slot(self)?, preimg_ptrs);
                Ok(())
            }
            LEMOP::Hash4(img, tag, preimg) => {
                let preimg_ptrs = retrieve_many(&binds, preimg)?;
                let tgt_ptr = store.intern_4_ptrs(
                    *tag,
                    preimg_ptrs[0],
                    preimg_ptrs[1],
                    preimg_ptrs[2],
                    preimg_ptrs[3],
                );
                bind(binds, img.clone(), tgt_ptr)?;
                visits.insert(*slots_info.get_slot(self)?, preimg_ptrs);
                Ok(())
            }
            LEMOP::Unhash2(preimg, img) => {
                let img_ptr = img.get_ptr(&binds)?;
                let Some(idx) = img_ptr.get_index2() else {
                    bail!("{img} isn't a Tree2 pointer");
                };
                let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                let vec = vec![*a, *b];
                for (mptr, ptr) in preimg.iter().zip(vec.iter()) {
                    bind(binds, mptr.clone(), *ptr)?;
                }
                visits.insert(*slots_info.get_slot(self)?, vec);
                Ok(())
            }
            LEMOP::Unhash3(preimg, img) => {
                let img_ptr = img.get_ptr(&binds)?;
                let Some(idx) = img_ptr.get_index3() else {
                    bail!("{img} isn't a Tree3 pointer");
                };
                let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                let vec = vec![*a, *b, *c];
                for (mptr, ptr) in preimg.iter().zip(vec.iter()) {
                    bind(binds, mptr.clone(), *ptr)?;
                }
                visits.insert(*slots_info.get_slot(self)?, vec);
                Ok(())
            }
            LEMOP::Unhash4(preimg, img) => {
                let img_ptr = img.get_ptr(&binds)?;
                let Some(idx) = img_ptr.get_index4() else {
                    bail!("{img} isn't a Tree4 pointer");
                };
                let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                let vec = vec![*a, *b, *c, *d];
                for (mptr, ptr) in preimg.iter().zip(vec.iter()) {
                    bind(binds, mptr.clone(), *ptr)?;
                }
                visits.insert(*slots_info.get_slot(self)?, vec);
                Ok(())
            }
            LEMOP::Hide(tgt, sec, src) => {
                let src_ptr = src.get_ptr(&binds)?;
                let Ptr::Leaf(Tag::Num, secret) = sec.get_ptr(&binds)? else {
                    bail!("{sec} is not a numeric pointer")
                };
                let z_ptr = store.hash_ptr(src_ptr)?;
                let hash =
                    store
                        .poseidon_cache
                        .hash3(&[*secret, z_ptr.tag.to_field(), z_ptr.hash]);
                let tgt_ptr = Ptr::comm(hash);
                store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                bind(binds, tgt.clone(), tgt_ptr)
            }
            LEMOP::Open(tgt_secret, tgt_ptr, comm_or_num) => {
                match comm_or_num.get_ptr(&binds)? {
                    Ptr::Leaf(Tag::Num, hash) | Ptr::Leaf(Tag::Comm, hash) => {
                        let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                            bail!("No committed data for hash {}", &hash.hex_digits())
                        };
                        bind(binds, tgt_ptr.clone(), *ptr)?;
                        bind(binds, tgt_secret.clone(), Ptr::Leaf(Tag::Num, *secret))
                    }
                    _ => {
                        bail!("{comm_or_num} is not a num/comm pointer")
                    }
                }
            }
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
        mut binds: HashMap<MetaPtr, Ptr<F>>,
        mut visits: Visits<F>,
        slots_info: &SlotsInfo,
    ) -> Result<Frame<F>> {
        match self {
            LEMCTL::MatchTag(ptr, cases) => {
                let ptr = ptr.get_ptr(&binds)?;
                let ptr_tag = ptr.tag();
                match cases.get(ptr_tag) {
                    Some(op) => op.run(input, store, binds, visits, slots_info),
                    None => bail!("No match for tag {}", ptr_tag),
                }
            }
            LEMCTL::MatchSymbol(match_ptr, cases, def) => {
                let ptr = match_ptr.get_ptr(&binds)?;
                let Some(symbol) = store.fetch_symbol(ptr) else {
                    bail!("Symbol not found for {match_ptr}");
                };
                match cases.get(&symbol) {
                    Some(op) => op.run(input, store, binds, visits, slots_info),
                    None => def.run(input, store, binds, visits, slots_info),
                }
            }
            LEMCTL::Seq(ops, rest) => {
                for op in ops {
                    op.run(store, &mut binds, &mut visits, slots_info)?;
                }
                rest.run(input, store, binds, visits, slots_info)
            },
            LEMCTL::Return(o) => {
                let output = [
                    *o[0].get_ptr(&binds)?,
                    *o[1].get_ptr(&binds)?,
                    *o[2].get_ptr(&binds)?,
                ];
                Ok(Frame {
                    input,
                    output,
                    binds,
                    visits,
                })
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
        slots_info: &SlotsInfo,
    ) -> Result<Vec<Frame<F>>> {
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
            let mut binds = HashMap::default();
            for (i, name) in self.input_vars.iter().enumerate() {
                bind(&mut binds, MetaPtr(name.clone()), input[i])?;
            }

            let visits = Visits::default();
            let frame = self.lem.run(input, store, binds, visits, slots_info)?;
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
