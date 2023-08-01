//! ### Slot optimizations
//!
//! Some LEM functions may require expensive gadgets, such as Poseidon hashing.
//! So we use the concept of "slots" to avoid wasting constraints. To explore
//! this idea, let's use the following LEM as an example:
//!
//! ```text
//! (a, b, c): 3 => {
//!     match_tag c {
//!         Num => {
//!             let x: Cons = hash2(a, b);
//!             return (x, x, x);
//!         },
//!         Char => {
//!             let m: Cons = hash2(b, a);
//!             let n: Cons = hash2(c, a);
//!             return (m, m, n);
//!         }
//!     }
//! }
//! ```
//!
//! On a first impression, one might think that we need to perform three hashing
//! operations in the circuit when in fact we can get away with only two. That
//! is so because interpretation can only follow one of the paths:
//!
//! * If it goes through `Num`, we need to get one hash right
//! * If it goes through `Char`, we need to get two hashes right
//!
//! Either way, that's at most two hashes that we really care about. So we say
//! that we need to allocate two slots. The first slot is for the the hash of `x`
//! or `m` and the second slot is for the hash of `n` (or a "dummy value", as
//! explained ahead). Let's see a sketch of part of the circuit:
//!
//! ```text
//!     ┌─────┐        ┌─────┐
//! s0i0┤slot0├s0  s1i0┤slot1├s1
//! s0i1┤hash2│    s1i1┤hash2│
//!     └─────┘        └─────┘
//! ...
//! PNum = c.tag == Num
//! PChar = c.tag == Char
//!
//! PNum → a == s0i0
//! PNum → b == s0i1
//! PNum → x.hash == s0
//!
//! PChar → b == s0i0
//! PChar → a == s0i1
//! PChar → m.hash == s0
//!
//! PChar → c == s1i0
//! PChar → a == s1i1
//! PChar → n.hash == s1
//! ```
//!
//! `PNum` and `PChar` are boolean premises that indicate whether interpretation
//! went through `Num` or `Char` respectively. They're used as inputs for gadgets
//! that implement implications (hence the right arrows above). We will talk
//! about "concrete" vs "virtual" paths elsewhere.
//!
//! Now we're able to feed the slots with the data that comes from interpretation:
//!
//! 1. If it goes through `Num`, we will collect `[[a, b]]` for the preimages of
//! the slots. So we can feed the preimage of `slot0` with `[a, b]` and the
//! preimage of `slot1` with dummies
//!
//! 2. If it goes through `Char`, we will collect `[[b, a], [c, a]]` for the
//! preimages of the slots. So we can feed the preimage of `slot0` with `[b, a]`
//! and the preimage of `slot1` with `[c, a]`.
//!
//! In the first case, `PNum` will be true, requiring that the conclusions of the
//! implications for which it is the premise must also be true (which is fine!).
//! `PChar`, on the other hand, will be false, making the conclusions of the
//! implications for which it is the premise irrelevant. This is crucial because
//! interpretation won't even produce bindings for `m` or `n`, thus we don't
//! expect to fulfill `m.hash == s0` nor `n.hash == s1`. In fact, we don't expect
//! to fulfill any conclusion in the implications deriving from the `PChar` premise.
//!
//! Finally, we have an analogous situation for the second case, when
//! interpretation goes through `Char`.
//!
//! This example explored slots of type "hash2", but the same line of thought can
//! be expanded to different types of slots, orthogonally.
//!
//! #### The slot optimization algorithm
//!
//! We've separated the process in three steps:
//!
//! 1. Perform a static analysis to compute the number of slots (for each slot
//! type) that are needed. This piece of information will live on a `SlotsCounter`
//! structure, which is populated by the function `Block::count_slots`;
//!
//! 2. Interpret the LEM function and collect the data that will be fed to some
//! (or all) slots, along with all bindings from `Var`s to `Ptr`s. This piece of
//! information will live on a `Frame` structure;
//!
//! 3. Build the circuit with `SlotsCounter` and `Frame` at hand. This step is
//! better explained in the `Func::synthesize` function.
//!
//! The 3 steps above will be further referred to as *STEP 1*, *STEP 2* and
//! *STEP 3* respectively. STEP 1 should be performed once per function. Then
//! STEP 2 will need as many iterations as it takes to evaluate the Lurk
//! expression and so will STEP 3.

use super::{Block, Ctrl, Op};

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct SlotsCounter {
    pub hash2: usize,
    pub hash3: usize,
    pub hash4: usize,
}

impl SlotsCounter {
    /// This interface is mostly for testing
    #[inline]
    pub fn new(num_slots: (usize, usize, usize)) -> Self {
        Self {
            hash2: num_slots.0,
            hash3: num_slots.1,
            hash4: num_slots.2,
        }
    }

    #[inline]
    pub fn consume_hash2(&mut self) -> usize {
        self.hash2 += 1;
        self.hash2 - 1
    }

    #[inline]
    pub fn consume_hash3(&mut self) -> usize {
        self.hash3 += 1;
        self.hash3 - 1
    }

    #[inline]
    pub fn consume_hash4(&mut self) -> usize {
        self.hash4 += 1;
        self.hash4 - 1
    }

    #[inline]
    pub fn max(&self, other: Self) -> Self {
        use std::cmp::max;
        Self {
            hash2: max(self.hash2, other.hash2),
            hash3: max(self.hash3, other.hash3),
            hash4: max(self.hash4, other.hash4),
        }
    }

    #[inline]
    pub fn add(&self, other: Self) -> Self {
        Self {
            hash2: self.hash2 + other.hash2,
            hash3: self.hash3 + other.hash3,
            hash4: self.hash4 + other.hash4,
        }
    }
}

impl Block {
    pub fn count_slots(&self) -> SlotsCounter {
        let ops_slots = self.ops.iter().fold(SlotsCounter::default(), |acc, op| {
            let val = match op {
                Op::Hash2(..) | Op::Unhash2(..) => SlotsCounter::new((1, 0, 0)),
                Op::Hash3(..) | Op::Unhash3(..) => SlotsCounter::new((0, 1, 0)),
                Op::Hash4(..) | Op::Unhash4(..) => SlotsCounter::new((0, 0, 1)),
                Op::Call(_, func, _) => func.body.count_slots(),
                _ => SlotsCounter::default(),
            };
            acc.add(val)
        });
        let ctrl_slots = match &self.ctrl {
            Ctrl::MatchTag(_, cases, def) => {
                let init = def
                    .as_ref()
                    .map_or(SlotsCounter::default(), |def| def.count_slots());
                cases
                    .values()
                    .fold(init, |acc, block| acc.max(block.count_slots()))
            }
            Ctrl::MatchVal(_, cases, def) => {
                let init = def
                    .as_ref()
                    .map_or(SlotsCounter::default(), |def| def.count_slots());
                cases
                    .values()
                    .fold(init, |acc, block| acc.max(block.count_slots()))
            }
            Ctrl::IfEq(_, _, eq_block, else_block) => {
                let eq_slots = eq_block.count_slots();
                eq_slots.max(else_block.count_slots())
            }
            Ctrl::Return(..) => SlotsCounter::default(),
        };
        ops_slots.add(ctrl_slots)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SlotType {
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
pub(crate) struct Slot {
    pub(crate) idx: usize,
    pub(crate) typ: SlotType,
}

impl std::fmt::Display for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Slot({}, {})", self.idx, self.typ)
    }
}
