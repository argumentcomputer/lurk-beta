mod pointers;
mod step;
mod store;
mod symbol;
mod tag;

use std::collections::{BTreeMap, HashMap};

use crate::field::{FWrap, LurkField};

use self::{
    pointers::{Ptr, PtrVal},
    store::Store,
    tag::Tag,
};

/// ## Lurk Evaluation Model (LEM)
///
/// A LEM is a description of Lurk's evaluation algorithm, encoded as data. In
/// other words, it's a meta-representation of Lurk's step function.
///
/// The motivation behind LEM is the fact that hand-writing the circuit is a
/// fragile process that hinders experimentation and safety. Thus we would like
/// to bootstrap the circuit automatically, given a higher level description of
/// the step function.
///
/// ### Data semantics
///
/// A LEM describes how to handle pointers with "meta pointers", with are
/// basically named references. Instead of saying `let foo ...` in Rust, we
/// use a `MetaPtr("foo")` in LEM.
///
/// The actual algorithm is encoded with a LEM operation (`LEMOP`). It's worth
/// noting that one of the LEM operators is in fact a vector of operators, which
/// allows imperative expressiveness.
///
/// ### Interpretation
///
/// Running a LEM is done via interpretation, which might be a bit slower than
/// calling Rust functions directly. But it also has its advantages:
///
/// 1. The logic to collect data during execution can be factored out from the
/// definition of the step function. This process is needed in order to evidence
/// the inputs for the circuit at proving time;
///
/// 2. Actually, such logic to collect data is a natural consequence of the fact
/// that we're on a higher level of abstraction. Relevant data is not simply
/// stored on rust variables that die after the function ends. On the contrary,
/// all relevant data lives on a `HashMap` that's also a product of the
/// interpreted LEM.
///
/// ### Static checks of correctness
///
/// Since a LEM is an algorithm encoded as data, we can perform static checks of
/// correctness as some form of (automated) formal verification. Here are some
/// (WIP) properties we want a LEM to have before we can adopt it as a proper
/// Lurk step function:
///
/// 1. Static single assignments: overwriting meta pointers would erase relevant
/// data needed to feed the circuit at proving time. We don't want to lose any
/// piece of information that the prover might know;
///
/// 2. Non-duplicated input labels: right at the start of interpretation, the
/// input labels are bound to the actual pointers that represent the expression,
/// environment and continuation. If some label is repeated, it will fatally
/// break property 1;
///
/// 3. Output assignment completeness: at the end of every step we want all the
/// output labels to be bound to some pointer otherwise we wouldn't know how to
/// proceed on the next step;
///
/// 4. Non-duplicated output labels: property 3 forces us have a pointer bound
/// to every output label. If some output label is duplicated, we would fatally
/// break property 1;
///
/// 5. Disjoint input and output labels: if an input label is also present in
/// the output, satisfying property 3 would break property 1 because such label
/// would be bound twice;
///
/// 6. Assign first, use later: this prevents obvious "x not found" errors at
/// interpretation time.
pub struct LEM<'a, F: LurkField> {
    input: [&'a str; 3],
    output: [&'a str; 3],
    lem_op: LEMOP<'a, F>,
}

#[derive(PartialEq, Clone, Copy)]
pub struct MetaPtr<'a>(&'a str);

impl<'a> MetaPtr<'a> {
    #[inline]
    pub fn name(self) -> &'a str {
        self.0
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct MetaVar<'a>(&'a str);

impl<'a> MetaVar<'a> {
    #[inline]
    pub fn name(self) -> &'a str {
        self.0
    }
}

#[derive(Clone)]
pub enum LEMOP<'a, F: LurkField> {
    MkNull(MetaPtr<'a>, Tag),
    Copy(MetaPtr<'a>, MetaPtr<'a>),
    Hash2Ptrs(MetaPtr<'a>, Tag, [MetaPtr<'a>; 2]),
    Hash3Ptrs(MetaPtr<'a>, Tag, [MetaPtr<'a>; 3]),
    Hash4Ptrs(MetaPtr<'a>, Tag, [MetaPtr<'a>; 4]),
    Unhash2Ptrs([MetaPtr<'a>; 2], MetaPtr<'a>),
    Unhash3Ptrs([MetaPtr<'a>; 3], MetaPtr<'a>),
    Unhash4Ptrs([MetaPtr<'a>; 4], MetaPtr<'a>),
    Hide(MetaPtr<'a>, F, MetaPtr<'a>),
    Open(MetaVar<'a>, MetaPtr<'a>, F), // secret, tgt, src hash
    IfTagEq(MetaPtr<'a>, Tag, Box<LEMOP<'a, F>>, Box<LEMOP<'a, F>>),
    IfTagOr(MetaPtr<'a>, Tag, Tag, Box<LEMOP<'a, F>>, Box<LEMOP<'a, F>>),
    MatchTag(MetaPtr<'a>, BTreeMap<Tag, LEMOP<'a, F>>, Box<LEMOP<'a, F>>),
    Seq(Vec<LEMOP<'a, F>>),
}

pub struct StepData<'a, F: LurkField> {
    input: [Ptr<F>; 3],
    output: [Ptr<F>; 3],
    ptrs: HashMap<&'a str, Ptr<F>>,
    vals: HashMap<&'a str, F>,
}

impl<'a, F: LurkField> LEMOP<'a, F> {
    #[inline]
    pub fn mk_if_tag_eq(
        ptr: MetaPtr<'a>,
        tag: Tag,
        ff: LEMOP<'a, F>,
        tt: LEMOP<'a, F>,
    ) -> LEMOP<'a, F> {
        LEMOP::IfTagEq(ptr, tag, Box::new(tt), Box::new(ff))
    }

    #[inline]
    pub fn mk_if_tag_or(
        ptr: MetaPtr<'a>,
        tag1: Tag,
        tag2: Tag,
        ff: LEMOP<'a, F>,
        tt: LEMOP<'a, F>,
    ) -> LEMOP<'a, F> {
        LEMOP::IfTagOr(ptr, tag1, tag2, Box::new(tt), Box::new(ff))
    }

    pub fn assert_list(ptr: MetaPtr<'a>, ff: LEMOP<'a, F>, tt: LEMOP<'a, F>) -> LEMOP<'a, F> {
        Self::mk_if_tag_or(ptr, Tag::Cons, Tag::Nil, ff, tt)
    }

    pub fn mk_cons(o: &'a str, i: [MetaPtr<'a>; 2]) -> LEMOP<'a, F> {
        LEMOP::Hash2Ptrs(MetaPtr(o), Tag::Cons, i)
    }

    // pub fn mk_strcons(o: &'a str, i: [MetaPtr<'a>; 2]) -> LEMOP<'a> {
    //     Self::mk_if_tag_eq(
    //         i[0],
    //         Tag::Char,
    //         LEMOP::Err("strcons requires a char as the first argument"),
    //         Self::mk_if_tag_eq(
    //             i[1],
    //             Tag::Str,
    //             LEMOP::Err("strcons requires a str as the second argument"),
    //             LEMOP::Hash2Ptrs(MetaPtr(o), Tag::Str, i),
    //         ),
    //     )
    // }

    // pub fn mk_fun(o: &'a str, i: [MetaPtr<'a>; 3]) -> LEMOP<'a> {
    //     Self::assert_list(
    //         i[0],
    //         LEMOP::Err("The arguments must be a list"),
    //         Self::assert_list(
    //             i[2],
    //             LEMOP::Err("The closed env must be a list"),
    //             LEMOP::Hash3Ptrs(MetaPtr(o), Tag::Fun, i),
    //         ),
    //     )
    // }

    pub fn mk_match_tag(
        i: MetaPtr<'a>,
        cases: Vec<(Tag, LEMOP<'a, F>)>,
        def: LEMOP<'a, F>,
    ) -> LEMOP<'a, F> {
        let mut match_map = BTreeMap::default();
        for (f, op) in cases.iter() {
            match_map.insert(*f, op.clone());
        }
        LEMOP::MatchTag(i, match_map, Box::new(def))
    }
}

impl<'a, F: LurkField> LEM<'a, F> {
    pub fn check(&self) {
        for s in self.input.iter() {
            assert!(
                !self.output.contains(&s),
                "Input and output must be disjoint"
            )
        }
        // TODO
    }

    // pub fn compile should generate the circuit

    pub fn run(
        &self,
        i: [Ptr<F>; 3],
        store: &mut Store<F>,
    ) -> Result<([Ptr<F>; 3], HashMap<&'a str, Ptr<F>>, HashMap<&'a str, F>), String> {
        // key/val pairs on this map should never be overwritten
        let mut ptr_map: HashMap<&'a str, Ptr<F>> = HashMap::default();
        let mut var_map: HashMap<&'a str, F> = HashMap::default();
        ptr_map.insert(self.input[0], i[0]);
        if ptr_map.insert(self.input[1], i[1]).is_some() {
            return Err(format!("{} already defined", self.input[1]));
        }
        if ptr_map.insert(self.input[2], i[2]).is_some() {
            return Err(format!("{} already defined", self.input[2]));
        }
        let mut stack = vec![&self.lem_op];
        while let Some(op) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    let tgt_ptr = Ptr {
                        tag: *tag,
                        val: PtrVal::Null,
                    };
                    if ptr_map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Copy(tgt, src) => {
                    let Some(src_ptr) = ptr_map.get(src.name()) else {
                        return Err(format!("{} not defined", src.name()))
                    };
                    if ptr_map.insert(tgt.name(), *src_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash2Ptrs(tgt, tag, src) => {
                    let Some(src_ptr1) = ptr_map.get(src[0].name()) else {
                        return Err(format!("{} not defined", src[0].name()))
                    };
                    let Some(src_ptr2) = ptr_map.get(src[1].name()) else {
                        return Err(format!("{} not defined", src[1].name()))
                    };
                    let (idx, _) = store.ptrs2.insert_full((*src_ptr1, *src_ptr2));
                    let tgt_ptr = Ptr {
                        tag: *tag,
                        val: PtrVal::Index2(idx),
                    };
                    if ptr_map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash3Ptrs(tgt, tag, src) => {
                    let Some(src_ptr1) = ptr_map.get(src[0].name()) else {
                        return Err(format!("{} not defined", src[0].name()))
                    };
                    let Some(src_ptr2) = ptr_map.get(src[1].name()) else {
                        return Err(format!("{} not defined", src[1].name()))
                    };
                    let Some(src_ptr3) = ptr_map.get(src[2].name()) else {
                        return Err(format!("{} not defined", src[2].name()))
                    };
                    let (idx, _) = store.ptrs3.insert_full((*src_ptr1, *src_ptr2, *src_ptr3));
                    let tgt_ptr = Ptr {
                        tag: *tag,
                        val: PtrVal::Index3(idx),
                    };
                    if ptr_map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash4Ptrs(tgt, tag, src) => {
                    let Some(src_ptr1) = ptr_map.get(src[0].name()) else {
                        return Err(format!("{} not defined", src[0].name()))
                    };
                    let Some(src_ptr2) = ptr_map.get(src[1].name()) else {
                        return Err(format!("{} not defined", src[1].name()))
                    };
                    let Some(src_ptr3) = ptr_map.get(src[2].name()) else {
                        return Err(format!("{} not defined", src[2].name()))
                    };
                    let Some(src_ptr4) = ptr_map.get(src[3].name()) else {
                        return Err(format!("{} not defined", src[3].name()))
                    };
                    let (idx, _) = store
                        .ptrs4
                        .insert_full((*src_ptr1, *src_ptr2, *src_ptr3, *src_ptr4));
                    let tgt_ptr = Ptr {
                        tag: *tag,
                        val: PtrVal::Index4(idx),
                    };
                    if ptr_map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Unhash2Ptrs(tgts, src) => {
                    let Some(src_ptr) = ptr_map.get(src.name()) else {
                        return Err(format!("{} not defined", src.name()))
                    };
                    let Ptr { tag: _, val: PtrVal::Index2(idx)} = src_ptr else {
                        return Err(format!(
                            "{} is bound to a null pointer and can't be unhashed",
                            src.name()
                        ));
                    };
                    let Some((a, b)) = store.ptrs2.get_index(*idx) else {
                        return Err(format!("{} isn't bound to a 2-hashed pointer", src.name()))
                    };
                    if ptr_map.insert(tgts[0].name(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptr_map.insert(tgts[1].name(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                }
                LEMOP::Unhash3Ptrs(tgts, src) => {
                    let Some(src_ptr) = ptr_map.get(src.name()) else {
                        return Err(format!("{} not defined", src.name()))
                    };
                    let Ptr { tag: _, val: PtrVal::Index3(idx)} = src_ptr else {
                        return Err(format!(
                            "{} is bound to a null pointer and can't be unhashed",
                            src.name()
                        ));
                    };
                    let Some((a, b, c)) = store.ptrs3.get_index(*idx) else {
                        return Err(format!("{} isn't bound to a 3-hashed pointer", src.name()))
                    };
                    if ptr_map.insert(tgts[0].name(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptr_map.insert(tgts[1].name(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                    if ptr_map.insert(tgts[2].name(), *c).is_some() {
                        return Err(format!("{} already defined", tgts[2].name()));
                    }
                }
                LEMOP::Unhash4Ptrs(tgts, src) => {
                    let Some(src_ptr) = ptr_map.get(src.name()) else {
                        return Err(format!("{} not defined", src.name()))
                    };
                    let Ptr { tag: _, val: PtrVal::Index4(idx)} = src_ptr else {
                        return Err(format!(
                            "{} is bound to a null pointer and can't be unhashed",
                            src.name()
                        ));
                    };
                    let Some((a, b, c, d)) = store.ptrs4.get_index(*idx) else {
                        return Err(format!("{} isn't bound to a 4-hashed pointer", src.name()))
                    };
                    if ptr_map.insert(tgts[0].name(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptr_map.insert(tgts[1].name(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                    if ptr_map.insert(tgts[2].name(), *c).is_some() {
                        return Err(format!("{} already defined", tgts[2].name()));
                    }
                    if ptr_map.insert(tgts[3].name(), *d).is_some() {
                        return Err(format!("{} already defined", tgts[3].name()));
                    }
                }
                LEMOP::Hide(tgt, secret, src) => {
                    let Some(src_ptr) = ptr_map.get(src.name()) else {
                        return Err(format!("{} not defined", src.name()))
                    };
                    let aqua_ptr = store.hydrate_ptr(src_ptr)?;
                    let hash = store.poseidon_cache.hash3(&[*secret, aqua_ptr.tag.field(), aqua_ptr.val]);
                    let tgt_ptr = Ptr {
                        tag: Tag::Comm,
                        val: PtrVal::Field(hash),
                    };
                    store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                    if ptr_map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Open(tgt_secret, tgt_ptr, hash) => {
                    let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                        return Err(format!("No committed data for hash {}", hash.hex_digits()))
                    };
                    if ptr_map.insert(tgt_ptr.name(), *ptr).is_some() {
                        return Err(format!("{} already defined", tgt_ptr.name()));
                    }
                    if var_map.insert(tgt_secret.name(), *secret).is_some() {
                        return Err(format!("{} already defined", tgt_secret.name()));
                    }
                }
                LEMOP::IfTagEq(ptr, tag, tt, ff) => {
                    let Some(Ptr {tag: ptr_tag, val: _}) = ptr_map.get(ptr.name()) else {
                        return Err(format!("{} not defined", ptr.name()))
                    };
                    if ptr_tag == tag {
                        stack.push(tt)
                    } else {
                        stack.push(ff)
                    }
                }
                LEMOP::IfTagOr(ptr, tag1, tag2, tt, ff) => {
                    let Some(Ptr {tag: ptr_tag, val: _}) = ptr_map.get(ptr.name()) else {
                        return Err(format!("{} not defined", ptr.name()))
                    };
                    if ptr_tag == tag1 || ptr_tag == tag2 {
                        stack.push(tt)
                    } else {
                        stack.push(ff)
                    }
                }
                LEMOP::MatchTag(ptr, cases, def) => {
                    let Some(Ptr {tag: ptr_tag, val: _}) = ptr_map.get(ptr.name()) else {
                        return Err(format!("{} not defined", ptr.name()))
                    };
                    match cases.get(ptr_tag) {
                        Some(op) => stack.push(op),
                        None => stack.push(def),
                    }
                }
                LEMOP::Seq(ops) => stack.extend(ops.iter().rev()),
            }
        }
        let Some(out1) = ptr_map.get(self.output[0]) else {
            return Err(format!("Output {} not defined", self.output[0]))
        };
        let Some(out2) = ptr_map.get(self.output[1]) else {
            return Err(format!("Output {} not defined", self.output[1]))
        };
        let Some(out3) = ptr_map.get(self.output[2]) else {
            return Err(format!("Output {} not defined", self.output[2]))
        };
        Ok(([*out1, *out2, *out3], ptr_map, var_map))
    }

    pub fn eval(self, expr: Ptr<F>) -> Result<(Vec<StepData<'a, F>>, Store<F>), String> {
        let mut expr = expr;
        let mut env = Ptr {
            tag: Tag::Nil,
            val: PtrVal::Null,
        };
        let mut cont = Ptr {
            tag: Tag::Outermost,
            val: PtrVal::Null,
        };
        let mut steps_data = vec![];
        let mut store: Store<F> = Default::default();
        let terminal = Ptr {
            tag: Tag::Terminal,
            val: PtrVal::Null,
        };
        loop {
            let input = [expr, env, cont];
            let (output, ptrs, vals) = self.run(input, &mut store)?;
            steps_data.push(StepData {
                input,
                output,
                ptrs,
                vals,
            });
            if output[2] == terminal {
                break;
            } else {
                [expr, env, cont] = output;
            }
        }
        Ok((steps_data, store))
    }

    pub fn eval_res(self, expr: Ptr<F>) -> Result<(Ptr<F>, Store<F>), String> {
        let (steps_data, store) = self.eval(expr)?;
        Ok((
            steps_data
                .last()
                .expect("eval should add at least one step data")
                .output[0],
            store,
        ))
    }
}
