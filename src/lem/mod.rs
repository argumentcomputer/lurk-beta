mod eval;
mod lurk_symbol;
mod pointers;
mod store;
mod symbol;
mod tag;

use std::collections::HashMap;

use crate::{
    circuit::gadgets::{constraints::and_v_, pointer::AllocatedPtr},
    field::{FWrap, LurkField},
};

use self::{
    lurk_symbol::LurkSymbol,
    pointers::{AquaPtr, Ptr},
    store::Store,
    tag::Tag,
};

use crate::circuit::gadgets::constraints::enforce_equal;
use crate::circuit::gadgets::constraints::{
    alloc_equal, alloc_equal_const, enforce_implication, popcount,
};
use bellperson::gadgets::boolean::Boolean;
use bellperson::gadgets::num::AllocatedNum;
use bellperson::ConstraintSystem;

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
    lem_op: LEMOP<'a, F>,
}

#[derive(PartialEq, Clone, Copy, Eq, Hash)]
pub enum MetaPtr<'a> {
    Raw(&'a str),
    Ref(&'a str),
}

impl<'a> MetaPtr<'a> {
    #[inline]
    pub fn name(&self) -> &'a str {
        match self {
            Self::Raw(name) | Self::Ref(name) => name,
        }
    }

    pub fn get_ptr<F: LurkField>(
        &self,
        ref_map: &HashMap<&'a str, &'a str>,
        ptr_map: &HashMap<&'a str, Ptr<F>>,
    ) -> Result<Ptr<F>, String> {
        match self {
            Self::Raw(name) => match ptr_map.get(name) {
                None => Err(format!("Pointer {} not defined", name)),
                Some(ptr) => Ok(*ptr),
            },
            Self::Ref(ref_name) => match ref_map.get(ref_name) {
                None => Err(format!("Reference {} not defined", ref_name)),
                Some(name) => match ptr_map.get(name) {
                    None => Err(format!(
                        "Pointer {} not defined (referenced by {})",
                        name, ref_name
                    )),
                    Some(ptr) => Ok(*ptr),
                },
            },
        }
    }
}

#[derive(PartialEq, Clone, Copy, Eq, Hash)]
pub struct MetaVar<'a>(&'a str);

impl<'a> MetaVar<'a> {
    #[inline]
    pub fn name(self) -> &'a str {
        self.0
    }
}

#[derive(Clone)]
pub enum LEMOP<'a, F: LurkField> {
    MkNull(&'a str, Tag),
    MkRef(&'a str, &'a str),
    Hash2Ptrs(&'a str, Tag, [MetaPtr<'a>; 2]),
    Hash3Ptrs(&'a str, Tag, [MetaPtr<'a>; 3]),
    Hash4Ptrs(&'a str, Tag, [MetaPtr<'a>; 4]),
    Unhash2Ptrs([&'a str; 2], MetaPtr<'a>),
    Unhash3Ptrs([&'a str; 3], MetaPtr<'a>),
    Unhash4Ptrs([&'a str; 4], MetaPtr<'a>),
    Hide(&'a str, F, MetaPtr<'a>),
    Open(&'a str, &'a str, F), // secret, tgt, src hash
    IfTagEq(MetaPtr<'a>, Tag, Box<LEMOP<'a, F>>, Box<LEMOP<'a, F>>),
    IfTagOr(MetaPtr<'a>, Tag, Tag, Box<LEMOP<'a, F>>, Box<LEMOP<'a, F>>),
    MatchTag(MetaPtr<'a>, HashMap<Tag, LEMOP<'a, F>>),
    MatchLeafVal(MetaPtr<'a>, HashMap<FWrap<F>, LEMOP<'a, F>>),
    Seq(Vec<LEMOP<'a, F>>),
    SetReturn([MetaPtr<'a>; 3]),
}

impl<'a, F: LurkField> LEMOP<'a, F> {
    #[inline]
    pub fn mk_match_tag(i: MetaPtr<'a>, cases: Vec<(Tag, LEMOP<'a, F>)>) -> LEMOP<'a, F> {
        LEMOP::MatchTag(i, HashMap::from_iter(cases))
    }
}

pub struct Witness<'a, F: LurkField> {
    input: [Ptr<F>; 3],
    output: [Ptr<F>; 3],
    refs: HashMap<&'a str, &'a str>,
    ptrs: HashMap<&'a str, Ptr<F>>,
    vars: HashMap<&'a str, F>,
}

impl<'a, F: LurkField> LEM<'a, F> {
    pub fn check(&self) {
        // TODO
    }

    pub fn run(
        &self,
        i: [Ptr<F>; 3],
        store: &mut Store<F>,
    ) -> Result<
        (
            [Ptr<F>; 3],
            HashMap<&'a str, &'a str>,
            HashMap<&'a str, Ptr<F>>,
            HashMap<&'a str, F>,
        ),
        String,
    > {
        // key/val pairs on this map should never be overwritten
        let mut ref_map = HashMap::default();
        let mut ptr_map = HashMap::default();
        let mut var_map = HashMap::default();
        ptr_map.insert(self.input[0], i[0]);
        if ptr_map.insert(self.input[1], i[1]).is_some() {
            return Err(format!("{} already defined", self.input[1]));
        }
        if ptr_map.insert(self.input[2], i[2]).is_some() {
            return Err(format!("{} already defined", self.input[2]));
        }
        let mut out1: Option<Ptr<F>> = None;
        let mut out2: Option<Ptr<F>> = None;
        let mut out3: Option<Ptr<F>> = None;
        let mut stack = vec![&self.lem_op];
        while let Some(op) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    let tgt_ptr = Ptr::null(*tag);
                    if ptr_map.insert(tgt, tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt));
                    }
                }
                LEMOP::MkRef(tgt, src) => {
                    ref_map.insert(*tgt, *src);
                }
                LEMOP::Hash2Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ref_map, &ptr_map)?;
                    let src_ptr2 = src[1].get_ptr(&ref_map, &ptr_map)?;
                    let tgt_ptr = store.index_2_ptrs(*tag, src_ptr1, src_ptr2);
                    if ptr_map.insert(tgt, tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt));
                    }
                }
                LEMOP::Hash3Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ref_map, &ptr_map)?;
                    let src_ptr2 = src[1].get_ptr(&ref_map, &ptr_map)?;
                    let src_ptr3 = src[2].get_ptr(&ref_map, &ptr_map)?;
                    let tgt_ptr = store.index_3_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3);
                    if ptr_map.insert(tgt, tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt));
                    }
                }
                LEMOP::Hash4Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ref_map, &ptr_map)?;
                    let src_ptr2 = src[1].get_ptr(&ref_map, &ptr_map)?;
                    let src_ptr3 = src[2].get_ptr(&ref_map, &ptr_map)?;
                    let src_ptr4 = src[3].get_ptr(&ref_map, &ptr_map)?;
                    let tgt_ptr = store.index_4_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3, src_ptr4);
                    if ptr_map.insert(tgt, tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt));
                    }
                }
                LEMOP::Unhash2Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ref_map, &ptr_map)?;
                    let Some(idx) = src_ptr.get_index2() else {
                        return Err(format!(
                            "{} isn't a Tree2 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptr_map.insert(tgts[0], *a).is_some() {
                        return Err(format!("{} already defined", tgts[0]));
                    }
                    if ptr_map.insert(tgts[1], *b).is_some() {
                        return Err(format!("{} already defined", tgts[1]));
                    }
                }
                LEMOP::Unhash3Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ref_map, &ptr_map)?;
                    let Some(idx) = src_ptr.get_index3() else {
                        return Err(format!(
                            "{} isn't a Tree3 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptr_map.insert(tgts[0], *a).is_some() {
                        return Err(format!("{} already defined", tgts[0]));
                    }
                    if ptr_map.insert(tgts[1], *b).is_some() {
                        return Err(format!("{} already defined", tgts[1]));
                    }
                    if ptr_map.insert(tgts[2], *c).is_some() {
                        return Err(format!("{} already defined", tgts[2]));
                    }
                }
                LEMOP::Unhash4Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ref_map, &ptr_map)?;
                    let Some(idx) = src_ptr.get_index4() else {
                        return Err(format!(
                            "{} isn't a Tree4 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptr_map.insert(tgts[0], *a).is_some() {
                        return Err(format!("{} already defined", tgts[0]));
                    }
                    if ptr_map.insert(tgts[1], *b).is_some() {
                        return Err(format!("{} already defined", tgts[1]));
                    }
                    if ptr_map.insert(tgts[2], *c).is_some() {
                        return Err(format!("{} already defined", tgts[2]));
                    }
                    if ptr_map.insert(tgts[3], *d).is_some() {
                        return Err(format!("{} already defined", tgts[3]));
                    }
                }
                LEMOP::Hide(tgt, secret, src) => {
                    let src_ptr = src.get_ptr(&ref_map, &ptr_map)?;
                    let aqua_ptr = store.hydrate_ptr(&src_ptr)?;
                    let hash =
                        store
                            .poseidon_cache
                            .hash3(&[*secret, aqua_ptr.tag.field(), aqua_ptr.val]);
                    let tgt_ptr = Ptr::comm(hash);
                    store.comms.insert(FWrap::<F>(hash), (*secret, src_ptr));
                    if ptr_map.insert(tgt, tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt));
                    }
                }
                LEMOP::Open(tgt_secret, tgt_ptr, hash) => {
                    let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                        return Err(format!("No committed data for hash {}", hash.hex_digits()))
                    };
                    if ptr_map.insert(tgt_ptr, *ptr).is_some() {
                        return Err(format!("{} already defined", tgt_ptr));
                    }
                    if var_map.insert(*tgt_secret, *secret).is_some() {
                        return Err(format!("{} already defined", tgt_secret));
                    }
                }
                LEMOP::IfTagEq(ptr, tag, tt, ff) => {
                    let Some(ptr) = ptr_map.get(ptr.name()) else {
                        return Err(format!("{} not defined", ptr.name()))
                    };
                    if ptr.tag() == tag {
                        stack.push(tt)
                    } else {
                        stack.push(ff)
                    }
                }
                LEMOP::IfTagOr(ptr, tag1, tag2, tt, ff) => {
                    let Some(ptr) = ptr_map.get(ptr.name()) else {
                        return Err(format!("{} not defined", ptr.name()))
                    };
                    let ptr_tag = ptr.tag();
                    if ptr_tag == tag1 || ptr_tag == tag2 {
                        stack.push(tt)
                    } else {
                        stack.push(ff)
                    }
                }
                LEMOP::MatchTag(ptr, cases) => {
                    let Some(ptr) = ptr_map.get(ptr.name()) else {
                        return Err(format!("{} not defined", ptr.name()))
                    };
                    let ptr_tag = ptr.tag();
                    match cases.get(ptr_tag) {
                        Some(op) => stack.push(op),
                        None => return Err(format!("No match for tag {:?}", ptr_tag)),
                    }
                }
                LEMOP::MatchLeafVal(ptr, cases) => {
                    let Some(Ptr::Leaf(_, f)) = ptr_map.get(ptr.name()) else {
                        return Err(format!("{} not defined as a pointer with a field value", ptr.name()))
                    };
                    match cases.get(&FWrap(*f)) {
                        Some(op) => stack.push(op),
                        None => {
                            return Err(format!("No match for field element {}", f.hex_digits()))
                        }
                    }
                }
                LEMOP::Seq(ops) => stack.extend(ops.iter().rev()),
                LEMOP::SetReturn(o) => {
                    out1 = ptr_map.get(&o[0].name()).map(|x| *x);
                    out2 = ptr_map.get(&o[1].name()).map(|x| *x);
                    out3 = ptr_map.get(&o[2].name()).map(|x| *x);
                }
            }
        }
        let Some(out1) = out1 else {
            return Err("Output 1 not defined".to_string());
        };
        let Some(out2) = out2 else {
            return Err("Output 2 not defined".to_string());
        };
        let Some(out3) = out3 else {
            return Err("Output 3 not defined".to_string());
        };
        Ok(([out1, out2, out3], ref_map, ptr_map, var_map))
    }

    pub fn eval(&self, expr: Ptr<F>) -> Result<(Vec<Witness<'a, F>>, Store<F>), String> {
        let mut expr = expr;
        let mut env = Ptr::lurk_sym(LurkSymbol::Nil);
        let mut cont = Ptr::null(Tag::Outermost);
        let mut witnesses = vec![];
        let mut store: Store<F> = Default::default();
        let terminal = Ptr::null(Tag::Terminal);
        loop {
            let input = [expr, env, cont];
            let (output, refs, ptrs, vars) = self.run(input, &mut store)?;
            witnesses.push(Witness {
                input,
                output,
                refs,
                ptrs,
                vars,
            });
            if output[2] == terminal {
                break;
            } else {
                [expr, env, cont] = output;
            }
        }
        Ok((witnesses, store))
    }

    pub fn eval_res(&self, expr: Ptr<F>) -> Result<(Ptr<F>, Store<F>), String> {
        let (witnesses, store) = self.eval(expr)?;
        Ok((
            witnesses
                .last()
                .expect("eval should add at least one step data")
                .output[0],
            store,
        ))
    }

    fn allocate_input_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        ptr: &Ptr<F>,
        name: String,
        store: &mut Store<F>,
    ) -> Result<AllocatedPtr<F>, String> {
        let aqua_ptr = store.hydrate_ptr(ptr)?;
        let Ok(alloc_tag) = AllocatedNum::alloc(cs.namespace(|| format!("alloc {}'s tag", name)), || {
            Ok(aqua_ptr.tag.field())
        }) else {
            return Err(format!("Couldn't allocate tag for {}", name))
        };
        let Ok(alloc_val) = AllocatedNum::alloc(cs.namespace(|| format!("alloc {}'s val", name)), || {
            Ok(aqua_ptr.val)
        }) else {
            return Err(format!("Couldn't allocate val for {}", name))
        };

        let Ok(_) = alloc_tag.inputize(cs.namespace(|| format!("inputize tag for {}", name))) else {
            return Err(format!("Couldn't inputize tag for {}", name))
        };
        let Ok(_) = alloc_val.inputize(cs.namespace(|| format!("inputize val for {}", name))) else {
            return Err(format!("Couldn't inputize val for {}", name))
        };

        Ok(AllocatedPtr::from_parts(&alloc_tag, &alloc_val))
    }

    fn allocate_ptr_from_witness<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        aqua_ptr: AquaPtr<F>,
        name: &'a str,
    ) -> Result<AllocatedPtr<F>, String> {
        let Ok(alloc_tag) = AllocatedNum::alloc(cs.namespace(|| format!("alloc {}'s tag", name)), || {
            Ok(aqua_ptr.tag.field())
        }) else {
            return Err(format!("Couldn't allocate tag for {}", name))
        };
        let Ok(alloc_val) = AllocatedNum::alloc(cs.namespace(|| format!("alloc {}'s val", name)), || {
            Ok(aqua_ptr.val)
        }) else {
            return Err(format!("Couldn't allocate val for {}", name))
        };
        Ok(AllocatedPtr::from_parts(&alloc_tag, &alloc_val))
    }

    fn enforce_equal_ptrs<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: &AllocatedPtr<F>,
        a_name: String,
        b: &AllocatedPtr<F>,
        b_name: String,
    ) {
        enforce_equal(
            cs,
            || format!("{}'s tag equals {}'s tag", a_name, b_name),
            &a.tag(),
            &b.tag(),
        );
        enforce_equal(
            cs,
            || format!("{}'s val equals {}'s val", a_name, b_name),
            &a.hash(),
            &b.hash(),
        );
    }

    fn implies_equal<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        premise: &Boolean,
        a: &AllocatedNum<F>,
        b: &AllocatedNum<F>,
    ) -> Result<(), String> {
        let Ok(is_equal) = alloc_equal(cs.namespace(|| "is_equal"), a, b) else {
            return Err("TODO".to_string())
        };
        let Ok(_) = enforce_implication(
            cs.namespace(|| "not dummy implies tag is equal"),
            premise,
            &is_equal
        ) else {
            return Err("TODO".to_string())
        };
        Ok(())
    }

    fn implies_ptr_equal<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        not_dummy: &Boolean,
        ptr_a: &AllocatedPtr<F>,
        a_name: String,
        ptr_b: &AllocatedPtr<F>,
        b_name: String,
    ) -> Result<(), String> {
        Self::implies_equal(
            &mut cs.namespace(|| format!("implies tag equal for {} and {}", a_name, b_name)),
            not_dummy,
            ptr_a.tag(),
            ptr_b.tag(),
        )?;
        Self::implies_equal(
            &mut cs.namespace(|| format!("implies hash equal for {} and {}", a_name, b_name)),
            not_dummy,
            ptr_a.hash(),
            ptr_b.hash(),
        )?;
        Ok(())
    }

    // TODO: remove dependency on `potential_assignments` and set dummy values on the fly
    //       to avoid doing it twice for the same meta data
    pub fn constrain<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &mut Store<F>,
        witness: &Witness<'a, F>,
    ) -> Result<(), String> {
        let mut alloc_ptrs: HashMap<&'a str, AllocatedPtr<F>> = HashMap::default();

        // allocate first input
        {
            let Some(ptr) = witness.ptrs.get(self.input[0]) else {
                return Err("TODO".to_string())
            };
            alloc_ptrs.insert(
                self.input[0],
                Self::allocate_input_ptr(cs, ptr, format!("input {}", self.input[0]), store)?,
            );
        }

        // allocate second input
        {
            if alloc_ptrs.contains_key(self.input[1]) {
                return Err(format!("{} already allocated", self.input[1]));
            }
            let Some(ptr) = witness.ptrs.get(self.input[1]) else {
                return Err("TODO".to_string())
            };
            alloc_ptrs.insert(
                self.input[1],
                Self::allocate_input_ptr(cs, ptr, format!("input {}", self.input[1]), store)?,
            );
        }

        // allocate third input
        {
            if alloc_ptrs.contains_key(self.input[2]) {
                return Err(format!("{} already allocated", self.input[2]));
            }
            let Some(ptr) = witness.ptrs.get(self.input[2]) else {
                return Err("TODO".to_string())
            };
            alloc_ptrs.insert(
                self.input[2],
                Self::allocate_input_ptr(cs, ptr, format!("input {}", self.input[2]), store)?,
            );
        }

        // TODO: consider greating globals
        let zero = AllocatedNum::alloc(cs.namespace(|| "#zero"), || Ok(F::zero())).unwrap();
        let one = AllocatedNum::alloc(cs.namespace(|| "#one"), || Ok(F::one())).unwrap();
        let mut stack = vec![(&self.lem_op, None::<Boolean>, Vec::new())];
        while let Some((op, not_dummy, path)) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    if alloc_ptrs.contains_key(tgt) {
                        return Err(format!("{} already allocated", tgt));
                    };
                    let aqua_ptr = match not_dummy.clone() {
                        None => {
                            let Some(ptr) = witness.ptrs.get(tgt) else {
                                return Err("TODO".to_string());
                            };
                            store.hydrate_ptr(ptr)?
                        }
                        Some(not_dummy) => {
                            if not_dummy.get_value().unwrap() {
                                let Some(ptr) = witness.ptrs.get(tgt) else {
                                    return Err("TODO".to_string());
                                };
                                store.hydrate_ptr(ptr)?
                            } else {
                                AquaPtr {
                                    tag: Tag::Dummy,
                                    val: F::zero(),
                                }
                            }
                        }
                    };
                    let alloc_tgt = Self::allocate_ptr_from_witness(cs, aqua_ptr, tgt)?;
                    alloc_ptrs.insert(tgt, alloc_tgt.clone());
                    let Ok(alloc_tag) = AllocatedNum::alloc(              //  take from globals
                        cs.namespace(|| format!("{}'s tag", tgt)),
                        || Ok(tag.field()),
                    ) else {
                        return Err(format!("Couldn't allocate tag for {}", tgt));
                    };

                    if let Some(not_dummy) = not_dummy {
                        Self::implies_equal(
                            &mut cs.namespace(|| format!("{:?}.tag_is_equal", path.join("."))),
                            &not_dummy,
                            alloc_tgt.tag(),
                            &alloc_tag,
                        )?;
                        Self::implies_equal(
                            &mut cs.namespace(|| format!("{:?}.hash_is_equal", path.join("."))),
                            &not_dummy,
                            alloc_tgt.hash(),
                            &zero,
                        )?;
                    } else {
                        enforce_equal(
                            cs,
                            || format!("{}'s tag is {}", tgt, tag.field::<F>().hex_digits()),
                            &alloc_tgt.tag(),
                            &alloc_tag,
                        );
                        enforce_equal(
                            cs,
                            || format!("{}'s val is zero", tgt),
                            &alloc_tgt.hash(),
                            &zero,
                        );
                    }
                }
                LEMOP::MatchTag(match_ptr, cases) => {
                    let Some(alloc_match_ptr) = alloc_ptrs.get(match_ptr.name()) else {
                        return Err(format!("{} not allocated", match_ptr.name()));
                    };
                    let mut not_dummy_vec = Vec::new();
                    for (i, (tag, op)) in cases.iter().enumerate() {
                        let Ok(alloc_has_match) = alloc_equal_const(
                            &mut cs.namespace(
                                || format!("{}.alloc_has_match item:{}, tag:{:?}", path.join("."), i, tag.field::<F>())
                            ),
                            alloc_match_ptr.tag(),
                            tag.field::<F>(),
                        ) else {
                            return Err("Allocated variable does not has the expected tag".to_string());
                        };
                        not_dummy_vec.push(alloc_has_match.clone());

                        let mut new_path_matchtag = path.clone();
                        new_path_matchtag.push("MatchTag.");
                        if let Some(not_dummy) = not_dummy.clone() {
                            let Ok(not_dummy_and_has_match) = and_v_(cs, &[&not_dummy, &alloc_has_match]) else {
                                return Err("TODO".to_string());
                            };
                            stack.push((op, Some(not_dummy_and_has_match), new_path_matchtag));
                        } else {
                            stack.push((op, Some(alloc_has_match), new_path_matchtag));
                        }
                    }

                    let Ok(_) = popcount(
                        &mut cs.namespace(|| format!("{}.popcount", path.join("."))),
                        &not_dummy_vec[..],
                        &one,
                    ) else {
                        return Err("Failed to constrain popcount gadget".to_string())
                    };
                }
                LEMOP::Seq(ops) => {
                    let mut new_path_seq = path.clone();
                    new_path_seq.push("Seq.");
                    stack.extend(
                        ops.iter()
                            .rev()
                            .map(|op| (op, not_dummy.clone(), new_path_seq.clone())),
                    )
                }
                LEMOP::SetReturn(outputs) => {
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(alloc_ptr_computed) = alloc_ptrs.get(output.name()) else {
                            return Err("Could not find output allocated in the circuit".to_string())
                        };
                        let Some(ptr_expected) = witness.ptrs.get(output.name()) else {
                            return Err("Could not find the expected witness".to_string())
                        };
                        let alloc_ptr_expected = Self::allocate_input_ptr(
                            cs,
                            ptr_expected,
                            format!("{}.output {}", path.join("."), i),
                            store,
                        )?;

                        if let Some(not_dummy) = not_dummy.clone() {
                            let Ok(_) = Self::implies_ptr_equal(
                                cs,
                                &not_dummy,
                                alloc_ptr_computed,
                                format!("{}.computed output {}", path.join("."), i),
                                &alloc_ptr_expected,
                                format!("{}.expected output {}", path.join("."), i)
                            ) else {
                                return Err("Failed to constrain implies_ptr_equal".to_string())
                            };
                        } else {
                            Self::enforce_equal_ptrs(
                                cs,
                                alloc_ptr_computed,
                                format!("{}.computed output {}", path.join("."), i),
                                &alloc_ptr_expected,
                                format!("{}.expected output {}", path.join("."), i),
                            );
                        }
                    }
                }
                _ => todo!(),
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lem::{pointers::Ptr, tag::Tag};
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;

    #[test]
    fn accepts_dummy_nested_match_tag() {
        let input = ["expr_in", "env_in", "cont_in"];
        let lem_op = LEMOP::mk_match_tag(
            MetaPtr::Raw("expr_in"),
            vec![
                (
                    Tag::Num,
                    LEMOP::Seq(vec![
                        LEMOP::MkNull("cont_out_terminal", Tag::Terminal),
                        LEMOP::SetReturn([
                            MetaPtr::Raw("expr_in"),
                            MetaPtr::Raw("env_in"),
                            MetaPtr::Raw("cont_out_terminal"),
                        ]),
                    ]),
                ),
                (
                    Tag::Char,
                    LEMOP::mk_match_tag(
                        // this nested match excercises the need to pass on the information
                        // that we are on a dummy branch, because a constrain will
                        // be created for `cont_out_error` and it will need to be relaxed
                        // by an implication with a false premise
                        MetaPtr::Raw("expr_in"),
                        vec![(
                            Tag::Num,
                            LEMOP::Seq(vec![
                                LEMOP::MkNull("cont_out_error", Tag::Error),
                                LEMOP::SetReturn([
                                    MetaPtr::Raw("expr_in"),
                                    MetaPtr::Raw("env_in"),
                                    MetaPtr::Raw("cont_out_error"),
                                ]),
                            ]),
                        )],
                    ),
                ),
                (
                    Tag::Sym,
                    LEMOP::mk_match_tag(
                        // this nested match exercises the need to relax `popcount`
                        // because there is no match but it's on a dummy path, so
                        // we don't want to be too restrictive
                        MetaPtr::Raw("expr_in"),
                        vec![(
                            Tag::Char,
                            LEMOP::SetReturn([
                                MetaPtr::Raw("expr_in"),
                                MetaPtr::Raw("env_in"),
                                MetaPtr::Raw("cont_in"),
                            ]),
                        )],
                    ),
                ),
            ],
        );
        let lem: LEM<'static, Fr> = LEM { input, lem_op };

        let expr = Ptr::num(Fr::from_u64(42));
        let (res, mut store) = lem.eval(expr).unwrap();
        for w in res.iter() {
            let mut cs = TestConstraintSystem::<Fr>::new();
            lem.constrain(&mut cs, &mut store, w).unwrap();
            assert!(cs.is_satisfied());
        }
    }
}
