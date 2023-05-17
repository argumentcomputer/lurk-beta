mod eval;
mod lurk_symbol;
mod pointers;
mod store;
mod symbol;
mod tag;

use std::collections::{HashMap, HashSet};

use crate::{
    circuit::gadgets::{constraints::all_booleans_are_false, pointer::AllocatedPtr},
    field::{FWrap, LurkField},
};

use self::{
    pointers::{Ptr, PtrVal},
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
pub struct MetaPtr<'a>(&'a str);

impl<'a> MetaPtr<'a> {
    #[inline]
    pub fn name(self) -> &'a str {
        self.0
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
    MatchTag(MetaPtr<'a>, HashMap<Tag, LEMOP<'a, F>>, Box<LEMOP<'a, F>>),
    MatchFieldVal(
        MetaPtr<'a>,
        HashMap<FWrap<F>, LEMOP<'a, F>>,
        Box<LEMOP<'a, F>>,
    ),
    Seq(Vec<LEMOP<'a, F>>),
    SetReturn([MetaPtr<'a>; 3]),
}

impl<'a, F: LurkField> LEMOP<'a, F> {
    #[inline]
    pub fn mk_match_tag(
        i: MetaPtr<'a>,
        cases: Vec<(Tag, LEMOP<'a, F>)>,
        def: LEMOP<'a, F>,
    ) -> LEMOP<'a, F> {
        LEMOP::MatchTag(i, HashMap::from_iter(cases), Box::new(def))
    }

    pub fn potential_assignments(&self) -> (HashSet<MetaPtr<'a>>, HashSet<MetaVar<'a>>) {
        let mut ptrs_set = HashSet::default();
        let mut vars_set = HashSet::default();
        let mut stack = vec![self];
        while let Some(op) = stack.pop() {
            match op {
                LEMOP::MkNull(ptr, _)
                | LEMOP::Copy(ptr, _)
                | LEMOP::Hash2Ptrs(ptr, ..)
                | LEMOP::Hash3Ptrs(ptr, ..)
                | LEMOP::Hash4Ptrs(ptr, ..)
                | LEMOP::Hide(ptr, ..) => {
                    ptrs_set.insert(*ptr);
                }
                LEMOP::Unhash2Ptrs([a, b], _) => {
                    ptrs_set.insert(*a);
                    ptrs_set.insert(*b);
                }
                LEMOP::Unhash3Ptrs([a, b, c], _) => {
                    ptrs_set.insert(*a);
                    ptrs_set.insert(*b);
                    ptrs_set.insert(*c);
                }
                LEMOP::Unhash4Ptrs([a, b, c, d], _) => {
                    ptrs_set.insert(*a);
                    ptrs_set.insert(*b);
                    ptrs_set.insert(*c);
                    ptrs_set.insert(*d);
                }
                LEMOP::Open(v, p, _) => {
                    ptrs_set.insert(*p);
                    vars_set.insert(*v);
                }
                LEMOP::IfTagEq(.., a, b) | LEMOP::IfTagOr(.., a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                LEMOP::MatchTag(_, cases, def) => {
                    for op in cases.values() {
                        stack.push(op);
                    }
                    stack.push(def);
                }
                LEMOP::MatchFieldVal(_, cases, def) => {
                    for op in cases.values() {
                        stack.push(op);
                    }
                    stack.push(def);
                }
                LEMOP::Seq(ops) => {
                    stack.extend(ops.iter());
                }
                LEMOP::SetReturn(_) => {}
            }
        }
        (ptrs_set, vars_set)
    }

    //         LEMOP::MatchTag(ptr, cases, def) => {
    //             let mut output_names = Vec::new();
    //             let mut multiclauses: Vec<Vec<CaseClause<'_, F>>> = Vec::new();
    //             for var_name in cases.iter() {
    //                 let clauses: Vec<CaseClause<'_, F>> = Vec::new();
    //                 multiclauses.push(clauses);
    //             }

    //             for (key, c_op) in cases.iter() {
    //                 // Recursively construct the circuit for c_op

    //                 let clause_output_var_names = c_op.compile(cs, g.clone(), alloc_vars)?;

    //                 for (i, var_name) in clause_output_var_names.iter().enumerate() {
    //                     let alloc_var = match alloc_vars.get(var_name.clone()) {
    //                         Some(v) => v,
    //                         None => panic!("xii3"),
    //                     };
    //                     multiclauses[i].push(CaseClause {
    //                         key: key.field(),
    //                         value: alloc_var,
    //                     });
    //                 }
    //             }
    //             // Recursively construct circuit for def
    //             let default_output_var_names = def.compile(cs, g.clone(), alloc_vars)?;
    //             // create default
    //             let mut default = vec![];
    //             for name in default_output_var_names {
    //                 let var = alloc_vars.get(name.clone());
    //                 let var = match var {
    //                     Some(v) => v,
    //                     None => panic!("xii5"),
    //                 };
    //                 default.push(var);
    //             }

    //             // Convert multiclauses
    //             let m = multiclauses
    //                 .iter()
    //                 .map(|v| v.as_slice())
    //                 .collect::<Vec<&[CaseClause<'a, F>]>>()
    //                 .as_slice();

    //             let ptr_tag = match alloc_vars.get(ptr.name()) {
    //                 Some(p) => p,
    //                 None => panic!("xii6"),
    //             };

    //             // create multicase
    //             let result = multi_case(
    //                 &mut cs.namespace(|| "multicase"),
    //                 &ptr_tag,
    //                 &m,
    //                 &default[..],
    //                 &g.clone(),
    //             );

    //             let result = match result {
    //                 Ok(r) => r,
    //                 Err(_) => panic!("xii7"),
    //             };
    //             // TODO: Glue: here we have a potential soundness problems, double check
    //             for (i, elem) in result.iter().enumerate() {
    //                 let mut result_name = format!("match_result_{}", i);
    //                 alloc_vars.insert(&mut result_name[..], elem.clone());
    //                 output_names.push(&result_name[..])
    //             }
    //             output_names
    //         }
}

pub struct Witness<'a, F: LurkField> {
    input: [Ptr<F>; 3],
    output: [Ptr<F>; 3],
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
    ) -> Result<([Ptr<F>; 3], HashMap<&'a str, Ptr<F>>, HashMap<&'a str, F>), String> {
        // key/val pairs on this map should never be overwritten
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
                    let tgt_ptr = store.index_2_ptrs(*tag, *src_ptr1, *src_ptr2);
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
                    let tgt_ptr = store.index_3_ptrs(*tag, *src_ptr1, *src_ptr2, *src_ptr3);
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
                    let tgt_ptr =
                        store.index_4_ptrs(*tag, *src_ptr1, *src_ptr2, *src_ptr3, *src_ptr4);
                    if ptr_map.insert(tgt.name(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Unhash2Ptrs(tgts, src) => {
                    let Some(src_ptr) = ptr_map.get(src.name()) else {
                        return Err(format!("{} not defined", src.name()))
                    };
                    let Some(idx) = src_ptr.get_index2() else {
                        return Err(format!(
                            "{} is bound to a leaf pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b)) = store.fetch_2_ptrs(idx) else {
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
                    let Some(idx) = src_ptr.get_index3() else {
                        return Err(format!(
                            "{} is bound to a leaf pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
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
                    let Some(idx) = src_ptr.get_index4() else {
                        return Err(format!(
                            "{} is bound to a leaf pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
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
                    let hash =
                        store
                            .poseidon_cache
                            .hash3(&[*secret, aqua_ptr.tag.field(), aqua_ptr.val]);
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
                LEMOP::MatchFieldVal(ptr, cases, def) => {
                    let Some(Ptr {tag: _, val: PtrVal::Field(f)}) = ptr_map.get(ptr.name()) else {
                        return Err(format!("{} not defined as a pointer with a field value", ptr.name()))
                    };
                    match cases.get(&FWrap(*f)) {
                        Some(op) => stack.push(op),
                        None => stack.push(def),
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
        Ok(([out1, out2, out3], ptr_map, var_map))
    }

    fn allocate_ptr_from_witness<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        name: &'a str,
        store: &mut Store<F>,
        ptr_witness: &HashMap<&'a str, Ptr<F>>,
    ) -> Result<AllocatedPtr<F>, String> {
        let Some(ptr) = ptr_witness.get(name) else {
            return Err(format!("Couldn't find {} in the witness", name))
        };
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
        Ok(AllocatedPtr::from_parts(&alloc_tag, &alloc_val))
    }

    // fn enforce_equal_ptrs<CS: ConstraintSystem<F>>(
    //     cs: &mut CS,
    //     a: &AllocatedPtr<F>,
    //     a_name: &str,
    //     b: &AllocatedPtr<F>,
    //     b_name: &str,
    // ) {
    //     enforce_equal(
    //         cs,
    //         || format!("{}'s tag equals {}'s tag", a_name, b_name),
    //         &a.tag(),
    //         &b.tag(),
    //     );
    //     enforce_equal(
    //         cs,
    //         || format!("{}'s val equals {}'s val", a_name, b_name),
    //         &a.hash(),
    //         &b.hash(),
    //     );
    // }

    fn implies_equal<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        not_dummy: &Boolean,
        a: &AllocatedNum<F>,
        b: &AllocatedNum<F>,
    ) -> Result<(), String> {
        let Ok(is_equal) = alloc_equal(&mut cs.namespace(|| "is_equal"), a, b) else {
            return Err("TODO".to_string())
        };
        let Ok(_) = enforce_implication(
            &mut cs.namespace(|| "not dummy implies tag is equal"),
            not_dummy,
            &is_equal
        ) else {
            return Err("TODO".to_string())
        };
        Ok(())
    }

    /*pub(crate) fn implies_ptr_equal<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        not_dummy: Boolean,
        ptr_a: AllocatedPtr<F>,
        ptr_b: AllocatedPtr<F>,
    ) -> Result<(), String> {
        Self::implies_equal(&mut cs.namespace(|| "implies tag equal"), &not_dummy, ptr_a.tag(), ptr_b.tag())?;
        Self::implies_equal(&mut cs.namespace(|| "implies hash equal"), &not_dummy, ptr_a.hash(), ptr_b.hash())?;
        Ok(())
    }*/

    pub fn constrain<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &mut Store<F>,
        witness: &Witness<'a, F>,
    ) -> Result<(), String> {
        let mut alloc_ptrs: HashMap<&'a str, AllocatedPtr<F>> = HashMap::default();
        let mut ptrs_witness = witness.ptrs.clone();
        let mut vars_witness = witness.vars.clone();

        // allocate first input
        {
            alloc_ptrs.insert(
                self.input[0],
                Self::allocate_ptr_from_witness(cs, self.input[0], store, &ptrs_witness)?,
            );
        }

        // allocate second input
        {
            if alloc_ptrs.contains_key(self.input[1]) {
                return Err(format!("{} already allocated", self.input[1]));
            }
            alloc_ptrs.insert(
                self.input[1],
                Self::allocate_ptr_from_witness(cs, self.input[1], store, &ptrs_witness)?,
            );
        }

        // allocate third input
        {
            if alloc_ptrs.contains_key(self.input[2]) {
                return Err(format!("{} already allocated", self.input[2]));
            }
            alloc_ptrs.insert(
                self.input[2],
                Self::allocate_ptr_from_witness(cs, self.input[2], store, &ptrs_witness)?,
            );
        }

        // TODO: consider greating globals
        let zero = AllocatedNum::alloc(cs.namespace(|| "#zero"), || Ok(F::zero())).unwrap();
        let one = AllocatedNum::alloc(cs.namespace(|| "#one"), || Ok(F::one())).unwrap();
        let mut stack = vec![(&self.lem_op, None)];
        while let Some((op, not_dummy)) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    if alloc_ptrs.contains_key(tgt.name()) {
                        return Err(format!("{} already allocated", tgt.name()));
                    }
                    let alloc_tgt =
                        Self::allocate_ptr_from_witness(cs, tgt.name(), store, &ptrs_witness)?;
                    let Ok(alloc_tag) = AllocatedNum::alloc(              //  take from globals
                        cs.namespace(|| format!("{}'s tag", tgt.name())),
                        || Ok(tag.field()),
                    ) else {
                        return Err(format!("Couldn't allocate tag for {}", tgt.name()));
                    };

                    if let Some(not_dummy) = not_dummy {
                        Self::implies_equal(
                            // TODO: improve namespace
                            &mut cs.namespace(|| {
                                format!("tag_is_equal_{:?}_{:?}", alloc_tag.get_value(), tgt.name())
                            }),
                            &not_dummy,
                            alloc_tgt.tag(),
                            &alloc_tag,
                        )?;
                        Self::implies_equal(
                            // TODO: improve namespace
                            &mut cs.namespace(|| {
                                format!(
                                    "hash_is_equal_{:?}_{:?}",
                                    alloc_tag.get_value(),
                                    tgt.name()
                                )
                            }),
                            &not_dummy,
                            alloc_tgt.hash(),
                            &zero,
                        )?;
                    } else {
                        enforce_equal(
                            cs,
                            || format!("{}'s tag is {}", tgt.name(), tag.field::<F>().hex_digits()),
                            &alloc_tgt.tag(),
                            &alloc_tag,
                        );
                        enforce_equal(
                            cs,
                            || format!("{}'s val is zero", tgt.name()),
                            &alloc_tgt.hash(),
                            &zero,
                        );
                    }
                }
                // LEMOP::Copy(tgt, src) => { Copy might just disappear!!
                //     let Some(alloc_src) = alloc_ptrs.get(src.name()) else {
                //         return Err(format!("{} not allocated", src.name()));
                //     };
                //     if alloc_ptrs.contains_key(tgt.name()) {
                //         return Err(format!("{} already allocated", tgt.name()));
                //     }
                //     let alloc_tgt =
                //         Self::allocate_ptr_from_witness(cs, tgt.name(), store, &ptrs_witness)?;
                //     let alloc_src = alloc_src.clone();
                //     alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                //     Self::enforce_equal_ptrs(cs, &alloc_src, src.name(), &alloc_tgt, tgt.name());
                // }
                LEMOP::MatchTag(match_ptr, cases, def) => {
                    let Some(alloc_match_ptr) = alloc_ptrs.get(match_ptr.name()) else {
                        return Err(format!("{} not allocated", match_ptr.name()));
                    };
                    let Some(tag_f) = alloc_match_ptr.tag().get_value() else {
                        return Err(format!("Couldn't get tag for allocated pointer {}", match_ptr.name()));
                    };
                    let mut has_match = false;
                    let mut not_dummy_vec = Vec::new();
                    for (i, (tag, op)) in cases.iter().enumerate() {
                        dbg!(i);
                        dbg!(tag.field::<F>());
                        //dbg!(op);

                        let Ok(alloc_has_match) = alloc_equal_const(
                            // TODO: improve namespace
                            &mut cs.namespace(|| format!("alloc_has_match_{:?}_{:?}", tag.field::<F>(), alloc_match_ptr.tag().get_value())),
                            alloc_match_ptr.tag(),
                            tag.field::<F>(),
                        ) else {
                            return Err("TODO".to_string());
                        };
                        not_dummy_vec.push(alloc_has_match.clone());

                        if tag.field::<F>() == tag_f {
                            has_match = true;
                        } else {
                            let (ptrs, vars) = op.potential_assignments();
                            for ptr in ptrs.iter() {
                                ptrs_witness.insert(ptr.name(), Ptr::null(Tag::Dummy));
                            }
                            for var in vars.iter() {
                                vars_witness.insert(var.name(), F::zero());
                            }
                        }
                        stack.push((op, Some(alloc_has_match)));
                    }
                    if has_match {
                        let (ptrs, vars) = def.potential_assignments();
                        for ptr in ptrs.iter() {
                            ptrs_witness.insert(ptr.name(), Ptr::null(Tag::Dummy));
                        }
                        for var in vars.iter() {
                            vars_witness.insert(var.name(), F::zero());
                        }
                    }
                    let Ok(is_default) = all_booleans_are_false(
                        // TODO: improve namespace
                        &mut cs.namespace(|| format!("is_default_{:?}", alloc_match_ptr.tag().get_value())),
                        &not_dummy_vec.iter().collect::<Vec<_>>(),
                    ) else {
                        return Err("TODO".to_string());
                    }; // see or_v_unchecked_for_optimization

                    stack.push((def, Some(is_default.clone())));

                    not_dummy_vec.push(is_default);

                    let Ok(_) = popcount(
                        // TODO: improve namespace
                        &mut cs.namespace(|| format!("popcount_{:?}", alloc_match_ptr.tag().get_value())),
                        &not_dummy_vec[..],
                        &one,
                    ) else {
                        return Err("TODO".to_string())
                    };
                }
                LEMOP::Seq(ops) => stack.extend(ops.iter().rev().map(|op| (op, not_dummy.clone()))),
                LEMOP::SetReturn(outputs) => {
                    // TODO: implement
                }
                _ => todo!(),
            }
        }
        Ok(())
    }
}
