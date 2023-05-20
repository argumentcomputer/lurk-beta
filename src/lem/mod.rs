mod eval;
mod lurk_symbol;
mod pointers;
mod store;
mod symbol;
mod tag;

use std::collections::HashMap;

use crate::{
    circuit::gadgets::{
        constraints::{and, implies_equal},
        pointer::AllocatedPtr,
    },
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
    alloc_equal_const, enforce_selector_with_premise, popcount,
};
use bellperson::gadgets::boolean::Boolean;
use bellperson::gadgets::num::AllocatedNum;
use bellperson::ConstraintSystem;
use dashmap::DashMap;

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
pub struct LEM<F: LurkField> {
    input: [String; 3],
    lem_op: LEMOP<F>,
}

#[derive(PartialEq, Clone, Eq, Hash)]
pub struct MetaPtr(String);

impl MetaPtr {
    #[inline]
    pub fn name(&self) -> &String {
        &self.0
    }

    pub fn get_ptr<F: LurkField>(&self, ptrs: &HashMap<String, Ptr<F>>) -> Result<Ptr<F>, String> {
        match ptrs.get(&self.0) {
            Some(ptr) => Ok(*ptr),
            None => Err(format!("Meta pointer {} not defined", self.0)),
        }
    }
}

#[derive(PartialEq, Clone, Eq, Hash)]
pub struct MetaVar(String);

impl MetaVar {
    #[inline]
    pub fn name(&self) -> &String {
        &self.0
    }
}

#[derive(Clone)]
pub enum LEMOP<F: LurkField> {
    MkNull(MetaPtr, Tag),
    Hash2Ptrs(MetaPtr, Tag, [MetaPtr; 2]),
    Hash3Ptrs(MetaPtr, Tag, [MetaPtr; 3]),
    Hash4Ptrs(MetaPtr, Tag, [MetaPtr; 4]),
    Unhash2Ptrs([MetaPtr; 2], MetaPtr),
    Unhash3Ptrs([MetaPtr; 3], MetaPtr),
    Unhash4Ptrs([MetaPtr; 4], MetaPtr),
    Hide(MetaPtr, F, MetaPtr),
    Open(MetaVar, MetaPtr, F), // secret, tgt, src hash
    MatchTag(MetaPtr, HashMap<Tag, LEMOP<F>>),
    MatchLurkSymbolVal(MetaPtr, HashMap<LurkSymbol, LEMOP<F>>),
    Seq(Vec<LEMOP<F>>),
    SetReturn([MetaPtr; 3]),
}

impl<F: LurkField> LEMOP<F> {
    pub fn check(&self) -> Result<(), String> {
        // TODO
        Ok(())
    }

    pub fn deconflict(
        &self,
        path: String,
        dmap: &DashMap<String, String, ahash::RandomState>, // name -> path/name
    ) -> Result<Self, String> {
        match self {
            Self::MkNull(ptr, tag) => {
                let new_name = format!("{}.{}", path, ptr.name());
                if dmap.insert(ptr.name().clone(), new_name.clone()).is_some() {
                    return Err(format!("{} already defined", ptr.name()));
                };
                Ok(Self::MkNull(MetaPtr(new_name), *tag))
            }
            Self::Hash2Ptrs(tgt, tag, src) => {
                let Some(src0_path) = dmap.get(src[0].name()) else {
                    return Err(format!("{} not defined", src[0].name()));
                };
                let Some(src1_path) = dmap.get(src[1].name()) else {
                    return Err(format!("{} not defined", src[1].name()));
                };
                let new_name = format!("{}/{}", path, tgt.name());
                if dmap.insert(tgt.name().clone(), new_name.clone()).is_some() {
                    return Err(format!("{} already defined", tgt.name()));
                };
                Ok(Self::Hash2Ptrs(
                    MetaPtr(new_name),
                    *tag,
                    [MetaPtr(src0_path.clone()), MetaPtr(src1_path.clone())],
                ))
            }
            Self::Hash3Ptrs(tgt, tag, src) => {
                let Some(src0_path) = dmap.get(src[0].name()) else {
                    return Err(format!("{} not defined", src[0].name()));
                };
                let Some(src1_path) = dmap.get(src[1].name()) else {
                    return Err(format!("{} not defined", src[1].name()));
                };
                let Some(src2_path) = dmap.get(src[2].name()) else {
                    return Err(format!("{} not defined", src[2].name()));
                };
                let new_name = format!("{}/{}", path, tgt.name());
                if dmap.insert(tgt.name().clone(), new_name.clone()).is_some() {
                    return Err(format!("{} already defined", tgt.name()));
                };
                Ok(Self::Hash3Ptrs(
                    MetaPtr(new_name),
                    *tag,
                    [
                        MetaPtr(src0_path.clone()),
                        MetaPtr(src1_path.clone()),
                        MetaPtr(src2_path.clone()),
                    ],
                ))
            }
            Self::Hash4Ptrs(tgt, tag, src) => {
                let Some(src0_path) = dmap.get(src[0].name()) else {
                    return Err(format!("{} not defined", src[0].name()));
                };
                let Some(src1_path) = dmap.get(src[1].name()) else {
                    return Err(format!("{} not defined", src[1].name()));
                };
                let Some(src2_path) = dmap.get(src[2].name()) else {
                    return Err(format!("{} not defined", src[2].name()));
                };
                let Some(src3_path) = dmap.get(src[3].name()) else {
                    return Err(format!("{} not defined", src[3].name()));
                };
                let new_name = format!("{}/{}", path, tgt.name());
                if dmap.insert(tgt.name().clone(), new_name.clone()).is_some() {
                    return Err(format!("{} already defined", tgt.name()));
                };
                Ok(Self::Hash4Ptrs(
                    MetaPtr(new_name),
                    *tag,
                    [
                        MetaPtr(src0_path.clone()),
                        MetaPtr(src1_path.clone()),
                        MetaPtr(src2_path.clone()),
                        MetaPtr(src3_path.clone()),
                    ],
                ))
            }
            LEMOP::MatchTag(ptr, cases) => {
                let Some(ptr_path) = dmap.get(ptr.name()) else {
                    return Err(format!("{} not defined", ptr.name()));
                };
                let mut new_cases = vec![];
                for (tag, case) in cases.iter() {
                    // each case needs it's own clone of `dmap`
                    let new_case = case.deconflict(format!("{}.{}", &path, &tag), &dmap.clone())?;
                    new_cases.push((*tag, new_case));
                }
                Ok(LEMOP::MatchTag(
                    MetaPtr(ptr_path.clone()),
                    HashMap::from_iter(new_cases),
                ))
            }
            LEMOP::Seq(ops) => {
                let mut new_ops = vec![];
                for op in ops.iter() {
                    new_ops.push(op.deconflict(path.clone(), dmap)?);
                }
                Ok(LEMOP::Seq(new_ops))
            }
            LEMOP::SetReturn(o) => {
                let Some(o0) = dmap.get(o[0].name()) else {
                    return Err(format!("{} not defined", o[0].name()));
                };
                let Some(o1) = dmap.get(o[1].name()) else {
                    return Err(format!("{} not defined", o[1].name()));
                };
                let Some(o2) = dmap.get(o[2].name()) else {
                    return Err(format!("{} not defined", o[2].name()));
                };
                Ok(LEMOP::SetReturn([
                    MetaPtr(o0.clone()),
                    MetaPtr(o1.clone()),
                    MetaPtr(o2.clone()),
                ]))
            }
            _ => todo!(),
        }
    }
}

#[derive(Clone)]
pub struct Witness<F: LurkField> {
    input: [Ptr<F>; 3],
    output: [Ptr<F>; 3],
    ptrs: HashMap<String, Ptr<F>>,
    vars: HashMap<String, F>,
}

impl<F: LurkField> LEM<F> {
    pub fn new(input: [&str; 3], lem_op: LEMOP<F>) -> Result<LEM<F>, String> {
        lem_op.check()?;
        let dmap = DashMap::from_iter(input.map(|i| (i.to_string(), i.to_string())));
        Ok(LEM {
            input: input.map(|i| i.to_string()),
            lem_op: lem_op.deconflict(String::new(), &dmap)?,
        })
    }

    pub fn run(&self, input: [Ptr<F>; 3], store: &mut Store<F>) -> Result<Witness<F>, String> {
        // key/val pairs on these maps should never be overwritten
        let mut ptrs = HashMap::default();
        let mut vars = HashMap::default();
        ptrs.insert(self.input[0].clone(), input[0]);
        if ptrs.insert(self.input[1].clone(), input[1]).is_some() {
            return Err(format!("{} already defined", self.input[1]));
        }
        if ptrs.insert(self.input[2].clone(), input[2]).is_some() {
            return Err(format!("{} already defined", self.input[2]));
        }
        let mut output = None;
        let mut stack = vec![&self.lem_op];
        while let Some(op) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    let tgt_ptr = Ptr::null(*tag);
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash2Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?;
                    let src_ptr2 = src[1].get_ptr(&ptrs)?;
                    let tgt_ptr = store.index_2_ptrs(*tag, src_ptr1, src_ptr2);
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash3Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?;
                    let src_ptr2 = src[1].get_ptr(&ptrs)?;
                    let src_ptr3 = src[2].get_ptr(&ptrs)?;
                    let tgt_ptr = store.index_3_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3);
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Hash4Ptrs(tgt, tag, src) => {
                    let src_ptr1 = src[0].get_ptr(&ptrs)?;
                    let src_ptr2 = src[1].get_ptr(&ptrs)?;
                    let src_ptr3 = src[2].get_ptr(&ptrs)?;
                    let src_ptr4 = src[3].get_ptr(&ptrs)?;
                    let tgt_ptr = store.index_4_ptrs(*tag, src_ptr1, src_ptr2, src_ptr3, src_ptr4);
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Unhash2Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index2() else {
                        return Err(format!(
                            "{} isn't a Tree2 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptrs.insert(tgts[0].name().clone(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptrs.insert(tgts[1].name().clone(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                }
                LEMOP::Unhash3Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index3() else {
                        return Err(format!(
                            "{} isn't a Tree3 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptrs.insert(tgts[0].name().clone(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptrs.insert(tgts[1].name().clone(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                    if ptrs.insert(tgts[2].name().clone(), *c).is_some() {
                        return Err(format!("{} already defined", tgts[2].name()));
                    }
                }
                LEMOP::Unhash4Ptrs(tgts, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let Some(idx) = src_ptr.get_index4() else {
                        return Err(format!(
                            "{} isn't a Tree4 pointer",
                            src.name()
                        ));
                    };
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                        return Err(format!("Couldn't fetch {}'s children", src.name()))
                    };
                    if ptrs.insert(tgts[0].name().clone(), *a).is_some() {
                        return Err(format!("{} already defined", tgts[0].name()));
                    }
                    if ptrs.insert(tgts[1].name().clone(), *b).is_some() {
                        return Err(format!("{} already defined", tgts[1].name()));
                    }
                    if ptrs.insert(tgts[2].name().clone(), *c).is_some() {
                        return Err(format!("{} already defined", tgts[2].name()));
                    }
                    if ptrs.insert(tgts[3].name().clone(), *d).is_some() {
                        return Err(format!("{} already defined", tgts[3].name()));
                    }
                }
                LEMOP::Hide(tgt, secret, src) => {
                    let src_ptr = src.get_ptr(&ptrs)?;
                    let aqua_ptr = store.hydrate_ptr(&src_ptr)?;
                    let hash =
                        store
                            .poseidon_cache
                            .hash3(&[*secret, aqua_ptr.tag.field(), aqua_ptr.val]);
                    let tgt_ptr = Ptr::comm(hash);
                    store.comms.insert(FWrap::<F>(hash), (*secret, src_ptr));
                    if ptrs.insert(tgt.name().clone(), tgt_ptr).is_some() {
                        return Err(format!("{} already defined", tgt.name()));
                    }
                }
                LEMOP::Open(tgt_secret, tgt_ptr, hash) => {
                    let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                        return Err(format!("No committed data for hash {}", hash.hex_digits()))
                    };
                    if ptrs.insert(tgt_ptr.name().clone(), *ptr).is_some() {
                        return Err(format!("{} already defined", tgt_ptr.name()));
                    }
                    if vars.insert(tgt_secret.name().clone(), *secret).is_some() {
                        return Err(format!("{} already defined", tgt_secret.name()));
                    }
                }
                LEMOP::MatchTag(ptr, cases) => {
                    let ptr = ptr.get_ptr(&ptrs)?;
                    let ptr_tag = ptr.tag();
                    match cases.get(ptr_tag) {
                        Some(op) => stack.push(op),
                        None => return Err(format!("No match for tag {:?}", ptr_tag)),
                    }
                }
                LEMOP::MatchLurkSymbolVal(ptr, cases) => {
                    let Ptr::Leaf(Tag::LurkSym, f) = ptr.get_ptr(&ptrs)? else {
                        return Err(format!("{} not defined as a pointer to a Lurk symbol", ptr.name()))
                    };
                    let Some(lurk_symbol) = LurkSymbol::from_field(&f) else {
                        return Err(format!("{} contains invalid value for a Lurk symbol", ptr.name()))
                    };
                    match cases.get(&lurk_symbol) {
                        Some(op) => stack.push(op),
                        None => {
                            return Err(format!("No match for field element {}", f.hex_digits()))
                        }
                    }
                }
                LEMOP::Seq(ops) => stack.extend(ops.iter().rev()),
                LEMOP::SetReturn(o) => {
                    output = Some([
                        o[0].get_ptr(&ptrs)?,
                        o[1].get_ptr(&ptrs)?,
                        o[2].get_ptr(&ptrs)?,
                    ]);
                }
            }
        }
        let Some(output) = output else {
            return Err("Output not defined".to_string());
        };
        Ok(Witness {
            input,
            output,
            ptrs,
            vars,
        })
    }

    pub fn eval(&self, expr: Ptr<F>) -> Result<(Vec<Witness<F>>, Store<F>), String> {
        let mut expr = expr;
        let mut env = Ptr::lurk_sym(&LurkSymbol::Nil);
        let mut cont = Ptr::null(Tag::Outermost);
        let mut witnesses = vec![];
        let mut store: Store<F> = Default::default();
        let terminal = Ptr::null(Tag::Terminal);
        loop {
            let w = self.run([expr, env, cont], &mut store)?;
            witnesses.push(w.clone());
            if w.output[2] == terminal {
                break;
            } else {
                [expr, env, cont] = w.output;
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

    fn allocate_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        aqua_ptr: &AquaPtr<F>,
        name: &String,
    ) -> Result<AllocatedPtr<F>, String> {
        let Ok(alloc_tag) = AllocatedNum::alloc(cs.namespace(|| format!("allocate {}'s tag", name)), || {
            Ok(aqua_ptr.tag.field())
        }) else {
            return Err(format!("Couldn't allocate tag for {}", name))
        };
        let Ok(alloc_val) = AllocatedNum::alloc(cs.namespace(|| format!("allocate {}'s val", name)), || {
            Ok(aqua_ptr.val)
        }) else {
            return Err(format!("Couldn't allocate val for {}", name))
        };
        Ok(AllocatedPtr::from_parts(&alloc_tag, &alloc_val))
    }

    fn allocate_input_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        aqua_ptr: &AquaPtr<F>,
        name: &String,
    ) -> Result<AllocatedPtr<F>, String> {
        let alloc_ptr = Self::allocate_ptr(
            &mut cs.namespace(|| format!("allocate pointer {}", name)),
            aqua_ptr,
            name,
        )?;
        let Ok(_) = alloc_ptr.tag().inputize(cs.namespace(|| format!("inputize {}'s tag", name))) else {
            return Err(format!("Couldn't inputize tag for {}", name))
        };
        let Ok(_) = alloc_ptr.hash().inputize(cs.namespace(|| format!("inputize {}'s val", name))) else {
            return Err(format!("Couldn't inputize val for {}", name))
        };
        Ok(alloc_ptr)
    }

    fn on_concrete_path(concrete_path: &Option<Boolean>) -> Result<bool, String> {
        match concrete_path {
            None => Ok(true),
            Some(concrete_path) => match concrete_path.get_value() {
                Some(b) => Ok(b),
                None => Err("Couldn't check whether we're on a concrete path".to_string()),
            },
        }
    }

    /// TODO: improve
    /// Create R1CS constraints for LEM.
    /// As we find new operations, we stack them to be constrained later.
    /// We use hash maps we manage viariables and pointers.
    /// This way we can reference allocated variables that were
    /// created previously.
    /// We have real paths and virtual paths.
    /// Then we can constrain LEM using implications.
    pub fn constrain<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &mut Store<F>,
        witness: &Witness<F>,
    ) -> Result<(), String> {
        let mut alloc_ptrs: HashMap<&String, AllocatedPtr<F>> = HashMap::default();

        // TODO: consider creating `initialize` function
        // allocate first input
        {
            let Some(ptr) = witness.ptrs.get(&self.input[0]) else {
                return Err("Could not find first input".to_string())
            };
            alloc_ptrs.insert(
                &self.input[0],
                Self::allocate_input_ptr(
                    &mut cs.namespace(|| format!("allocate input {}", self.input[0])),
                    &store.hydrate_ptr(ptr)?,
                    &self.input[0],
                )?,
            );
        }

        // allocate second input
        {
            if alloc_ptrs.contains_key(&self.input[1]) {
                return Err(format!("{} already allocated", self.input[1]));
            }
            let Some(ptr) = witness.ptrs.get(&self.input[1]) else {
                return Err("Could not find second input".to_string())
            };
            alloc_ptrs.insert(
                &self.input[1],
                Self::allocate_input_ptr(
                    &mut cs.namespace(|| format!("allocate input {}", self.input[1])),
                    &store.hydrate_ptr(ptr)?,
                    &self.input[1],
                )?,
            );
        }

        // allocate third input
        {
            if alloc_ptrs.contains_key(&self.input[2]) {
                return Err(format!("{} already allocated", self.input[2]));
            }
            let Some(ptr) = witness.ptrs.get(&self.input[2]) else {
                return Err("Could not find third input".to_string())
            };
            alloc_ptrs.insert(
                &self.input[2],
                Self::allocate_input_ptr(
                    &mut cs.namespace(|| format!("allocate input {}", self.input[2])),
                    &store.hydrate_ptr(ptr)?,
                    &self.input[2],
                )?,
            );
        }

        // TODO: consider greating globals
        let zero = AllocatedNum::alloc(cs.namespace(|| "#zero"), || Ok(F::zero())).unwrap();
        let one = AllocatedNum::alloc(cs.namespace(|| "#one"), || Ok(F::one())).unwrap();
        let mut alloc_tags: HashMap<&Tag, AllocatedNum<F>> = HashMap::default();
        let mut stack = vec![(&self.lem_op, None::<Boolean>, String::new())];
        while let Some((op, concrete_path, path)) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    if alloc_ptrs.contains_key(tgt.name()) {
                        return Err(format!("{} already allocated", tgt.name()));
                    };
                    let aqua_ptr = {
                        if Self::on_concrete_path(&concrete_path)? {
                            let Some(ptr) = witness.ptrs.get(tgt.name()) else {
                                return Err(format!("Couldn't retrieve witness {}", tgt.name()));
                            };
                            store.hydrate_ptr(ptr)?
                        } else {
                            AquaPtr::dummy()
                        }
                    };
                    let alloc_tgt = Self::allocate_ptr(
                        &mut cs.namespace(|| format!("allocate pointer {}", tgt.name())),
                        &aqua_ptr,
                        tgt.name(),
                    )?;
                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                    let alloc_tag = {
                        match alloc_tags.get(tag) {
                            Some(alloc_tag) => alloc_tag.clone(),
                            None => {
                                let Ok(alloc_tag) = AllocatedNum::alloc(
                                    cs.namespace(|| format!("Tag {:?}", tag)),
                                    || Ok(tag.field()),
                                ) else {
                                    return Err(format!("Couldn't allocate tag for {}", tgt.name()));
                                };
                                alloc_tags.insert(tag, alloc_tag.clone());
                                alloc_tag
                            }
                        }
                    };

                    // If `concrete_path` is Some, then we constrain using "concrete implies ..." logic
                    if let Some(concrete_path) = concrete_path {
                        let Ok(_) = implies_equal(
                            &mut cs.namespace(|| format!("implies equal for {}'s tag", tgt.name())),
                            &concrete_path,
                            alloc_tgt.tag(),
                            &alloc_tag,
                        ) else {
                            return Err("TODO".to_string())
                        };
                        let Ok(_) = implies_equal(
                            &mut cs.namespace(|| format!("implies equal for {}'s val (must be zero)", tgt.name())),
                            &concrete_path,
                            alloc_tgt.hash(),
                            &zero,
                        ) else {
                            return Err("TODO".to_string())
                        };
                    } else {
                        // If `concrete_path` is None, we just do regular constraining
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
                LEMOP::MatchTag(match_ptr, cases) => {
                    let Some(alloc_match_ptr) = alloc_ptrs.get(match_ptr.name()) else {
                        return Err(format!("{} not allocated", match_ptr.name()));
                    };
                    let mut concrete_path_vec = Vec::new();
                    for (tag, op) in cases.iter() {
                        let Ok(alloc_has_match) = alloc_equal_const(
                            &mut cs.namespace(
                                || format!("{}.alloc_equal_const (tag:{})", &path, tag)
                            ),
                            alloc_match_ptr.tag(),
                            tag.field::<F>(),
                        ) else {
                            return Err("Allocated variable does not have the expected tag".to_string());
                        };
                        concrete_path_vec.push(alloc_has_match.clone());

                        let new_path_matchtag = format!("{}.{}", &path, tag);
                        if let Some(concrete_path) = concrete_path.clone() {
                            let Ok(concrete_path_and_has_match) = and
                                (
                                    &mut cs.namespace(|| format!("{}.and (tag:{})", &path, tag)),
                                    &concrete_path,
                                    &alloc_has_match
                                ) else {
                                    return Err("Failed to constrain `and`".to_string());
                                };
                            stack.push((op, Some(concrete_path_and_has_match), new_path_matchtag));
                        } else {
                            stack.push((op, Some(alloc_has_match), new_path_matchtag));
                        }
                    }

                    // If `concrete_path` is Some, then we constrain using "concrete implies ..." logic
                    if let Some(concrete_path) = concrete_path {
                        let Ok(_) = enforce_selector_with_premise(
                            &mut cs.namespace(|| {
                                format!(
                                    "{}.enforce exactly one selected (if concrete, tag: {:?})",
                                    &path,
                                    alloc_match_ptr.tag().get_value()
                                )
                            }),
                            &concrete_path,
                            &concrete_path_vec,
                        ) else {
                            return Err("Failed to enforce selector if concrete".to_string());
                        };
                    } else {
                        // If `concrete_path` is None, we just do regular constraining
                        let Ok(_) = popcount(
                            &mut cs.namespace(|| format!("{}.enforce exactly one selected", &path)),
                            &concrete_path_vec[..],
                            &one,
                        ) else {
                            return Err("Failed to enforce selector".to_string())
                        };
                    }
                }
                LEMOP::Seq(ops) => stack.extend(
                    ops.iter()
                        .rev()
                        .map(|op| (op, concrete_path.clone(), path.clone())),
                ),
                LEMOP::SetReturn(outputs) => {
                    let is_concrete_path = Self::on_concrete_path(&concrete_path)?; 
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(alloc_ptr_computed) = alloc_ptrs.get(output.name()) else {
                            return Err(format!("Output {} not allocated", output.name()))
                        };
                        let aqua_ptr = {
                            if is_concrete_path {
                                let Some(ptr) = witness.ptrs.get(output.name()) else {
                                    return Err(format!("Output {} not found in the witness", output.name()))
                                };
                                store.hydrate_ptr(ptr)?
                            } else {
                                AquaPtr::dummy()
                            }
                        };
                        let output_name = format!("{}.output[{}]", &path, i);
                        let alloc_ptr_expected = Self::allocate_input_ptr(
                            &mut cs.namespace(|| format!("allocate input for {}", &output_name)),
                            &aqua_ptr,
                            &output_name,
                        )?;

                        // If `concrete_path` is Some, then we constrain using "concrete implies ..." logic
                        if let Some(concrete_path) = concrete_path.clone() {
                            let Ok(_) = alloc_ptr_computed.implies_ptr_equal(
                                &mut cs.namespace(|| format!("enforce imply equal for {}", output_name)),
                                &concrete_path,
                                &alloc_ptr_expected,
                            ) else {
                                return Err("Failed to constrain implies_ptr_equal".to_string())
                            };
                        } else {
                            // If `concrete_path` is None, we just do regular constraining
                            alloc_ptr_computed.enforce_equal(
                                &mut cs.namespace(|| format!("enforce equal for {}", output_name)),
                                &alloc_ptr_expected,
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

mod shortcuts {
    use super::*;

    #[inline]
    pub fn mptr(name: &str) -> MetaPtr {
        MetaPtr(name.to_string())
    }

    #[inline]
    pub fn mvar(name: &str) -> MetaVar {
        MetaVar(name.to_string())
    }

    #[inline]
    pub fn match_tag<F: LurkField>(i: MetaPtr, cases: Vec<(Tag, LEMOP<F>)>) -> LEMOP<F> {
        LEMOP::MatchTag(i, HashMap::from_iter(cases))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lem::{pointers::Ptr, tag::Tag};
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;
    use shortcuts::*;

    #[test]
    fn accepts_virtual_nested_match_tag() {
        let input = ["expr_in", "env_in", "cont_in"];
        let lem_op = match_tag(
            mptr("expr_in"),
            vec![
                (
                    Tag::Num,
                    LEMOP::Seq(vec![
                        LEMOP::MkNull(mptr("cont_out_terminal"), Tag::Terminal),
                        LEMOP::SetReturn([
                            mptr("expr_in"),
                            mptr("env_in"),
                            mptr("cont_out_terminal"),
                        ]),
                    ]),
                ),
                (
                    Tag::Char,
                    match_tag(
                        // This nested match excercises the need to pass on the information
                        // that we are on a virtual branch, because a constrain will
                        // be created for `cont_out_error` and it will need to be relaxed
                        // by an implication with a false premise
                        mptr("expr_in"),
                        vec![(
                            Tag::Num,
                            LEMOP::Seq(vec![
                                LEMOP::MkNull(mptr("cont_out_error"), Tag::Error),
                                LEMOP::SetReturn([
                                    mptr("expr_in"),
                                    mptr("env_in"),
                                    mptr("cont_out_error"),
                                ]),
                            ]),
                        )],
                    ),
                ),
                (
                    Tag::Sym,
                    match_tag(
                        // This nested match exercises the need to relax `popcount`
                        // because there is no match but it's on a virtual path, so
                        // we don't want to be too restrictive
                        mptr("expr_in"),
                        vec![(
                            Tag::Char,
                            LEMOP::SetReturn([mptr("expr_in"), mptr("env_in"), mptr("cont_in")]),
                        )],
                    ),
                ),
            ],
        );
        let lem = LEM::new(input, lem_op).unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let (res, mut store) = lem.eval(expr).unwrap();
        for w in res.iter() {
            let mut cs = TestConstraintSystem::<Fr>::new();
            lem.constrain(&mut cs, &mut store, w).unwrap();
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn resolves_conflicts_of_clashing_names_in_parallel_branches() {
        let input = ["expr_in", "env_in", "cont_in"];
        let lem_op = match_tag(
            // This match is creating `cont_out_terminal` on two different branches,
            // which, in theory, would cause troubles at allocation time. But we're
            // dealing with that automatically
            mptr("expr_in"),
            vec![
                (
                    Tag::Num,
                    LEMOP::Seq(vec![
                        LEMOP::MkNull(mptr("cont_out_terminal"), Tag::Terminal),
                        LEMOP::SetReturn([
                            mptr("expr_in"),
                            mptr("env_in"),
                            mptr("cont_out_terminal"),
                        ]),
                    ]),
                ),
                (
                    Tag::Char,
                    LEMOP::Seq(vec![
                        LEMOP::MkNull(mptr("cont_out_terminal"), Tag::Terminal),
                        LEMOP::SetReturn([
                            mptr("expr_in"),
                            mptr("env_in"),
                            mptr("cont_out_terminal"),
                        ]),
                    ]),
                ),
            ],
        );
        let lem = LEM::new(input, lem_op).unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let (res, mut store) = lem.eval(expr).unwrap();
        for w in res.iter() {
            let mut cs = TestConstraintSystem::<Fr>::new();
            lem.constrain(&mut cs, &mut store, w).unwrap();
            assert!(cs.is_satisfied());
        }
    }
}
