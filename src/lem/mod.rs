mod constrainer;
mod eval;
mod interpreter;
mod lurk_symbol;
mod pointers;
mod store;
mod symbol;
mod tag;

use std::collections::HashMap;

use crate::field::LurkField;

use self::{lurk_symbol::LurkSymbol, pointers::Ptr, tag::Tag};

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
                for (tag, case) in cases {
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
                for op in ops {
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
#[allow(dead_code)]
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
}

mod shortcuts {
    use super::*;

    #[allow(dead_code)]
    #[inline]
    pub(crate) fn mptr(name: &str) -> MetaPtr {
        MetaPtr(name.to_string())
    }

    #[allow(dead_code)]
    #[inline]
    pub(crate) fn mvar(name: &str) -> MetaVar {
        MetaVar(name.to_string())
    }

    #[allow(dead_code)]
    #[inline]
    pub(crate) fn match_tag<F: LurkField>(i: MetaPtr, cases: Vec<(Tag, LEMOP<F>)>) -> LEMOP<F> {
        LEMOP::MatchTag(i, HashMap::from_iter(cases))
    }
}

#[cfg(test)]
mod tests {
    use super::{store::Store, *};
    use crate::lem::{pointers::Ptr, tag::Tag};
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;
    use shortcuts::*;

    fn constrain_test_helper(lem: &LEM<Fr>, store: &mut Store<Fr>, witnesses: &Vec<Witness<Fr>>) {
        for w in witnesses {
            let mut cs = TestConstraintSystem::<Fr>::new();
            lem.constrain(&mut cs, store, w).unwrap();
            assert!(cs.is_satisfied());
        }
    }

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
        let mut store = Store::default();
        let witnesses = lem.eval(expr, &mut store).unwrap();
        constrain_test_helper(&lem, &mut store, &witnesses);
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
        let mut store = Store::default();
        let witnesses = lem.eval(expr, &mut store).unwrap();
        constrain_test_helper(&lem, &mut store, &witnesses);
    }
}
