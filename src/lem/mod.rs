mod constrainer;
mod eval;
mod interpreter;
mod macros;
mod pointers;
mod store;
mod symbol;
mod tag;

use crate::field::LurkField;
use anyhow::{anyhow, bail, Result};
use std::collections::HashMap;

use self::{pointers::Ptr, store::Store, tag::Tag};

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
/// LEM also allows the `Store` API to be completely abstracted away from the
/// responsibilities of LEM authors. Indeed, we want the implementation details
/// of the `Store` not to be important at LEM definition time.
///
/// ### Data semantics
///
/// A LEM describes how to handle pointers with "meta pointers", which are
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
/// all relevant data lives on `HashMap`s that are also a product of the
/// interpreted LEM.
///
/// ### Constraining
///
/// This is the process of creating the circuit, which we want to be done
/// automatically for whoever creates a LEM. Each `LEMOP` has to be precisely
/// constrained in such a way that the resulting circuits accepts a witness iff
/// it was generated by a valid interpretation of the LEM at play.
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
/// 3. One return per LEM path: a LEM must always specify an output regardless
/// of the logical path it takes at interpretation time, otherwise there would
/// be a chance of the next step starting with an unknown input. Also, a LEM
/// should not specify more than an output per logical path because it would
/// risk setting conflicting constraints for the output;
///
/// 4. Assign first, use later: this prevents obvious errors such as "x not
/// defined" during interpretation or "x not allocated" during constraining.
pub struct LEM {
    input: [String; 3],
    lem_op: LEMOP,
}

/// Named references to be bound to `Ptr`s.
#[derive(PartialEq, Clone, Eq, Hash)]
pub struct MetaPtr(String);

impl MetaPtr {
    #[inline]
    pub fn name(&self) -> &String {
        &self.0
    }

    pub fn get_ptr<F: LurkField>(&self, ptrs: &HashMap<String, Ptr<F>>) -> Result<Ptr<F>> {
        match ptrs.get(&self.0) {
            Some(ptr) => Ok(*ptr),
            None => Err(anyhow!("Meta pointer {} not defined", self.0)),
        }
    }
}

/// The basic building blocks of LEMs.
#[non_exhaustive]
#[derive(Clone, PartialEq)]
pub enum LEMOP {
    /// `MkNull(x, t)` binds `x` to a `Ptr::Leaf(t, F::zero())`
    Null(MetaPtr, Tag),
    /// `Hash2(x, t, is)` binds `x` to a `Ptr` with tag `t` and 2 children `is`
    Hash2(MetaPtr, Tag, [MetaPtr; 2]),
    /// `Hash3(x, t, is)` binds `x` to a `Ptr` with tag `t` and 3 children `is`
    Hash3(MetaPtr, Tag, [MetaPtr; 3]),
    /// `Hash4(x, t, is)` binds `x` to a `Ptr` with tag `t` and 4 children `is`
    Hash4(MetaPtr, Tag, [MetaPtr; 4]),
    /// `Unhash2([a, b], x)` binds `a` and `b` to the 2 children of `x`
    Unhash2([MetaPtr; 2], MetaPtr),
    /// `Unhash3([a, b, c], x)` binds `a` and `b` to the 3 children of `x`
    Unhash3([MetaPtr; 3], MetaPtr),
    /// `Unhash4([a, b, c, d], x)` binds `a` and `b` to the 4 children of `x`
    Unhash4([MetaPtr; 4], MetaPtr),
    /// `Hide(x, s, p)` binds `x` to a (comm) `Ptr` resulting from hiding the
    /// payload `p` with (num) secret `s`
    Hide(MetaPtr, MetaPtr, MetaPtr),
    /// `Open(s, p, h)` binds `s` and `p` to the secret and payload (respectively)
    /// of the commitment that resulted on (num or comm) `h`
    Open(MetaPtr, MetaPtr, MetaPtr),
    /// `MatchTag(x, cases)` performs a match on the tag of `x`, considering only
    /// the appropriate `LEMOP` among the ones provided in `cases`
    MatchTag(MetaPtr, HashMap<Tag, LEMOP>),
    /// `MatchSymPath(x, cases, def)` checks whether `x` matches some symbol among
    /// the ones provided in `cases`. If so, run the corresponding `LEMOP`. Run
    /// The default `def` `LEMOP` otherwise
    MatchSymPath(MetaPtr, HashMap<Vec<String>, LEMOP>, Box<LEMOP>),
    /// `Seq(ops)` executes each `op: LEMOP` in `ops` sequentially
    Seq(Vec<LEMOP>),
    /// `Return([a, b, c])` sets the output as `[a, b, c]`
    Return([MetaPtr; 3]),
}

impl LEMOP {
    /// Performs the static checks of correctness described in `LEM`.
    ///
    /// Note: this function is not supposed to be called manually. It's used by
    /// `LEM::new`, which is the API that should be used directly.
    pub fn check(&self) -> Result<()> {
        // TODO
        Ok(())
    }

    /// Removes conflicting names in parallel logical LEM paths. While these
    /// conflicting names shouldn't be an issue for interpretation, they are
    /// problematic when we want to generate the constraints for the LEM, since
    /// conflicting names would cause different allocations to be bound the same
    /// name.
    ///
    /// The conflict resolution is achieved by changing meta pointers so that
    /// their names are prepended by the paths where they're declared.
    ///
    /// Note: this function is not supposed to be called manually. It's used by
    /// `LEM::new`, which is the API that should be used directly.
    pub fn deconflict(
        &self,
        path: &str,
        map: &mut HashMap<String, String>, // name -> path/name
    ) -> Result<Self> {
        match self {
            Self::Null(ptr, tag) => {
                let new_name = format!("{}.{}", path, ptr.name());
                if map.insert(ptr.name().clone(), new_name.clone()).is_some() {
                    bail!("{} already defined", ptr.name());
                };
                Ok(Self::Null(MetaPtr(new_name), *tag))
            }
            Self::Hash2(tgt, tag, src) => {
                let Some(src0_path) = map.get(src[0].name()).cloned() else {
                    bail!("{} not defined", src[0].name());
                };
                let Some(src1_path) = map.get(src[1].name()).cloned() else {
                    bail!("{} not defined", src[1].name());
                };
                let new_name = format!("{}.{}", path, tgt.name());
                if map.insert(tgt.name().clone(), new_name.clone()).is_some() {
                    bail!("{} already defined", tgt.name());
                };
                Ok(Self::Hash2(
                    MetaPtr(new_name),
                    *tag,
                    [MetaPtr(src0_path), MetaPtr(src1_path)],
                ))
            }
            Self::Hash3(tgt, tag, src) => {
                let Some(src0_path) = map.get(src[0].name()).cloned() else {
                    bail!("{} not defined", src[0].name());
                };
                let Some(src1_path) = map.get(src[1].name()).cloned() else {
                    bail!("{} not defined", src[1].name());
                };
                let Some(src2_path) = map.get(src[2].name()).cloned() else {
                    bail!("{} not defined", src[2].name());
                };
                let new_name = format!("{}.{}", path, tgt.name());
                if map.insert(tgt.name().clone(), new_name.clone()).is_some() {
                    bail!("{} already defined", tgt.name());
                };
                Ok(Self::Hash3(
                    MetaPtr(new_name),
                    *tag,
                    [MetaPtr(src0_path), MetaPtr(src1_path), MetaPtr(src2_path)],
                ))
            }
            Self::Hash4(tgt, tag, src) => {
                let Some(src0_path) = map.get(src[0].name()).cloned() else {
                    bail!("{} not defined", src[0].name());
                };
                let Some(src1_path) = map.get(src[1].name()).cloned() else {
                    bail!("{} not defined", src[1].name());
                };
                let Some(src2_path) = map.get(src[2].name()).cloned() else {
                    bail!("{} not defined", src[2].name());
                };
                let Some(src3_path) = map.get(src[3].name()).cloned() else {
                    bail!("{} not defined", src[3].name());
                };
                let new_name = format!("{}.{}", path, tgt.name());
                if map.insert(tgt.name().clone(), new_name.clone()).is_some() {
                    bail!("{} already defined", tgt.name());
                };
                Ok(Self::Hash4(
                    MetaPtr(new_name),
                    *tag,
                    [
                        MetaPtr(src0_path),
                        MetaPtr(src1_path),
                        MetaPtr(src2_path),
                        MetaPtr(src3_path),
                    ],
                ))
            }
            LEMOP::Unhash2(tgt, src) => {
                let Some(src_path) = map.get(src.name()).cloned() else {
                    bail!("{} not defined", src.name());
                };
                let tgt0_new_name = format!("{}.{}", path, tgt[0].name());
                if map
                    .insert(tgt[0].name().clone(), tgt0_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[0].name());
                };
                let tgt1_new_name = format!("{}.{}", path, tgt[1].name());
                if map
                    .insert(tgt[1].name().clone(), tgt1_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[1].name());
                };
                Ok(Self::Unhash2(
                    [MetaPtr(tgt0_new_name), MetaPtr(tgt1_new_name)],
                    MetaPtr(src_path),
                ))
            }
            LEMOP::Unhash3(tgt, src) => {
                let Some(src_path) = map.get(src.name()).cloned() else {
                    bail!("{} not defined", src.name());
                };
                let tgt0_new_name = format!("{}.{}", path, tgt[0].name());
                if map
                    .insert(tgt[0].name().clone(), tgt0_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[0].name());
                };
                let tgt1_new_name = format!("{}.{}", path, tgt[1].name());
                if map
                    .insert(tgt[1].name().clone(), tgt1_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[1].name());
                };
                let tgt2_new_name = format!("{}.{}", path, tgt[2].name());
                if map
                    .insert(tgt[2].name().clone(), tgt2_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[2].name());
                };
                Ok(Self::Unhash3(
                    [
                        MetaPtr(tgt0_new_name),
                        MetaPtr(tgt1_new_name),
                        MetaPtr(tgt2_new_name),
                    ],
                    MetaPtr(src_path),
                ))
            }
            LEMOP::Unhash4(tgt, src) => {
                let Some(src_path) = map.get(src.name()).cloned() else {
                    bail!("{} not defined", src.name());
                };
                let tgt0_new_name = format!("{}.{}", path, tgt[0].name());
                if map
                    .insert(tgt[0].name().clone(), tgt0_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[0].name());
                };
                let tgt1_new_name = format!("{}.{}", path, tgt[1].name());
                if map
                    .insert(tgt[1].name().clone(), tgt1_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[1].name());
                };
                let tgt2_new_name = format!("{}.{}", path, tgt[2].name());
                if map
                    .insert(tgt[2].name().clone(), tgt2_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[2].name());
                };
                let tgt3_new_name = format!("{}.{}", path, tgt[3].name());
                if map
                    .insert(tgt[3].name().clone(), tgt3_new_name.clone())
                    .is_some()
                {
                    bail!("{} already defined", tgt[3].name());
                };
                Ok(Self::Unhash4(
                    [
                        MetaPtr(tgt0_new_name),
                        MetaPtr(tgt1_new_name),
                        MetaPtr(tgt2_new_name),
                        MetaPtr(tgt3_new_name),
                    ],
                    MetaPtr(src_path),
                ))
            }
            LEMOP::MatchTag(ptr, cases) => {
                let Some(ptr_path) = map.get(ptr.name()).cloned() else {
                    bail!("{} not defined", ptr.name());
                };
                let mut new_cases = vec![];
                for (tag, case) in cases {
                    // each case needs it's own clone of `map`
                    let new_case = case.deconflict(&format!("{path}.{tag}"), &mut map.clone())?;
                    new_cases.push((*tag, new_case));
                }
                Ok(LEMOP::MatchTag(
                    MetaPtr(ptr_path),
                    HashMap::from_iter(new_cases),
                ))
            }
            LEMOP::MatchSymPath(ptr, cases, def) => {
                let Some(ptr_path) = map.get(ptr.name()).cloned() else {
                    bail!("{} not defined", ptr.name());
                };
                let mut new_cases = vec![];
                for (case_name, case) in cases {
                    // each case needs it's own clone of `map`
                    let new_case = case.deconflict(
                        &format!("{path}.[{}]", case_name.join(".")),
                        &mut map.clone(),
                    )?;
                    new_cases.push((case_name.clone(), new_case));
                }
                Ok(LEMOP::MatchSymPath(
                    MetaPtr(ptr_path),
                    HashMap::from_iter(new_cases),
                    Box::new(def.deconflict(&format!("{path}.DEFAULT"), &mut map.clone())?),
                ))
            }
            LEMOP::Seq(ops) => {
                let mut new_ops = vec![];
                for op in ops {
                    new_ops.push(op.deconflict(path, map)?);
                }
                Ok(LEMOP::Seq(new_ops))
            }
            LEMOP::Return(o) => {
                let Some(o0) = map.get(o[0].name()).cloned() else {
                    bail!("{} not defined", o[0].name());
                };
                let Some(o1) = map.get(o[1].name()).cloned() else {
                    bail!("{} not defined", o[1].name());
                };
                let Some(o2) = map.get(o[2].name()).cloned() else {
                    bail!("{} not defined", o[2].name());
                };
                Ok(LEMOP::Return([MetaPtr(o0), MetaPtr(o1), MetaPtr(o2)]))
            }
            _ => todo!(),
        }
    }

    /// Intern all symbol paths that are matched on `MatchSymPath`s
    pub fn intern_matched_sym_paths<F: LurkField>(&self, store: &mut Store<F>) {
        let mut stack = vec![self];
        while let Some(op) = stack.pop() {
            match op {
                Self::MatchSymPath(_, cases, def) => {
                    for (path, op) in cases {
                        store.intern_symbol_path(path);
                        stack.push(op);
                    }
                    stack.push(def);
                }
                Self::MatchTag(_, cases) => cases.values().for_each(|op| stack.push(op)),
                Self::Seq(ops) => stack.extend(ops),
                // It's safer to be exaustive here and avoid missing new LEMOPs
                Self::Null(..)
                | Self::Hash2(..)
                | Self::Hash3(..)
                | Self::Hash4(..)
                | Self::Unhash2(..)
                | Self::Unhash3(..)
                | Self::Unhash4(..)
                | Self::Hide(..)
                | Self::Open(..)
                | Self::Return(..) => (),
            }
        }
    }
}

/// A `Valuation` carries the data that results from interpreting LEM. That is,
/// it contains all the assignments resulting from running one iteration.
#[derive(Clone)]
pub struct Valuation<F: LurkField> {
    input: [Ptr<F>; 3],
    output: [Ptr<F>; 3],
    ptrs: HashMap<String, Ptr<F>>,
}

impl LEM {
    /// Instantiates a `LEM` with the appropriate checks and transformations
    /// to make sure that interpretation and constraining will be smooth.
    pub fn new(input: [&str; 3], lem_op: &LEMOP) -> Result<LEM> {
        lem_op.check()?;
        let mut map = HashMap::from_iter(input.map(|i| (i.to_string(), i.to_string())));
        Ok(LEM {
            input: input.map(|i| i.to_string()),
            lem_op: lem_op.deconflict("", &mut map)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::constrainer::AllocationManager;
    use super::{store::Store, *};
    use crate::lem::constrainer::SlotsIndices;
    use crate::{lem, lem::pointers::Ptr};
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;

    fn constrain_test_helper(
        lem: &LEM,
        store: &mut Store<Fr>,
        valuations: &Vec<Valuation<Fr>>,
        max_indices: &SlotsIndices,
    ) {
        let mut alloc_manager = AllocationManager::default();
        for v in valuations {
            let mut cs = TestConstraintSystem::<Fr>::new();
            lem.constrain_limited(&mut cs, &mut alloc_manager, store, v, max_indices)
                .unwrap();
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn accepts_virtual_nested_match_tag() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let cont_out_terminal: Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                },
                Char => {
                    match_tag expr_in {
                        // This nested match excercises the need to pass on the
                        // information that we are on a virtual branch, because a
                        // constraint will be created for `cont_out_error` and it
                        // will need to be relaxed by an implication with a false
                        // premise.
                        Num => {
                            let cont_out_error: Error;
                            return (expr_in, env_in, cont_out_error);
                        }
                    };
                },
                Sym => {
                    match_tag expr_in {
                        // This nested match exercises the need to relax `popcount`
                        // because there is no match but it's on a virtual path, so
                        // we don't want to be too restrictive and demand that at
                        // least one path must be taken.
                        Char => {
                            return (expr_in, env_in, cont_in);
                        }
                    };
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        constrain_test_helper(&lem, &mut store, &valuations, &SlotsIndices::default());
    }

    #[test]
    fn resolves_conflicts_of_clashing_names_in_parallel_branches() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                // This match is creating `cont_out_terminal` on two different
                // branches, which, in theory, would cause troubles at allocation
                // time. We solve this problem by calling `LEMOP::deconflict`,
                // which turns one into `Num.cont_out_terminal` and the other into
                // `Char.cont_out_terminal`.
                Num => {
                    let cont_out_terminal: Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                },
                Char => {
                    let cont_out_terminal: Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        constrain_test_helper(&lem, &mut store, &valuations, &SlotsIndices::default());
    }

    #[test]
    fn test_hash2_slots_simple() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_out: Cons = hash2(expr_in, expr_in);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 1,
            hash3_idx: 0,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash2_slots_unhash_simple() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_out: Cons = hash2(expr_in, expr_in);
                    let (expr_car, expr_cdr) = unhash2(expr_out);
                    let cont_out_terminal: Terminal;
                    return (expr_car, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 1,
            hash3_idx: 0,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash2_slots_many() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_aux: Cons = hash2(expr_in, expr_in);
                    let expr_out: Cons = hash2(expr_aux, expr_aux);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                },
                Char => {
                    let expr_aux: Cons = hash2(expr_in, expr_in);
                    let expr_aux2: Cons = hash2(expr_aux, expr_aux);
                    let expr_out: Cons = hash2(expr_aux2, expr_aux2);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 3,
            hash3_idx: 0,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash2_slots_many_nested() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    match_tag cont_in {
                        Cons => {
                            let expr_comm: Cons = hash2(expr_in, expr_in);
                            let expr_comm2: Cons = hash2(expr_comm, expr_comm);
                            let expr_comm3: Cons = hash2(expr_comm, expr_comm2);
                            let expr_comm4: Cons = hash2(expr_comm, expr_comm3);
                            let expr_comm5: Cons = hash2(expr_comm, expr_comm4);
                        },
                        Outermost => {
                            let expr_outer: Cons = hash2(expr_in, expr_in);
                            let expr_outer2: Cons = hash2(expr_outer, expr_outer);
                        }
                    };
                    let expr_aux: Cons = hash2(expr_in, expr_in);
                    let expr_out: Cons = hash2(expr_aux, expr_aux);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                },
                Char => {
                    let expr_aux: Cons = hash2(expr_in, expr_in);
                    let expr_aux2: Cons = hash2(expr_aux, expr_aux);
                    let expr_out: Cons = hash2(expr_aux2, expr_aux2);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 7,
            hash3_idx: 0,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash2_slots_seq() {
        let lem = lem!(expr_in env_in cont_in {
            let expr_aux: Cons = hash2(expr_in, expr_in);
            let expr_out: Cons = hash2(expr_aux, expr_aux);
            let cont_out_terminal: Terminal;
            return (expr_out, env_in, cont_out_terminal);
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 2,
            hash3_idx: 0,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash3_slots_simple() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_out: Cons = hash3(expr_in, expr_in, expr_in);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 1,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash3_slots_unhash_simple() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_out: Cons = hash3(expr_in, expr_in, expr_in);
                    let (expr_input1, expr_input2, expr_input3) = unhash3(expr_out);
                    let cont_out_terminal: Terminal;
                    return (expr_input1, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 1,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash3_slots_many() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_aux: Cons = hash3(expr_in, expr_in, expr_in);
                    let expr_out: Cons = hash3(expr_aux, expr_aux, expr_aux);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                },
                Char => {
                    let expr_aux: Cons = hash3(expr_in, expr_in, expr_in);
                    let expr_aux2: Cons = hash3(expr_aux, expr_aux, expr_aux);
                    let expr_out: Cons = hash3(expr_aux2, expr_aux2, expr_aux2);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 3,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash3_slots_many_nested() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    match_tag cont_in {
                        Cons => {
                            let expr_comm: Cons = hash3(expr_in, expr_in, expr_in);
                            let expr_comm2: Cons = hash3(expr_comm, expr_comm, expr_comm);
                            let expr_comm3: Cons = hash3(expr_comm, expr_comm2, expr_comm2);
                            let expr_comm4: Cons = hash3(expr_comm, expr_comm3, expr_comm3);
                            let expr_comm5: Cons = hash3(expr_comm, expr_comm4, expr_comm4);
                        },
                        Outermost => {
                            let expr_outer: Cons = hash3(expr_in, expr_in, expr_in);
                            let expr_outer2: Cons = hash3(expr_outer, expr_outer, expr_outer);
                        }
                    };
                    let expr_aux: Cons = hash3(expr_in, expr_in, expr_in);
                    let expr_out: Cons = hash3(expr_aux, expr_aux, expr_aux);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                },
                Char => {
                    let expr_aux: Cons = hash3(expr_in, expr_in, expr_in);
                    let expr_aux2: Cons = hash3(expr_aux, expr_aux, expr_aux);
                    let expr_out: Cons = hash3(expr_aux2, expr_aux2, expr_aux2);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 7,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash3_slots_seq() {
        let lem = lem!(expr_in env_in cont_in {
            let expr_aux: Cons = hash3(expr_in, expr_in, expr_in);
            let expr_out: Cons = hash3(expr_aux, expr_aux, expr_aux);
            let cont_out_terminal: Terminal;
            return (expr_out, env_in, cont_out_terminal);
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 2,
            hash4_idx: 0,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash4_slots_simple() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_out: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 0,
            hash4_idx: 1,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash4_slots_unhash_simple() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_out: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
                    let (expr_input1, expr_input2, expr_input3, expr_input4) = unhash4(expr_out);
                    let cont_out_terminal: Terminal;
                    return (expr_input1, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 0,
            hash4_idx: 1,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash4_slots_many() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    let expr_aux: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
                    let expr_out: Cons = hash4(expr_aux, expr_aux, expr_aux, expr_aux);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                },
                Char => {
                    let expr_aux: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
                    let expr_aux2: Cons = hash4(expr_aux, expr_aux, expr_aux, expr_aux);
                    let expr_out: Cons = hash4(expr_aux2, expr_aux2, expr_aux2, expr_aux2);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 0,
            hash4_idx: 3,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash4_slots_many_nested() {
        let lem = lem!(expr_in env_in cont_in {
            match_tag expr_in {
                Num => {
                    match_tag cont_in {
                        Cons => {
                            let expr_comm: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
                            let expr_comm2: Cons = hash4(expr_comm, expr_comm, expr_comm, expr_comm);
                            let expr_comm3: Cons = hash4(expr_comm, expr_comm2, expr_comm2, expr_comm2);
                            let expr_comm4: Cons = hash4(expr_comm, expr_comm3, expr_comm3, expr_comm3);
                            let expr_comm5: Cons = hash4(expr_comm, expr_comm4, expr_comm4, expr_comm4);
                        },
                        Outermost => {
                            let expr_outer: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
                            let expr_outer2: Cons = hash4(expr_outer, expr_outer, expr_outer, expr_outer);
                        }
                    };
                    let expr_aux: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
                    let expr_out: Cons = hash4(expr_aux, expr_aux, expr_aux, expr_aux);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                },
                Char => {
                    let expr_aux: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
                    let expr_aux2: Cons = hash4(expr_aux, expr_aux, expr_aux, expr_aux);
                    let expr_out: Cons = hash4(expr_aux2, expr_aux2, expr_aux2, expr_aux2);
                    let cont_out_terminal: Terminal;
                    return (expr_out, env_in, cont_out_terminal);
                }
            };
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 0,
            hash4_idx: 7,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }

    #[test]
    fn test_hash4_slots_seq() {
        let lem = lem!(expr_in env_in cont_in {
            let expr_aux: Cons = hash4(expr_in, expr_in, expr_in, expr_in);
            let expr_out: Cons = hash4(expr_aux, expr_aux, expr_aux, expr_aux);
            let cont_out_terminal: Terminal;
            return (expr_out, env_in, cont_out_terminal);
        })
        .unwrap();

        let expr = Ptr::num(Fr::from_u64(42));
        let mut store = Store::default();
        let valuations = lem.eval(expr, &mut store).unwrap();
        let max_indices = SlotsIndices {
            hash2_idx: 0,
            hash3_idx: 0,
            hash4_idx: 2,
        };
        constrain_test_helper(&lem, &mut store, &valuations, &max_indices);
    }
}
