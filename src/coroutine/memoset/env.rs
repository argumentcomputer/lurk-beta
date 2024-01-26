use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};

use super::{
    query::{CircuitQuery, Query},
    CircuitScope, CircuitTranscript, LogMemo, LogMemoCircuit, Scope,
};
use crate::circuit::gadgets::constraints::{alloc_equal, alloc_is_zero};
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coprocessor::gadgets::{construct_cons, deconstruct_env};
use crate::field::LurkField;
use crate::lem::circuit::GlobalAllocator;
use crate::lem::{pointers::Ptr, store::Store};
use crate::symbol::Symbol;
use crate::tag::ExprTag;

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub(crate) enum EnvQuery<F> {
    Lookup(Ptr, Ptr),
    Phantom(F),
}

#[derive(Debug, Clone)]
pub(crate) enum EnvCircuitQuery<F: LurkField> {
    Lookup(AllocatedNum<F>, AllocatedNum<F>),
}

impl<F: LurkField> Query<F> for EnvQuery<F> {
    type CQ = EnvCircuitQuery<F>;

    fn eval(&self, s: &Store<F>, scope: &mut Scope<Self, LogMemo<F>>) -> Ptr {
        match self {
            Self::Lookup(var, env) => {
                if let Some([v, val, new_env]) = s.pop_binding(*env) {
                    if s.ptr_eq(var, &v) {
                        let t = s.intern_t();
                        s.cons(val, t)
                    } else {
                        self.recursive_eval(scope, s, Self::Lookup(*var, new_env))
                    }
                } else {
                    let nil = s.intern_nil();
                    s.cons(nil, nil)
                }
            }
            _ => unreachable!(),
        }
    }

    fn symbol(&self) -> Symbol {
        match self {
            Self::Lookup(_, _) => Symbol::sym(&["lurk", "env", "lookup"]),
            _ => unreachable!(),
        }
    }

    fn from_ptr(s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        let (head, body) = s.car_cdr(ptr).expect("query should be cons");
        let sym = s.fetch_sym(&head).expect("head should be sym");

        if sym == Symbol::sym(&["lurk", "env", "lookup"]) {
            let (var, env) = s.car_cdr(&body).expect("query body should be cons");
            Some(Self::Lookup(var, env))
        } else {
            None
        }
    }

    fn to_ptr(&self, s: &Store<F>) -> Ptr {
        match self {
            Self::Lookup(var, env) => {
                let lookup = s.intern_symbol(&self.symbol());
                // Since var and env will actually be single field elements in the circuit, we could reduce the cost of
                // this to use a smaller hash. This could get ugly fast, but this possibility is a consequence of the
                // optimized env-binding data structure we've adopted.
                let args = s.cons(*var, *env);
                s.cons(lookup, args)
            }
            _ => unreachable!(),
        }
    }

    fn index(&self) -> usize {
        match self {
            Self::Lookup(_, _) => 0,
            _ => unreachable!(),
        }
    }

    fn count() -> usize {
        1
    }
}

impl<F: LurkField> CircuitQuery<F> for EnvCircuitQuery<F> {
    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>>,
        acc: &AllocatedPtr<F>,
        transcript: &CircuitTranscript<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, CircuitTranscript<F>), SynthesisError> {
        match self {
            Self::Lookup(var, env) => {
                let nil = store.intern_nil();
                let t = store.intern_t();
                let allocated_nil = g.alloc_ptr(cs, &nil, store);
                let allocated_t = g.alloc_ptr(cs, &t, store);
                let sym_tag = g.alloc_tag(&mut cs.namespace(|| "sym_tag"), &ExprTag::Sym);
                let env_tag = g.alloc_tag(&mut cs.namespace(|| "env_tag"), &ExprTag::Env);

                let env_is_empty = alloc_is_zero(&mut cs.namespace(|| "env_is_empty"), env)?;

                let (next_var, next_val, new_env) = deconstruct_env(
                    &mut cs.namespace(|| "deconstruct_env"),
                    store,
                    &env_is_empty.not(),
                    env,
                )?;

                let var_matches = alloc_equal(&mut cs.namespace(|| "var_matches"), var, &next_var)?;
                let is_immediate = or!(cs, &var_matches, &env_is_empty)?;

                let immediate_val = AllocatedPtr::pick(
                    &mut cs.namespace(|| "immediate_val"),
                    &var_matches,
                    &next_val,
                    &allocated_nil,
                )?;

                let immediate_bound = AllocatedPtr::pick(
                    &mut cs.namespace(|| "immediate_bound"),
                    &var_matches,
                    &allocated_t,
                    &allocated_nil,
                )?;

                let immediate_result = construct_cons(
                    &mut cs.namespace(|| "immediate_result"),
                    g,
                    store,
                    &immediate_val,
                    &immediate_bound,
                )?;

                let (recursive_result, recursive_acc, recursive_transcript) = {
                    let subquery = {
                        let symbol = g.alloc_ptr(cs, &self.symbol_ptr(store), store);

                        let new_env_x = AllocatedPtr::from_parts(env_tag.clone(), new_env);
                        let var_x = AllocatedPtr::from_parts(sym_tag.clone(), var.clone());

                        let recursive_args = construct_cons(
                            &mut cs.namespace(|| "recursive_args"),
                            g,
                            store,
                            &var_x,
                            &new_env_x,
                        )?;

                        construct_cons(
                            &mut cs.namespace(|| "subquery"),
                            g,
                            store,
                            &symbol,
                            &recursive_args,
                        )?
                    };

                    let (sub_result, new_acc, new_transcript) = scope.synthesize_internal_query(
                        &mut cs.namespace(|| "recursive query"),
                        g,
                        store,
                        &subquery,
                        acc,
                        transcript,
                        &is_immediate.not(),
                    )?;

                    (sub_result, new_acc, new_transcript)
                };

                let value = AllocatedPtr::pick(
                    &mut cs.namespace(|| "pick value"),
                    &is_immediate,
                    &immediate_result,
                    &recursive_result,
                )?;

                let acc = AllocatedPtr::pick(
                    &mut cs.namespace(|| "pick acc"),
                    &is_immediate,
                    acc,
                    &recursive_acc,
                )?;

                let transcript = CircuitTranscript::pick(
                    &mut cs.namespace(|| "pick recursive_transcript"),
                    &is_immediate,
                    transcript,
                    &recursive_transcript,
                )?;

                Ok((value, acc, transcript))
            }
        }
    }

    fn from_ptr<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        let query = EnvQuery::from_ptr(s, ptr);
        if let Some(q) = query {
            match q {
                EnvQuery::Lookup(var, env) => {
                    let allocated_var =
                        AllocatedNum::alloc_infallible(&mut cs.namespace(|| "var"), || {
                            *s.hash_ptr(&var).value()
                        });
                    let allocated_env =
                        AllocatedNum::alloc_infallible(&mut cs.namespace(|| "env"), || {
                            *s.hash_ptr(&env).value()
                        });
                    Some(Self::Lookup(allocated_var, allocated_env))
                }
                _ => unreachable!(),
            }
        } else {
            None
        }
    }

    fn symbol(&self) -> Symbol {
        match self {
            Self::Lookup(_, _) => Symbol::sym(&["lurk", "env", "lookup"]),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::state::State;
    use crate::sym;

    use bellpepper_core::{test_cs::TestConstraintSystem, Comparable};
    use expect_test::{expect, Expect};
    use ff::Field;
    use halo2curves::bn256::Fr as F;
    use std::default::Default;

    #[test]
    fn test_env_lookup() {
        let s = Store::<F>::default();
        let mut scope: Scope<EnvQuery<F>, LogMemo<F>> = Scope::default();
        let a = s.intern_symbol(&sym!("a"));
        let b = s.intern_symbol(&sym!("b"));
        let c = s.intern_symbol(&sym!("c"));

        let one = s.num(F::ONE);
        let two = s.num(F::from_u64(2));
        let three = s.num(F::from_u64(3));
        let four = s.num(F::from_u64(4));

        let empty = s.intern_empty_env();
        let a_env = s.push_binding(a, one, empty);
        let b_env = s.push_binding(b, two, a_env);
        let c_env = s.push_binding(c, three, b_env);
        let a2_env = s.push_binding(a, four, c_env);

        let t = s.intern_t();
        let nil = s.intern_nil();

        let mut test = |var, env, found| {
            let expected = if let Some(val) = found {
                s.cons(val, t)
            } else {
                s.cons(nil, nil)
            };

            let result = EnvQuery::Lookup(var, env).eval(&s, &mut scope);
            assert!(s.ptr_eq(&expected, &result))
        };

        test(a, empty, None);
        test(a, a_env, Some(one));
        test(b, a_env, None);
        test(b, b_env, Some(two));
        test(a, a2_env, Some(four));
        test(c, b_env, None);
        test(c, c_env, Some(three));
        test(c, a2_env, Some(three));
    }

    #[test]
    fn test_lookup_circuit() {
        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };

        let s = &Store::<F>::default();

        let a = s.intern_symbol(&sym!("a"));
        let b = s.intern_symbol(&sym!("b"));
        let c = s.intern_symbol(&sym!("c"));

        let one = s.num(F::ONE);
        let two = s.num(F::from_u64(2));
        let three = s.num(F::from_u64(3));
        let four = s.num(F::from_u64(4));

        let empty = s.intern_empty_env();
        let a_env = s.push_binding(a, one, empty);
        let b_env = s.push_binding(b, two, a_env);
        let c_env = s.push_binding(c, three, b_env);
        let a2_env = s.push_binding(a, four, c_env);

        {
            // With internal insertions transcribed.

            let (one_lookup_constraints, one_lookup_aux) =
                test_lookup_circuit_aux(s, a, empty, true, expect!["3227"], expect!["3238"]);

            test_lookup_circuit_aux(s, a, a_env, true, expect!["3227"], expect!["3238"]);

            let (two_lookup_constraints, two_lookup_aux) =
                test_lookup_circuit_aux(s, b, a_env, true, expect!["5856"], expect!["5875"]);

            test_lookup_circuit_aux(s, b, b_env, true, expect!["3227"], expect!["3238"]);
            test_lookup_circuit_aux(s, a, a2_env, true, expect!["3227"], expect!["3238"]);

            let (three_lookup_constraints, three_lookup_aux) =
                test_lookup_circuit_aux(s, c, b_env, true, expect!["8485"], expect!["8512"]);

            test_lookup_circuit_aux(s, c, c_env, true, expect!["3227"], expect!["3238"]);
            test_lookup_circuit_aux(s, c, a2_env, true, expect!["5856"], expect!["5875"]);

            let delta1_constraints = two_lookup_constraints - one_lookup_constraints;
            let delta2_constraints = three_lookup_constraints - two_lookup_constraints;
            let overhead_constraints = one_lookup_constraints - delta1_constraints;

            assert_eq!(delta1_constraints, delta2_constraints);

            // This is the number of constraints per lookup.
            expect_eq(delta1_constraints, expect!["2629"]);

            // This is the number of constraints in the constant overhead.
            expect_eq(overhead_constraints, expect!["598"]);

            let delta1_aux = two_lookup_aux - one_lookup_aux;
            let delta2_aux = three_lookup_aux - two_lookup_aux;
            let overhead_aux = one_lookup_aux - delta1_aux;

            assert_eq!(delta1_aux, delta2_aux);

            // This is the number of aux per lookup.
            expect_eq(delta1_aux, expect!["2637"]);

            // This is the number of aux in the constant overhead.
            expect_eq(overhead_aux, expect!["601"]);
        }

        {
            // Without internal insertions transcribed.

            let (one_lookup_constraints, one_lookup_aux) =
                test_lookup_circuit_aux(s, a, empty, false, expect!["2938"], expect!["2949"]);

            test_lookup_circuit_aux(s, a, a_env, false, expect!["2938"], expect!["2949"]);

            let (two_lookup_constraints, two_lookup_aux) =
                test_lookup_circuit_aux(s, b, a_env, false, expect!["5278"], expect!["5297"]);

            test_lookup_circuit_aux(s, b, b_env, false, expect!["2938"], expect!["2949"]);
            test_lookup_circuit_aux(s, a, a2_env, false, expect!["2938"], expect!["2949"]);

            let (three_lookup_constraints, three_lookup_aux) =
                test_lookup_circuit_aux(s, c, b_env, false, expect!["7618"], expect!["7645"]);

            test_lookup_circuit_aux(s, c, c_env, false, expect!["2938"], expect!["2949"]);
            test_lookup_circuit_aux(s, c, a2_env, false, expect!["5278"], expect!["5297"]);

            let delta1_constraints = two_lookup_constraints - one_lookup_constraints;
            let delta2_constraints = three_lookup_constraints - two_lookup_constraints;
            let overhead_constraints = one_lookup_constraints - delta1_constraints;

            assert_eq!(delta1_constraints, delta2_constraints);

            // This is the number of constraints per lookup.
            expect_eq(delta1_constraints, expect!["2340"]);

            // This is the number of constraints in the constant overhead.
            expect_eq(overhead_constraints, expect!["598"]);

            let delta1_aux = two_lookup_aux - one_lookup_aux;
            let delta2_aux = three_lookup_aux - two_lookup_aux;
            let overhead_aux = one_lookup_aux - delta1_aux;

            assert_eq!(delta1_aux, delta2_aux);

            // This is the number of aux per lookup.
            expect_eq(delta1_aux, expect!["2348"]);

            // This is the number of aux in the constant overhead.
            expect_eq(overhead_aux, expect!["601"]);
        }
    }

    fn test_lookup_circuit_aux(
        s: &Store<F>,
        sym: Ptr,
        env: Ptr,
        transcribe_internal_insertions: bool,
        expected_constraints_simple: Expect,
        expected_aux_simple: Expect,
    ) -> (usize, usize) {
        let state = State::init_lurk_state();
        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };

        let mut scope: Scope<EnvQuery<F>, LogMemo<F>> = Scope::new(transcribe_internal_insertions);

        let make_query = |sym, env| EnvQuery::Lookup(sym, env).to_ptr(s);

        {
            let query = make_query(sym, env);

            scope.query(s, query);

            for (k, v) in scope.queries.iter() {
                println!("k: {}", k.fmt_to_string(s, &state));
                println!("v: {}", v.fmt_to_string(s, &state));
            }

            scope.finalize_transcript(s);

            let cs = &mut TestConstraintSystem::new();
            let g = &mut GlobalAllocator::default();

            scope.synthesize(cs, g, s).unwrap();

            println!(
                "transcript: {}",
                scope
                    .memoset
                    .transcript
                    .get()
                    .unwrap()
                    .fmt_to_string_simple(s)
            );

            expect_eq(cs.num_constraints(), expected_constraints_simple);
            expect_eq(cs.aux().len(), expected_aux_simple);

            let unsat = cs.which_is_unsatisfied();

            if unsat.is_some() {
                dbg!(unsat);
            }
            assert!(cs.is_satisfied());

            (cs.num_constraints(), cs.aux().len())
        }
    }
}
