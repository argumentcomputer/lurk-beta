use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};

use super::{
    query::{CircuitQuery, Query, RecursiveQuery},
    CircuitScope, LogMemo, LogMemoCircuit, Scope,
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
    type C = ();

    fn eval(&self, scope: &mut Scope<Self, LogMemo<F>, F>) -> Ptr {
        let s = scope.store.as_ref();
        match self {
            Self::Lookup(var, env) => {
                if let Some([v, val, new_env]) = s.pop_binding(*env) {
                    if s.ptr_eq(var, &v) {
                        let t = s.intern_t();
                        s.cons(val, t)
                    } else {
                        self.recursive_eval(scope, Self::Lookup(*var, new_env))
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

    fn to_circuit<CS: ConstraintSystem<F>>(&self, cs: &mut CS, s: &Store<F>) -> Self::CQ {
        match self {
            EnvQuery::Lookup(var, env) => {
                let allocated_var =
                    AllocatedNum::alloc_infallible(ns!(cs, "var"), || *s.hash_ptr(var).value());
                let allocated_env =
                    AllocatedNum::alloc_infallible(ns!(cs, "env"), || *s.hash_ptr(env).value());
                Self::CQ::Lookup(allocated_var, allocated_env)
            }
            _ => unreachable!(),
        }
    }

    fn dummy_from_index(_: &Self::C, s: &Store<F>, index: usize) -> Self {
        match index {
            0 => Self::Lookup(s.num(0.into()), s.num(0.into())),
            _ => unreachable!(),
        }
    }

    fn index(&self, _: &Self::C) -> usize {
        match self {
            Self::Lookup(_, _) => 0,
            _ => unreachable!(),
        }
    }

    fn count(_: &Self::C) -> usize {
        1
    }
}

impl<F: LurkField> RecursiveQuery<F> for EnvCircuitQuery<F> {
    fn post_recursion<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        subquery_results: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        assert_eq!(subquery_results.len(), 1);
        Ok(subquery_results[0].clone())
    }
}

impl<F: LurkField> CircuitQuery<F> for EnvCircuitQuery<F> {
    type C = ();
    fn synthesize_args<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        match self {
            Self::Lookup(var, env) => {
                let sym_tag = g.alloc_tag(ns!(cs, "sym_tag"), &ExprTag::Sym);
                let env_tag = g.alloc_tag(ns!(cs, "env_tag"), &ExprTag::Env);
                let var_alloc = AllocatedPtr::from_parts(sym_tag.clone(), var.clone());
                let env_alloc = AllocatedPtr::from_parts(env_tag.clone(), env.clone());

                construct_cons(ns!(cs, "args"), g, store, &var_alloc, &env_alloc)
            }
        }
    }

    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>, Self::C>,
        acc: &AllocatedPtr<F>,
        allocated_key: &AllocatedPtr<F>,
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError> {
        match self {
            Self::Lookup(var, env) => {
                let nil = store.intern_nil();
                let t = store.intern_t();
                let allocated_nil = g.alloc_ptr(cs, &nil, store);
                let allocated_t = g.alloc_ptr(cs, &t, store);

                let env_is_empty = alloc_is_zero(ns!(cs, "env_is_empty"), env)?;

                let (next_var, next_val, new_env) =
                    deconstruct_env(ns!(cs, "deconstruct_env"), store, &env_is_empty.not(), env)?;

                let var_matches = alloc_equal(ns!(cs, "var_matches"), var, &next_var)?;
                let is_immediate = or!(cs, &var_matches, &env_is_empty)?;

                let immediate_val = AllocatedPtr::pick(
                    ns!(cs, "immediate_val"),
                    &var_matches,
                    &next_val,
                    &allocated_nil,
                )?;

                let immediate_bound = AllocatedPtr::pick(
                    ns!(cs, "immediate_bound"),
                    &var_matches,
                    &allocated_t,
                    &allocated_nil,
                )?;

                let immediate_result = construct_cons(
                    ns!(cs, "immediate_result"),
                    g,
                    store,
                    &immediate_val,
                    &immediate_bound,
                )?;

                let subquery = Self::Lookup(var.clone(), new_env);

                self.recurse(
                    cs,
                    g,
                    store,
                    scope,
                    &[subquery],
                    &is_immediate.not(),
                    (&immediate_result, acc),
                    allocated_key,
                )
            }
        }
    }

    fn from_ptr<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        EnvQuery::from_ptr(s, ptr).map(|q| q.to_circuit(cs, s))
    }

    fn dummy_from_index<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, index: usize) -> Self {
        EnvQuery::dummy_from_index(&(), s, index).to_circuit(cs, s)
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
    use std::sync::Arc;

    #[test]
    fn test_env_lookup() {
        let s = Arc::new(Store::<F>::default());
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

        let mut scope: Scope<EnvQuery<F>, LogMemo<F>, F> = Scope::new(1, s, ());
        let mut test = |var, env, found| {
            let expected = if let Some(val) = found {
                scope.store.cons(val, t)
            } else {
                scope.store.cons(nil, nil)
            };

            let result = EnvQuery::Lookup(var, env).eval(&mut scope);
            assert!(scope.store.ptr_eq(&expected, &result))
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

        let s = &Arc::new(Store::<F>::default());

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
            // Without internal insertions transcribed.

            let (one_lookup_constraints, one_lookup_aux) =
                test_lookup_circuit_aux(s, a, empty, expect!["3525"], expect!["3541"]);

            test_lookup_circuit_aux(s, a, a_env, expect!["3525"], expect!["3541"]);

            let (two_lookup_constraints, two_lookup_aux) =
                test_lookup_circuit_aux(s, b, a_env, expect!["6459"], expect!["6485"]);

            test_lookup_circuit_aux(s, b, b_env, expect!["3525"], expect!["3541"]);
            test_lookup_circuit_aux(s, a, a2_env, expect!["3525"], expect!["3541"]);

            let (three_lookup_constraints, three_lookup_aux) =
                test_lookup_circuit_aux(s, c, b_env, expect!["9393"], expect!["9429"]);

            test_lookup_circuit_aux(s, c, c_env, expect!["3525"], expect!["3541"]);
            test_lookup_circuit_aux(s, c, a2_env, expect!["6459"], expect!["6485"]);

            let delta1_constraints = two_lookup_constraints - one_lookup_constraints;
            let delta2_constraints = three_lookup_constraints - two_lookup_constraints;
            let overhead_constraints = one_lookup_constraints - delta1_constraints;

            assert_eq!(delta1_constraints, delta2_constraints);

            // This is the number of constraints per lookup.
            expect_eq(delta1_constraints, expect!["2934"]);

            // This is the number of constraints in the constant overhead.
            expect_eq(overhead_constraints, expect!["591"]);

            let delta1_aux = two_lookup_aux - one_lookup_aux;
            let delta2_aux = three_lookup_aux - two_lookup_aux;
            let overhead_aux = one_lookup_aux - delta1_aux;

            assert_eq!(delta1_aux, delta2_aux);

            // This is the number of aux per lookup.
            expect_eq(delta1_aux, expect!["2944"]);

            // This is the number of aux in the constant overhead.
            expect_eq(overhead_aux, expect!["597"]);
        }
    }

    fn test_lookup_circuit_aux(
        s: &Arc<Store<F>>,
        sym: Ptr,
        env: Ptr,
        expected_constraints_simple: Expect,
        expected_aux_simple: Expect,
    ) -> (usize, usize) {
        let state = State::init_lurk_state();
        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };

        let mut scope: Scope<EnvQuery<F>, LogMemo<F>, F> = Scope::new(1, s.clone(), ());

        let make_query = |sym, env| EnvQuery::Lookup(sym, env).to_ptr(s);

        {
            let query = make_query(sym, env);

            scope.query(query);

            for (k, v) in scope.queries.iter() {
                println!("k: {}", k.fmt_to_string(s, &state));
                println!("v: {}", v.fmt_to_string(s, &state));
            }

            scope.finalize_transcript();

            let cs = &mut TestConstraintSystem::new();
            let g = &GlobalAllocator::default();

            scope.synthesize(cs, g).unwrap();

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
