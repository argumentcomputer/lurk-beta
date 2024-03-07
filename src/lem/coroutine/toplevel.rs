use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coprocessor::gadgets::construct_cons;
use crate::coroutine::memoset::{
    CircuitQuery, CircuitScope, LogMemo, LogMemoCircuit, Query, Scope,
};
use crate::field::LurkField;
use crate::lem::circuit::BoundAllocations;
use crate::lem::{circuit::GlobalAllocator, pointers::Ptr, store::Store, Func};
use crate::symbol::Symbol;

use anyhow::{bail, Context, Result};
use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use indexmap::IndexMap;
use std::marker::PhantomData;
use std::sync::Arc;

use super::eval::call;
use super::synthesis::synthesize_call;

#[derive(Clone)]
pub struct Coroutine<F> {
    pub func: Func,
    pub rc: usize,
    pub _p: PhantomData<F>,
}

#[derive(Clone)]
pub struct Toplevel<F>(IndexMap<Symbol, Coroutine<F>>);

fn compute_rc(_func: &Func) -> usize {
    // TODO
    1
}

impl<F> Toplevel<F> {
    pub fn new(funcs: Vec<(Symbol, Func)>) -> Self {
        let mut toplevel = IndexMap::new();
        for (name, func) in funcs.into_iter() {
            let rc = compute_rc(&func);
            let _p = PhantomData;
            toplevel.insert(name, Coroutine { func, rc, _p });
        }
        Toplevel(toplevel)
    }

    pub fn get(&self, name: &Symbol) -> Option<&Coroutine<F>> {
        self.0.get(name)
    }
}

#[derive(Clone)]
pub struct ToplevelQuery<F> {
    pub(crate) name: Symbol,
    pub(crate) args: Vec<Ptr>,
    pub(crate) _p: PhantomData<F>,
}

#[derive(Clone)]
pub struct ToplevelCircuitQuery<F: LurkField> {
    pub(crate) name: Symbol,
    pub(crate) args: Vec<AllocatedPtr<F>>,
}

impl<F> ToplevelQuery<F> {
    pub fn new(name: Symbol, args: Vec<Ptr>, toplevel: &Toplevel<F>) -> Result<Self> {
        let msg = || format!("`{name}` not found in the toplevel");
        let coroutine = toplevel.0.get(&name).with_context(msg)?;
        let input_size = coroutine.func.input_params.len();
        if args.len() != input_size {
            bail!(
                "Wrong number of arguments. Expected {}, found {}",
                args.len(),
                input_size
            )
        }
        let _p = PhantomData;
        let query = ToplevelQuery { name, args, _p };
        Ok(query)
    }
}

impl<F: LurkField> ToplevelCircuitQuery<F> {
    pub fn new(name: Symbol, args: Vec<AllocatedPtr<F>>, toplevel: &Toplevel<F>) -> Result<Self> {
        let msg = || format!("`{name}` not found in the toplevel");
        let coroutine = toplevel.0.get(&name).with_context(msg)?;
        let input_size = coroutine.func.input_params.len();
        if args.len() != input_size {
            bail!(
                "Wrong number of arguments. Expected {}, found {}",
                args.len(),
                input_size
            )
        }
        let query = ToplevelCircuitQuery { name, args };
        Ok(query)
    }
}

impl<F: LurkField> Query<F> for ToplevelQuery<F> {
    type CQ = ToplevelCircuitQuery<F>;
    type RD = Arc<Toplevel<F>>;
    fn eval(&self, scope: &mut Scope<Self, LogMemo<F>, F>) -> Ptr {
        let name = &self.name;
        let args = &self.args;
        let toplevel = scope.runtime_data.clone();
        let coroutine = toplevel.get(name).unwrap();
        let outputs = call(self, &coroutine.func, args, scope).unwrap();
        to_improper_list(&outputs, scope.store.as_ref())
    }
    fn to_circuit<CS: ConstraintSystem<F>>(&self, cs: &mut CS, s: &Store<F>) -> Self::CQ {
        let name = self.name.clone();
        let mut args = vec![];
        for (i, arg) in self.args.iter().enumerate() {
            let cs = ns!(cs, format!("arg:{i}"));
            let alloc = AllocatedPtr::alloc_infallible(cs, || s.hash_ptr(arg));
            args.push(alloc);
        }
        ToplevelCircuitQuery { name, args }
    }
    fn from_ptr(toplevel: &Arc<Toplevel<F>>, s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        let (head, mut acc) = s.car_cdr(ptr).expect("query should be cons");
        let name = s.fetch_sym(&head).expect("head should be sym");
        let num_args = toplevel.get(&name).unwrap().func.input_params.len();
        assert!(num_args > 0, "cannot yet make 0 argument queries");
        let mut args = vec![];
        let _p = PhantomData;
        if !acc.is_nil() {
            while args.len() < num_args - 1 {
                let (arg, rest) = s.car_cdr(&acc).expect("can't find image for cons");
                args.push(arg);
                acc = rest;
            }
        }
        args.push(acc);
        assert_eq!(args.len(), num_args);
        Some(ToplevelQuery { name, args, _p })
    }
    fn to_ptr(&self, s: &Store<F>) -> Ptr {
        let args = to_improper_list(&self.args, s);
        let name = s.intern_symbol(&self.name);
        s.cons(name, args)
    }
    fn dummy_from_index(toplevel: &Self::RD, s: &Store<F>, index: usize) -> Self {
        let (name, coroutine) = toplevel.0.get_index(index).unwrap();
        let name = name.clone();
        let args_size = coroutine.func.input_params.len();
        let args = vec![s.num(0.into()); args_size];
        let _p = PhantomData;
        ToplevelQuery { name, args, _p }
    }
    fn symbol(&self) -> Symbol {
        self.name.clone()
    }
    fn index(&self, toplevel: &Self::RD) -> usize {
        toplevel.0.get_index_of(&self.name).unwrap()
    }
    fn count(toplevel: &Self::RD) -> usize {
        toplevel.0.len()
    }
}

impl<F: LurkField> CircuitQuery<F> for ToplevelCircuitQuery<F> {
    type RD = Arc<Toplevel<F>>;
    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>, Self::RD>,
        acc: &AllocatedPtr<F>,
        allocated_key: &AllocatedPtr<F>,
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError> {
        let name = &self.name;
        let toplevel = scope.runtime_data.clone();
        let coroutine = toplevel.get(name).unwrap();

        let params = coroutine.func.input_params.iter().cloned();
        let args = self.args.iter().cloned();
        let bound_allocations = &mut BoundAllocations::new();
        for (param, arg) in params.zip(args) {
            bound_allocations.insert_ptr(param, arg);
        }
        let func = &coroutine.func;
        let mut next_acc = acc.clone();
        let mut sub_provenances = vec![];
        // TODO in the case of blank circuits, this should be `false`
        let not_dummy = &Boolean::Constant(true);
        let res = synthesize_call(
            cs,
            func,
            not_dummy,
            g,
            store,
            scope,
            bound_allocations,
            &mut next_acc,
            &mut sub_provenances,
        )
        .unwrap();
        let value = to_allocated_improper_list(cs, &res, g, store)?;
        let provenance = self.synthesize_provenance(
            ns!(cs, "provenance"),
            g,
            store,
            value.clone(),
            sub_provenances,
            allocated_key,
        )?;
        Ok(((value, provenance), next_acc))
    }

    fn symbol(&self) -> Symbol {
        self.name.clone()
    }

    fn from_ptr<CS: ConstraintSystem<F>>(_: &mut CS, _: &Store<F>, _: &Ptr) -> Option<Self> {
        unimplemented!()
    }

    fn dummy_from_index<CS: ConstraintSystem<F>>(_: &mut CS, _: &Store<F>, _: usize) -> Self {
        unimplemented!()
    }

    #[allow(unused_variables)]
    fn synthesize_args<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        to_allocated_improper_list(cs, &self.args, g, store)
    }
}

pub(crate) fn to_allocated_improper_list<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    args: &[AllocatedPtr<F>],
    g: &GlobalAllocator<F>,
    s: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    if args.is_empty() {
        let nil = s.intern_nil();
        let allocated_nil = g.alloc_ptr(cs, &nil, s);
        Ok(allocated_nil)
    } else {
        // Iterator from last to first. Enumerate indices used for namespaces
        let mut iter = args.iter().rev();
        let mut args = iter.next().unwrap().clone();
        for (i, arg) in iter.enumerate() {
            let cs = ns!(cs, format!("arg:{i}"));
            args = construct_cons(cs, g, s, arg, &args)?;
        }
        Ok(args)
    }
}

pub(crate) fn to_improper_list<F: LurkField>(args: &[Ptr], s: &Store<F>) -> Ptr {
    if args.is_empty() {
        s.intern_nil()
    } else {
        // Iterator from last to first
        let mut iter = args.iter().rev();
        let mut args = *iter.next().unwrap();
        for arg in iter {
            args = s.cons(*arg, args);
        }
        args
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::coroutine::memoset::prove::MemosetProver;
    use crate::coroutine::memoset::CoroutineCircuit;
    use crate::lem::tag::Tag;
    use crate::proof::{Prover, RecursiveSNARKTrait};
    use crate::{func, state::user_sym};

    use bellpepper::util_cs::bench_cs::BenchCS;
    use expect_test::expect;
    use halo2curves::bn256::Fr as F;

    fn sample_toplevel() -> (Arc<Toplevel<F>>, [Symbol; 4]) {
        let id = func!(id(x): 1 => { return (x) });
        let factorial = func!(factorial(n): 1 => {
            let zero = Num(0);
            let one = Num(1);
            let n_is_zero = eq_val(n, zero);
            if n_is_zero {
                return (one)
            }
            let m = sub(n, one);
            let p = QUERY("factorial", m);
            let res = mul(n, p);
            return (res)
        });
        let even = func!(even(n): 1 => {
            let zero = Num(0);
            let one = Num(1);
            let n_is_zero = eq_val(n, zero);
            if n_is_zero {
                return (one)
            }
            let m = sub(n, one);
            let res = QUERY("odd", m);
            return (res)
        });
        let odd = func!(odd(n): 1 => {
            let zero = Num(0);
            let n_is_zero = eq_val(n, zero);
            if n_is_zero {
                return (zero)
            }
            let one = Num(1);
            let m = sub(n, one);
            let res = QUERY("even", m);
            return (res)
        });
        let id_sym = user_sym("id");
        let factorial_sym = user_sym("factorial");
        let even_sym = user_sym("even");
        let odd_sym = user_sym("odd");
        let toplevel = Arc::new(Toplevel::<F>::new(vec![
            (id_sym.clone(), id),
            (factorial_sym.clone(), factorial),
            (even_sym.clone(), even),
            (odd_sym.clone(), odd),
        ]));
        let symbols = [id_sym, factorial_sym, even_sym, odd_sym];
        (toplevel, symbols)
    }

    #[test]
    fn lem_coroutine_eval_test() {
        let (toplevel, [_, factorial_sym, even_sym, odd_sym]) = sample_toplevel();
        let s = Arc::new(Store::<F>::default());

        let query1 = ToplevelQuery::<F>::new(factorial_sym, vec![s.num_u64(5)], &toplevel).unwrap();
        let query2 = ToplevelQuery::<F>::new(even_sym, vec![s.num_u64(5)], &toplevel).unwrap();
        let query3 = ToplevelQuery::<F>::new(odd_sym, vec![s.num_u64(5)], &toplevel).unwrap();
        let scope = &mut Scope::<ToplevelQuery<F>, LogMemo<F>, F>::new(1, s, toplevel);
        let res1 = query1.eval(scope);
        let res2 = query2.eval(scope);
        let res3 = query3.eval(scope);
        assert_eq!(res1, scope.store.num_u64(120));
        assert_eq!(res2, scope.store.num_u64(0));
        assert_eq!(res3, scope.store.num_u64(1));
    }

    #[test]
    fn lem_coroutine_prove_test() {
        let (toplevel, _) = sample_toplevel();
        let s = Arc::new(Store::<F>::default());

        let prover = MemosetProver::<'_, F, ToplevelQuery<F>>::new(10);
        let pp = prover.public_params(toplevel.clone(), s.clone());

        // This query is only necessary because Arecibo assumes that the first circuit
        // to run is 0. Eventually, this will be replaced by the coroutine prologue
        let id_query = s.read_with_default_state("(id . 0)").unwrap();

        let query = s.read_with_default_state("(factorial . 5)").unwrap();
        let mut scope = Scope::new(prover.reduction_count(), s.clone(), toplevel.clone());
        scope.query(id_query);
        scope.query(query);
        scope.finalize_transcript();
        let (snark, input, output, _iterations) = prover.prove_from_scope(&pp, &scope).unwrap();
        // Memoset acc is 0
        assert_eq!(output[7], F::zero());
        // Transcript is correct
        assert_eq!(output[9], output[11]);
        assert!(snark.verify(&pp, &input, &output).unwrap());

        let query = s.read_with_default_state("(even . 5)").unwrap();
        let mut scope = Scope::new(prover.reduction_count(), s, toplevel);
        scope.query(id_query);
        scope.query(query);
        scope.finalize_transcript();
        let (snark, input, output, _iterations) = prover.prove_from_scope(&pp, &scope).unwrap();
        assert_eq!(output[7], F::zero());
        assert_eq!(output[9], output[11]);
        assert!(snark.verify(&pp, &input, &output).unwrap());
    }

    #[test]
    fn lem_coroutine_size_test() {
        let (toplevel, [_, factorial, even, _]) = sample_toplevel();
        let s = Arc::new(Store::<F>::default());
        let index = toplevel.0.get_index_of(&factorial).unwrap();
        let factorial_circuit = CoroutineCircuit::<_, _, ToplevelQuery<_>>::blank(
            index,
            s.clone(),
            1,
            toplevel.clone(),
        );
        let mut cs = BenchCS::new();
        let dummy = [
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
        ];
        factorial_circuit
            .supernova_synthesize(&mut cs, &dummy)
            .unwrap();
        expect!("1772").assert_eq(&cs.num_constraints().to_string());

        let index = toplevel.0.get_index_of(&even).unwrap();
        let even_circuit = CoroutineCircuit::<_, _, ToplevelQuery<_>>::blank(
            index,
            s.clone(),
            1,
            toplevel.clone(),
        );
        let mut cs = BenchCS::new();
        let dummy = [
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
            AllocatedPtr::alloc_infallible::<_, _, Tag>(&mut cs, || unreachable!()),
        ];
        even_circuit.supernova_synthesize(&mut cs, &dummy).unwrap();
        expect!("1772").assert_eq(&cs.num_constraints().to_string());
    }

    #[test]
    fn prove_sum_list_coroutine() {
        let build_list = func!(build_list(n): 1 => {
            let zero = Num(0);
            let n_is_zero = eq_val(n, zero);
            if n_is_zero {
                let nil: Expr::Nil;
                return (nil)
            }
            let one = Num(1);
            let m = sub(n, one);
            let ys = QUERY("build-list", m);
            let xs: Expr::Cons = cons2(n, ys);
            return (xs)
        });
        let sum_list = func!(sum_list(xs): 1 => {
            match xs.tag {
                Expr::Nil => {
                    let zero = Num(0);
                    return (zero)
                }
                Expr::Cons => {
                    let (n, ys) = decons2(xs);
                    let m = QUERY("sum-list", ys);
                    let res = add(n, m);
                    return (res)
                }
            }
        });
        let main = func!(main(n): 1 => {
            let xs = QUERY("build-list", n);
            let n = QUERY("sum-list", xs);
            return (n)
        });
        let main_sym = user_sym("main");
        let build_list_sym = user_sym("build-list");
        let sum_list_sym = user_sym("sum-list");
        let toplevel = Arc::new(Toplevel::<F>::new(vec![
            (main_sym.clone(), main),
            (build_list_sym.clone(), build_list),
            (sum_list_sym.clone(), sum_list),
        ]));
        let s = Arc::new(Store::<F>::default());

        let query = ToplevelQuery::<F>::new(main_sym, vec![s.num_u64(10)], &toplevel).unwrap();
        let scope =
            &mut Scope::<ToplevelQuery<F>, LogMemo<F>, F>::new(1, s.clone(), toplevel.clone());
        let res = query.eval(scope);
        assert_eq!(res, scope.store.num_u64(55));

        let prover = MemosetProver::<'_, F, ToplevelQuery<F>>::new(1);
        let query = s.read_with_default_state("(main . 10)").unwrap();
        let mut scope = Scope::new(prover.reduction_count(), s.clone(), toplevel.clone());
        scope.query(query);
        scope.finalize_transcript();
        let pp = prover.public_params(toplevel, s);
        let (snark, input, output, iterations) = prover.prove_from_scope(&pp, &scope).unwrap();
        assert_eq!(iterations, 23);
        assert_eq!(output[7], F::zero());
        assert_eq!(output[9], output[11]);
        assert!(snark.verify(&pp, &input, &output).unwrap());
    }
}
