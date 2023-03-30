use std::collections::BTreeMap;

use crate::field::LurkField;

#[cfg(not(target_arch = "wasm32"))]
use crate::field::FWrap;
use crate::store::{Pointer, Ptr, ScalarContPtr, ScalarPtr, Store};
use crate::tag::{ExprTag, Op1, Op2};
use crate::{Num, Sym, UInt};
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::Deserialize;
use serde::Serialize;

/// `ScalarStore` allows realization of a graph of `ScalarPtr`s suitable for serialization to IPLD. `ScalarExpression`s
/// are composed only of `ScalarPtr`s, so `scalar_map` suffices to allow traversing an arbitrary DAG.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScalarStore<F: LurkField> {
    scalar_map: BTreeMap<ScalarPtr<F>, Option<ScalarExpression<F>>>,
    scalar_cont_map: BTreeMap<ScalarContPtr<F>, Option<ScalarContinuation<F>>>,
    #[serde(skip)]
    pending_scalar_ptrs: Vec<ScalarPtr<F>>,
}

impl<F: LurkField> ScalarStore<F> {
    /// Create a new `ScalarStore` and add all `ScalarPtr`s reachable in the scalar representation of `expr`.
    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> (Self, Option<ScalarPtr<F>>) {
        let mut new = Self::default();
        let scalar_ptr = new.add_one_ptr(store, expr);
        if let Some(scalar_ptr) = scalar_ptr {
            (new, Some(scalar_ptr))
        } else {
            (new, None)
        }
    }

    /// Add all ScalarPtrs representing and reachable from expr.
    pub fn add_one_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) -> Option<ScalarPtr<F>> {
        let scalar_ptr = self.add_ptr(store, expr);
        self.finalize(store);
        scalar_ptr
    }

    /// Add the `ScalarPtr` representing `expr`, and queue it for proceessing.
    pub fn add_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) -> Option<ScalarPtr<F>> {
        // Find the scalar_ptr representing ptr.
        if let Some(scalar_ptr) = store.get_expr_hash(expr) {
            self.add(store, expr, scalar_ptr);
            Some(scalar_ptr)
        } else {
            None
        }
    }

    /// Add a single `ScalarPtr` and queue it for processing.
    /// NOTE: This requires that `store.scalar_cache` has been hydrated.
    fn add_scalar_ptr(&mut self, store: &Store<F>, scalar_ptr: ScalarPtr<F>) {
        // Find the ptr corresponding to scalar_ptr.
        if let Some(ptr) = store.scalar_ptr_map.get(&scalar_ptr) {
            self.add(store, &*ptr, scalar_ptr);
        }
    }

    /// Add the `ScalarPtr` and `ScalarExpression` associated with `ptr`. The relationship between `ptr` and
    /// `scalar_ptr` is not checked here, so `add` should only be called by `add_ptr` and `add_scalar_ptr`, which
    /// enforce this relationship.
    fn add(&mut self, store: &Store<F>, ptr: &Ptr<F>, scalar_ptr: ScalarPtr<F>) {
        let mut new_pending_scalar_ptrs: Vec<ScalarPtr<F>> = Default::default();

        // If `scalar_ptr` is not already in the map, queue its children for processing.
        self.scalar_map.entry(scalar_ptr).or_insert_with(|| {
            let scalar_expression = ScalarExpression::from_ptr(store, ptr)?;
            if let Some(more_scalar_ptrs) = Self::child_scalar_ptrs(&scalar_expression) {
                new_pending_scalar_ptrs.extend(more_scalar_ptrs);
            }
            Some(scalar_expression)
        });

        self.pending_scalar_ptrs.extend(new_pending_scalar_ptrs);
    }

    /// All the `ScalarPtr`s directly reachable from `scalar_expression`, if any.
    fn child_scalar_ptrs(scalar_expression: &ScalarExpression<F>) -> Option<Vec<ScalarPtr<F>>> {
        match scalar_expression {
            ScalarExpression::Nil => None,
            ScalarExpression::Cons(car, cdr) => Some([*car, *cdr].into()),
            ScalarExpression::Comm(_, payload) => Some([*payload].into()),
            ScalarExpression::Sym(_str) => None,
            ScalarExpression::Fun {
                arg,
                body,
                closed_env,
            } => Some([*arg, *body, *closed_env].into()),
            ScalarExpression::Num(_) => None,
            ScalarExpression::Str(_) => None,
            ScalarExpression::Thunk(_) => None,
            ScalarExpression::Char(_) => None,
            ScalarExpression::UInt(_) => None,
        }
    }

    /// Unqueue all the pending `ScalarPtr`s and add them, queueing all of their children, then repeat until the queue
    /// is pending queue is empty.
    fn add_pending_scalar_ptrs(&mut self, store: &Store<F>) {
        while let Some(scalar_ptr) = self.pending_scalar_ptrs.pop() {
            self.add_scalar_ptr(store, scalar_ptr);
        }
        assert!(self.pending_scalar_ptrs.is_empty());
    }

    /// Method which finalizes the `ScalarStore`, ensuring that all reachable `ScalarPtr`s have been added.
    pub fn finalize(&mut self, store: &Store<F>) {
        self.add_pending_scalar_ptrs(store);
    }
    pub fn get_expr(&self, ptr: &ScalarPtr<F>) -> Option<&ScalarExpression<F>> {
        let x = self.scalar_map.get(ptr)?;
        (*x).as_ref()
    }

    pub fn get_cont(&self, ptr: &ScalarContPtr<F>) -> Option<&ScalarContinuation<F>> {
        let x = self.scalar_cont_map.get(ptr)?;
        (*x).as_ref()
    }

    pub fn to_store_with_expr(&mut self, ptr: &ScalarPtr<F>) -> Option<(Store<F>, Ptr<F>)> {
        if self.pending_scalar_ptrs.is_empty() {
            let mut store = Store::new();

            let ptr = store.intern_scalar_ptr(*ptr, self)?;

            for scalar_ptr in self.scalar_map.keys() {
                store.intern_scalar_ptr(*scalar_ptr, self);
            }
            for ptr in self.scalar_cont_map.keys() {
                store.intern_scalar_cont_ptr(*ptr, self);
            }
            Some((store, ptr))
        } else {
            None
        }
    }
    pub fn to_store(&mut self) -> Option<Store<F>> {
        if self.pending_scalar_ptrs.is_empty() {
            let mut store = Store::new();

            for ptr in self.scalar_map.keys() {
                store.intern_scalar_ptr(*ptr, self);
            }
            for ptr in self.scalar_cont_map.keys() {
                store.intern_scalar_cont_ptr(*ptr, self);
            }
            Some(store)
        } else {
            None
        }
    }
    pub(crate) fn insert_scalar_expression(
        &mut self,
        ptr: ScalarPtr<F>,
        expr: Option<ScalarExpression<F>>,
    ) -> Option<Option<ScalarExpression<F>>> {
        self.scalar_map.insert(ptr, expr)
    }
}

impl<F: LurkField> ScalarExpression<F> {
    fn from_ptr(store: &Store<F>, ptr: &Ptr<F>) -> Option<Self> {
        match ptr.tag() {
            ExprTag::Nil => Some(ScalarExpression::Nil),
            ExprTag::Cons => store.fetch_cons(ptr).and_then(|(car, cdr)| {
                if let (Some(car), Some(cdr)) = (store.get_expr_hash(car), store.get_expr_hash(cdr))
                {
                    Some(ScalarExpression::Cons(car, cdr))
                } else {
                    None
                }
            }),
            ExprTag::Comm => store.fetch_comm(ptr).and_then(|(secret, payload)| {
                store
                    .get_expr_hash(payload)
                    .map(|payload| ScalarExpression::Comm(secret.0, payload))
            }),
            ExprTag::Sym | ExprTag::Key => store.fetch_sym(ptr).map(ScalarExpression::Sym),
            ExprTag::Fun => store.fetch_fun(ptr).and_then(|(arg, body, closed_env)| {
                if let (Some(arg), Some(body), Some(closed_env)) = (
                    store.get_expr_hash(arg),
                    store.get_expr_hash(body),
                    store.get_expr_hash(closed_env),
                ) {
                    Some(ScalarExpression::Fun {
                        arg,
                        body,
                        closed_env,
                    })
                } else {
                    None
                }
            }),
            ExprTag::Num => store.fetch_num(ptr).map(|num| match num {
                Num::U64(x) => ScalarExpression::Num((*x).into()),
                Num::Scalar(x) => ScalarExpression::Num(*x),
            }),
            ExprTag::Str => store
                .fetch_str(ptr)
                .map(|str| ScalarExpression::Str(str.to_string())),
            ExprTag::Char => store.fetch_char(ptr).map(ScalarExpression::Char),
            ExprTag::U64 => store.fetch_uint(ptr).map(ScalarExpression::UInt),
            ExprTag::Thunk => unimplemented!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub enum ScalarExpression<F: LurkField> {
    Nil,
    Cons(ScalarPtr<F>, ScalarPtr<F>),
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(
            strategy = "any::<(FWrap<F>, ScalarPtr<F>)>().prop_map(|(x, y)| Self::Comm(x.0, y))"
        )
    )]
    Comm(F, ScalarPtr<F>),
    Sym(Sym),
    Fun {
        arg: ScalarPtr<F>,
        body: ScalarPtr<F>,
        closed_env: ScalarPtr<F>,
    },
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| Self::Num(x.0))")
    )]
    Num(F),
    Str(String),
    Thunk(ScalarThunk<F>),
    Char(char),
    UInt(UInt),
}

impl<F: LurkField> Default for ScalarExpression<F> {
    fn default() -> Self {
        Self::Nil
    }
}

impl<F: LurkField> std::fmt::Display for ScalarExpression<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScalarExpression::Nil => write!(f, "Nil"),
            ScalarExpression::Cons(x, y) => write!(f, "Cons({}, {})", x, y),
            ScalarExpression::Comm(ff, x) => write!(f, "Comm({}, {})", ff.trimmed_hex_digits(), x),
            ScalarExpression::Sym(s) => write!(f, "Sym({})", s.full_sym_name()),
            ScalarExpression::Fun {
                arg,
                body,
                closed_env,
            } => write!(f, "Fun(arg:{}, body:{}, env:{})", arg, body, closed_env),
            ScalarExpression::Num(ff) => match ff.to_u64() {
                Some(u) => write!(f, "Num({})", u),
                None => write!(f, "Num({})", ff.trimmed_hex_digits(),),
            },
            ScalarExpression::Str(x) => write!(f, "Str({})", x),
            ScalarExpression::Thunk(x) => {
                write!(f, "Thunk(value:{}, cont:{})", x.value, x.continuation)
            }
            ScalarExpression::Char(x) => write!(f, "Char({})", x),
            ScalarExpression::UInt(x) => write!(f, "UInt({})", x),
        }
    }
}

// Unused for now, but will be needed when we serialize Thunks to IPLD.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub struct ScalarThunk<F: LurkField> {
    pub(crate) value: ScalarPtr<F>,
    pub(crate) continuation: ScalarContPtr<F>,
}

impl<F: LurkField> Copy for ScalarThunk<F> {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub enum ScalarContinuation<F: LurkField> {
    Outermost,
    Call {
        unevaled_arg: ScalarPtr<F>,
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Call2 {
        function: ScalarPtr<F>,
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Tail {
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Error,
    Lookup {
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Unop {
        operator: Op1,
        continuation: ScalarContPtr<F>,
    },
    Binop {
        operator: Op2,
        saved_env: ScalarPtr<F>,
        unevaled_args: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Binop2 {
        operator: Op2,
        evaled_arg: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    If {
        unevaled_args: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Let {
        var: ScalarPtr<F>,
        body: ScalarPtr<F>,
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    LetRec {
        var: ScalarPtr<F>,
        body: ScalarPtr<F>,
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Emit {
        continuation: ScalarContPtr<F>,
    },
    Dummy,
    Terminal,
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::eval::empty_sym_env;

    use blstrs::Scalar as Fr;

    use tap::TapFallible;

    use libipld::serde::from_ipld;
    use libipld::serde::to_ipld;

    proptest! {
        #[test]
        fn prop_scalar_thunk_ipld(x in any::<ScalarThunk<Fr>>())  {
            let to_ipld = to_ipld(x).unwrap();
            let y = from_ipld(to_ipld).unwrap();
            assert_eq!(x, y);
        }

        #[test]
        fn prop_scalar_expression_ipld(x in any::<ScalarExpression<Fr>>()) {
            let to_ipld = to_ipld(x.clone())
            .tap_err(|e| {
                println!("ser x: {x:?}");
                println!("err e: {e:?}");
            })
            .unwrap();

            let y = from_ipld(to_ipld.clone())
            .tap_err(|e| {
                println!("ser x: {x:?}");
                println!("de ipld: {to_ipld:?}");
                println!("err e: {e:?}");
            })
            .unwrap();

            println!("x: {x:?}");
            println!("y: {y:?}");

            assert_eq!(x, y);
        }


        #[test]
        fn prop_scalar_expr_ipld(x in any::< ScalarExpression<Fr>>()) {
            let to_ipld = to_ipld(x.clone()).unwrap();
            let from_ipld = from_ipld(to_ipld).unwrap();
            assert_eq!(x, from_ipld);
        }

        #[test]
        fn prop_scalar_cont_ipld(x in any::<ScalarContinuation<Fr>>()) {
            let to_ipld = to_ipld(x.clone()).unwrap();
            let from_ipld = from_ipld(to_ipld).unwrap();
            assert_eq!(x, from_ipld);
        }

    }

    // This doesn't create well-defined ScalarStores, so is only useful for
    // testing ipld
    fn ipld_scalar_store_strategy<Fr: LurkField>() -> impl Strategy<Value = ScalarStore<Fr>> {
        (
            prop::collection::btree_map(
                any::<ScalarPtr<Fr>>(),
                any::<Option<ScalarExpression<Fr>>>(),
                0..1,
            ),
            prop::collection::btree_map(
                any::<ScalarContPtr<Fr>>(),
                any::<Option<ScalarContinuation<Fr>>>(),
                0..1,
            ),
        )
            .prop_map(|(scalar_map, scalar_cont_map)| ScalarStore {
                scalar_map,
                scalar_cont_map,
                pending_scalar_ptrs: Vec::new(),
            })
            .boxed()
    }

    proptest! {
        #[test]
        fn prop_scalar_store_ipld(x in ipld_scalar_store_strategy::<Fr>()) {
            let to_ipld = to_ipld(x.clone()).unwrap();
            let from_ipld = from_ipld(to_ipld).unwrap();
            assert_eq!(x, from_ipld);
        }
    }

    #[test]
    fn test_expr_ipld() {
        let test = |src| {
            let mut store1 = Store::<Fr>::default();
            let expr1 = store1.read(src).unwrap();
            store1.hydrate_scalar_cache();

            if let (scalar_store, Some(scalar_expr)) = ScalarStore::new_with_expr(&store1, &expr1) {
                let ipld = to_ipld(scalar_store.clone()).unwrap();
                let mut scalar_store2 = from_ipld(ipld).unwrap();
                assert_eq!(scalar_store, scalar_store2);
                if let Some((mut store2, expr2)) = scalar_store2.to_store_with_expr(&scalar_expr) {
                    store2.hydrate_scalar_cache();
                    let (scalar_store3, _) = ScalarStore::new_with_expr(&store2, &expr2);
                    assert_eq!(scalar_store2, scalar_store3)
                } else {
                    panic!()
                }
            } else {
                panic!()
            }
        };

        test("symbol");
        test("1");
        test("(1 . 2)");
        test("(1 2)");
        test("\"foo\" . \"bar\")");
        test("(foo . bar)");

        test("(1 . 2)");
        test("(+ 1 2 3)");
        test("(+ 1 2 (* 3 4))");

        test("(+ 1 2 (* 3 4) \"asdf\" )");
        test("(+ 1 2 2 (* 3 4) \"asdf\" \"asdf\")");
    }

    #[test]
    fn test_expr_eval_ipld() {
        use crate::eval;
        let test = |src| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            let env = empty_sym_env(&s);
            let mut eval = eval::Evaluator::new(expr, env, &mut s, 100);
            let (
                eval::IO {
                    expr,
                    env: _,
                    cont: _,
                },
                _lim,
                _emitted,
            ) = eval.eval().unwrap();

            let (scalar_store, _) = ScalarStore::new_with_expr(&s, &expr);
            println!("{scalar_store:?}");
            let ipld = to_ipld(scalar_store.clone()).unwrap();
            let scalar_store2 = from_ipld(ipld).unwrap();
            println!("{scalar_store2:?}");
            assert_eq!(scalar_store, scalar_store2);
        };

        test("(let ((a 123)) (lambda (x) (+ x a)))");
    }

    #[test]
    fn test_scalar_store() {
        let test = |src, expected| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            let (scalar_store, _) = ScalarStore::new_with_expr(&s, &expr);
            assert_eq!(expected, scalar_store.scalar_map.len());
        };

        // Four atoms, four conses (four-element list), and NIL.
        test("symbol", 1);
        test("(1 . 2)", 3);
        test("(+ 1 2 3)", 9);
        test("(+ 1 2 (* 3 4))", 14);
        // String are handled.
        test("(+ 1 2 (* 3 4) \"asdf\" )", 16);
        // Duplicate strings or symbols appear only once.
        test("(+ 1 2 2 (* 3 4) \"asdf\" \"asdf\")", 18);
    }

    #[test]
    fn test_scalar_store_opaque_cons() {
        let mut store = Store::<Fr>::default();

        let num1 = store.num(123);
        let num2 = store.num(987);
        let cons = store.intern_cons(num1, num2);
        let cons_hash = store.hash_expr(&cons).unwrap();
        let opaque_cons = store.intern_maybe_opaque_cons(*cons_hash.value());

        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_expr(&store, &opaque_cons);
        println!("{:?}", scalar_store.scalar_map);
        println!("{:?}", scalar_store.scalar_map.len());
        // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
        assert_eq!(3, scalar_store.scalar_map.len());
    }

    #[test]
    fn test_scalar_store_opaque_fun() {
        let mut store = Store::<Fr>::default();

        let arg = store.sym("A");
        let body = store.num(123);
        let empty_env = empty_sym_env(&store);
        let fun = store.intern_fun(arg, body, empty_env);
        let fun_hash = store.hash_expr(&fun).unwrap();
        let opaque_fun = store.intern_maybe_opaque_fun(*fun_hash.value());
        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_expr(&store, &opaque_fun);
        // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
        assert_eq!(4, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_sym() {
        let mut store = Store::<Fr>::default();

        let sym = store.sym("sym");
        let sym_hash = store.hash_expr(&sym).unwrap();
        let opaque_sym = store.intern_maybe_opaque_sym(*sym_hash.value());

        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_expr(&store, &opaque_sym);
        // Only the symbol's string itself, not all of its substrings, appears in `ScalarStore`.
        assert_eq!(1, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_str() {
        let mut store = Store::<Fr>::default();

        let str = store.str("str");
        let str_hash = store.hash_expr(&str).unwrap();
        let opaque_str = store.intern_maybe_opaque_sym(*str_hash.value());

        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_expr(&store, &opaque_str);
        // Only the string itself, not all of its substrings, appears in `ScalarStore`.
        assert_eq!(1, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_comm() {
        let mut store = Store::<Fr>::default();

        let num = store.num(987);
        let comm = store.intern_comm(Fr::from(123), num);
        let comm_hash = store.hash_expr(&comm).unwrap();
        let opaque_comm = store.intern_maybe_opaque_comm(*comm_hash.value());

        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_expr(&store, &opaque_comm);
        println!("{:?}", scalar_store.scalar_map);
        println!("{:?}", scalar_store.scalar_map.len());
        // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
        assert_eq!(2, scalar_store.scalar_map.len());
    }
}
