use std::collections::BTreeMap;

use crate::field::LurkField;

use crate::store::{Op1, Op2, Pointer, Ptr, ScalarContPtr, ScalarPtr, Store, Tag};
use crate::{Num, UInt};
use serde::Deserialize;
use serde::Serialize;

/// `ScalarStore` allows realization of a graph of `ScalarPtr`s suitable for serialization to IPLD. `ScalarExpression`s
/// are composed only of `ScalarPtr`s, so `scalar_map` suffices to allow traverseing an arbitrary DAG.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScalarStore<F: LurkField> {
    scalar_map: BTreeMap<ScalarPtr<F>, Option<ScalarExpression<F>>>,
    scalar_cont_map: BTreeMap<ScalarContPtr<F>, Option<ScalarContinuation<F>>>,
}

impl<'a, F: LurkField> ScalarStore<F> {
    /// NOTE: This requires that `store.scalar_cache` has been hydrated.
    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> Option<(Self, ScalarPtr<F>)> {
        let mut scalar_store = Self::default();
        let mut scalars = Vec::new();

        let root_scalar = store.get_expr_hash(expr)?;

        scalars.push(root_scalar);

        while let Some(scalar) = scalars.pop() {
            scalar_store.scalar_map.entry(scalar).or_insert_with(|| {
                let ptr = store.scalar_ptr_map.get(&scalar)?;
                let scalar_expr = store.get_scalar_expr(&ptr)?;
                scalars.extend(Self::child_scalar_ptrs(&scalar_expr));
                Some(scalar_expr)
            });
        }

        Some((scalar_store, root_scalar))
    }

    /// All the `ScalarPtr`s directly reachable from `scalar_expression`, if any.
    fn child_scalar_ptrs(scalar_expression: &ScalarExpression<F>) -> Vec<ScalarPtr<F>> {
        match scalar_expression {
            ScalarExpression::Nil => vec![],
            ScalarExpression::Cons(car, cdr) => vec![*car, *cdr],
            ScalarExpression::Comm(_, payload) => vec![*payload],
            ScalarExpression::Sym(_str) => vec![],
            ScalarExpression::Fun {
                arg,
                body,
                closed_env,
            } => vec![*arg, *body, *closed_env],
            ScalarExpression::Num(_) => vec![],
            ScalarExpression::Str(_) => vec![],
            ScalarExpression::Thunk(_) => vec![],
            ScalarExpression::Char(_) => vec![],
            ScalarExpression::UInt(_) => vec![],
        }
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
        let mut store = Store::new();

        let ptr = store.intern_scalar_ptr(*ptr, self)?;

        for scalar_ptr in self.scalar_map.keys() {
            store.intern_scalar_ptr(*scalar_ptr, self);
        }
        for ptr in self.scalar_cont_map.keys() {
            store.intern_scalar_cont_ptr(*ptr, self);
        }
        Some((store, ptr))
    }

    pub fn to_store(&mut self) -> Store<F> {
        let mut store = Store::new();

        for ptr in self.scalar_map.keys() {
            store.intern_scalar_ptr(*ptr, self);
        }
        for ptr in self.scalar_cont_map.keys() {
            store.intern_scalar_cont_ptr(*ptr, self);
        }
        store
    }
}

//impl<'a, F: LurkField> ScalarExpression<F> {
//}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ScalarExpression<F: LurkField> {
    Nil,
    Cons(ScalarPtr<F>, ScalarPtr<F>),
    Comm(F, ScalarPtr<F>),
    Sym(String),
    Fun {
        arg: ScalarPtr<F>,
        body: ScalarPtr<F>,
        closed_env: ScalarPtr<F>,
    },
    Num(F),
    Str(String),
    Thunk(ScalarThunk<F>),
    Char(char),
    UInt(UInt),
}

impl<'a, F: LurkField> Default for ScalarExpression<F> {
    fn default() -> Self {
        Self::Nil
    }
}

// Unused for now, but will be needed when we serialize Thunks to IPLD.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScalarThunk<F: LurkField> {
    pub(crate) value: ScalarPtr<F>,
    pub(crate) continuation: ScalarContPtr<F>,
}

impl<F: LurkField> Copy for ScalarThunk<F> {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
    use crate::field::FWrap;
    use crate::store::ScalarPointer;
    use blstrs::Scalar as Fr;

    use quickcheck::{Arbitrary, Gen};

    use crate::test::frequency;

    use libipld::serde::from_ipld;
    use libipld::serde::to_ipld;

    impl Arbitrary for ScalarThunk<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            ScalarThunk {
                value: Arbitrary::arbitrary(g),
                continuation: Arbitrary::arbitrary(g),
            }
        }
    }

    //#[quickcheck]
    //fn prop_scalar_thunk_ipld(x: ScalarThunk<Fr>) -> bool {
    //    if let Ok(ipld) = to_ipld(x) {
    //        if let Ok(y) = from_ipld(ipld) {
    //            x == y
    //        } else {
    //            false
    //        }
    //    } else {
    //        false
    //    }
    //}

    impl Arbitrary for ScalarExpression<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> ScalarExpression<Fr>>)> = vec![
                (100, Box::new(|_| Self::Nil)),
                (
                    100,
                    Box::new(|g| Self::Cons(ScalarPtr::arbitrary(g), ScalarPtr::arbitrary(g))),
                ),
                (100, Box::new(|g| Self::Sym(String::arbitrary(g)))),
                (100, Box::new(|g| Self::Str(String::arbitrary(g)))),
                (
                    100,
                    Box::new(|g| {
                        let f = FWrap::arbitrary(g);
                        Self::Num(f.0)
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Fun {
                        arg: ScalarPtr::arbitrary(g),
                        body: ScalarPtr::arbitrary(g),
                        closed_env: ScalarPtr::arbitrary(g),
                    }),
                ),
                (100, Box::new(|g| Self::Thunk(ScalarThunk::arbitrary(g)))),
            ];
            frequency(g, input)
        }
    }

    impl Arbitrary for ScalarContinuation<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> ScalarContinuation<Fr>>)> = vec![
                (100, Box::new(|_| Self::Outermost)),
                (
                    100,
                    Box::new(|g| Self::Call {
                        unevaled_arg: ScalarPtr::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Call2 {
                        function: ScalarPtr::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Tail {
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (100, Box::new(|_| Self::Error)),
                (
                    100,
                    Box::new(|g| Self::Lookup {
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Unop {
                        operator: Op1::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Binop {
                        operator: Op2::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        unevaled_args: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Binop2 {
                        operator: Op2::arbitrary(g),
                        evaled_arg: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::If {
                        unevaled_args: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Let {
                        var: ScalarPtr::arbitrary(g),
                        body: ScalarPtr::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::LetRec {
                        var: ScalarPtr::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        body: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (100, Box::new(|_| Self::Dummy)),
                (100, Box::new(|_| Self::Terminal)),
            ];
            frequency(g, input)
        }
    }

    //#[quickcheck]
    //fn prop_scalar_expression_ipld(x: ScalarExpression<Fr>) -> bool {
    //    match to_ipld(x.clone()) {
    //        Ok(ipld) => match from_ipld(ipld.clone()) {
    //            Ok(y) => {
    //                println!("x: {:?}", x);
    //                println!("y: {:?}", y);
    //                x == y
    //            }
    //            Err(e) => {
    //                println!("ser x: {:?}", x);
    //                println!("de ipld: {:?}", ipld);
    //                println!("err e: {:?}", e);
    //                false
    //            }
    //        },
    //        Err(e) => {
    //            println!("ser x: {:?}", x);
    //            println!("err e: {:?}", e);
    //            false
    //        }
    //    }
    //}

    #[quickcheck]
    fn prop_scalar_continuation_ipld(x: ScalarExpression<Fr>) -> bool {
        if let Ok(ipld) = to_ipld(x.clone()) {
            if let Ok(y) = from_ipld(ipld) {
                x == y
            } else {
                false
            }
        } else {
            false
        }
    }

    // This doesn't create well-defined ScalarStores, so is only useful for
    // testing ipld
    impl Arbitrary for ScalarStore<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            let map: Vec<(ScalarPtr<Fr>, Option<ScalarExpression<Fr>>)> = Arbitrary::arbitrary(g);
            let cont_map: Vec<(ScalarContPtr<Fr>, Option<ScalarContinuation<Fr>>)> =
                Arbitrary::arbitrary(g);
            ScalarStore {
                scalar_map: map.into_iter().collect(),
                scalar_cont_map: cont_map.into_iter().collect(),
            }
        }
    }

    #[quickcheck]
    fn prop_scalar_store_ipld(x: ScalarStore<Fr>) -> bool {
        if let Ok(ipld) = to_ipld(x.clone()) {
            if let Ok(y) = from_ipld(ipld) {
                x == y
            } else {
                false
            }
        } else {
            false
        }
    }

    #[test]
    fn test_expr_ipld() {
        let test = |src| {
            let mut store1 = Store::<Fr>::default();
            let expr1 = store1.read(src).unwrap();
            store1.hydrate_scalar_cache();

            if let Some((scalar_store, scalar_expr)) = ScalarStore::new_with_expr(&store1, &expr1) {
                let ipld = to_ipld(scalar_store.clone()).unwrap();
                let mut scalar_store2 = from_ipld(ipld).unwrap();
                assert_eq!(scalar_store, scalar_store2);
                println!("{:?}", scalar_store2);
                if let Some((mut store2, expr2)) = scalar_store2.to_store_with_expr(&scalar_expr) {
                    store2.hydrate_scalar_cache();
                    //println!("{:?}", store2);
                    println!("{:?}", expr2);
                    if let Some((scalar_store3, _)) = ScalarStore::new_with_expr(&store2, &expr2) {
                        println!("{:?}", scalar_store2);
                        println!("{:?}", scalar_store3);
                        assert_eq!(scalar_store2, scalar_store3)
                    } else {
                        //   println!("{:?}", expr2);
                        //println!("{:?}", store2);
                        assert!(false)
                    }
                } else {
                    assert!(false)
                }
            } else {
                assert!(false)
            }
        };

        //test("symbol");
        //test("1");
        test("#\\a#");
        //test("(1 . 2)");
        //test("(\"foo\" . \"bar\")");
        //test("(foo . bar)");
        //test("(1 . 2)");
        //test("(+ 1 2 3)");
        //test("(+ 1 2 (* 3 4))");
        //test("(+ 1 2 (* 3 4) \"asdf\" )");
        //test("(+ 1 2 2 (* 3 4) \"asdf\" \"asdf\")");
    }

    //#[test]
    //fn test_expr_eval_ipld() {
    //    use crate::eval;
    //    let test = |src| {
    //        let mut s = Store::<Fr>::default();
    //        let expr = s.read(src).unwrap();
    //        s.hydrate_scalar_cache();

    //        let env = empty_sym_env(&s);
    //        let mut eval = eval::Evaluator::new(expr, env, &mut s, 100);
    //        let (
    //            eval::IO {
    //                expr,
    //                env: _,
    //                cont: _,
    //            },
    //            _lim,
    //            _emitted,
    //        ) = eval.eval().unwrap();

    //        match ScalarStore::new_with_expr(&s, &expr) {
    //            Ok((scalar_store, _)) => {
    //                println!("{:?}", scalar_store);
    //                let ipld = to_ipld(scalar_store.clone()).unwrap();
    //                let scalar_store2 = from_ipld(ipld).unwrap();
    //                println!("{:?}", scalar_store2);
    //                assert_eq!(scalar_store, scalar_store2);
    //            }
    //            Err(e) => {
    //                println!("{:?}", e);
    //                assert!(false);
    //            }
    //        }
    //    };

    //    test("(let ((a 123)) (lambda (x) (+ x a)))");
    //}

    #[test]
    fn test_scalar_store() {
        let test = |src, expected| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&s, &expr) {
                println!("{:?}", scalar_store);
                assert_eq!(expected, scalar_store.scalar_map.len());
            } else {
                assert!(false);
            }
        };

        // Four atoms, four conses (four-element list), and NIL.
        test("symbol", 1);
        test("(1 . 2)", 3);
        test("(\"foo\" . \"bar\")", 3);
        test("(foo . bar)", 3);
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

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_cons) {
            println!("{:?}", scalar_store.scalar_map);
            println!("{:?}", scalar_store.scalar_map.len());
            // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
            assert_eq!(3, scalar_store.scalar_map.len());
        } else {
            assert!(false);
        }
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

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_fun) {
            println!("{:?}", scalar_store.scalar_map);
            println!("{:?}", scalar_store.scalar_map.len());
            // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
            assert_eq!(4, scalar_store.scalar_map.len());
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_scalar_store_opaque_sym() {
        let mut store = Store::<Fr>::default();

        let sym = store.sym(&"sym");
        let sym_hash = store.hash_expr(&sym).unwrap();
        let opaque_sym = store.intern_maybe_opaque_sym(*sym_hash.value());

        store.hydrate_scalar_cache();

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_sym) {
            println!("{:?}", scalar_store.scalar_map);
            println!("{:?}", scalar_store.scalar_map.len());
            // Only the symbol's string itself, not all of its substrings, appears in `ScalarStore`.
            assert_eq!(1, scalar_store.scalar_map.len());
        } else {
            assert!(false);
        }
    }

    //#[test]
    //fn test_scalar_store_opaque_str() {
    //    let mut store = Store::<Fr>::default();

    //    let str = store.str(&"str");
    //    let str_hash = store.hash_expr(&str).unwrap();
    //    let opaque_str = store.intern_maybe_opaque_sym(*str_hash.value());

    //    store.hydrate_scalar_cache();

    //    match ScalarStore::new_with_expr(&store, &opaque_str) {
    //        Ok((scalar_store, _)) => {
    //            println!("{:?}", scalar_store.scalar_map);
    //            println!("{:?}", scalar_store.scalar_map.len());
    //            // Only the symbol's string itself, not all of its substrings, appears in `ScalarStore`.
    //            assert_eq!(1, scalar_store.scalar_map.len());
    //        }
    //        Err(e) => {
    //            println!("{:?}", e);
    //            assert!(false);
    //        }
    //    }
    //}

    #[test]
    fn test_scalar_store_opaque_comm() {
        let mut store = Store::<Fr>::default();

        let num = store.num(987);
        let comm = store.intern_comm(Fr::from(123), num);
        let comm_hash = store.hash_expr(&comm).unwrap();
        let opaque_comm = store.intern_maybe_opaque_comm(*comm_hash.value());

        store.hydrate_scalar_cache();

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_comm) {
            println!("{:?}", scalar_store.scalar_map);
            println!("{:?}", scalar_store.scalar_map.len());
        } else {
            assert!(false);
        }
    }
}
