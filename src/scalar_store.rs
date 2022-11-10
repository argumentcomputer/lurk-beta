use std::collections::BTreeMap;
use std::fmt;

use crate::field::LurkField;

use crate::store::{Op1, Op2, Ptr, ScalarContPtr, ScalarPointer, ScalarPtr, Store, Tag};
use serde::Deserialize;
use serde::Serialize;

/// `ScalarStore` allows realization of a graph of `ScalarPtr`s suitable for serialization to IPLD. `ScalarExpression`s
/// are composed only of `ScalarPtr`s, so `scalar_map` suffices to allow traverseing an arbitrary DAG.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScalarStore<F: LurkField> {
    scalar_map: BTreeMap<ScalarPtr<F>, Option<ScalarExpression<F>>>,
    scalar_cont_map: BTreeMap<ScalarContPtr<F>, Option<ScalarContinuation<F>>>,
}

impl<'a, F: LurkField> fmt::Display for ScalarStore<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        for (k, v) in self.scalar_map.iter() {
            if let Some(v) = v {
                writeln!(f, "  {}: {},", k, v)?;
            } else {
                writeln!(f, "  {}: _,", k)?;
            }
        }
        for (k, v) in self.scalar_cont_map.iter() {
            if let Some(v) = v {
                writeln!(f, "  {:?}: {:?},", k, v)?;
            } else {
                writeln!(f, "  {:?}: _,", k)?;
            }
        }
        writeln!(f, "}}")?;
        Ok(())
    }
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
                let scalar_expr = store.get_scalar_expr(&scalar)?;
                scalars.extend(Self::child_scalar_ptrs(&scalar_expr));
                Some(scalar_expr)
            });
        }

        Some((scalar_store, root_scalar))
    }

    /// All the `ScalarPtr`s directly reachable from `scalar_expression`, if any.
    fn child_scalar_ptrs(scalar_expression: &ScalarExpression<F>) -> Vec<ScalarPtr<F>> {
        match scalar_expression {
            ScalarExpression::StrNil => vec![],
            ScalarExpression::Cons(car, cdr) => vec![*car, *cdr],
            ScalarExpression::Comm(_, payload) => vec![*payload],
            ScalarExpression::Sym(string) => vec![*string],
            ScalarExpression::Fun(arg, body, closed_env) => vec![*arg, *body, *closed_env],
            ScalarExpression::Num(_) => vec![],
            ScalarExpression::StrCons(head, tail) => vec![*head, *tail],
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

    pub fn to_store_with_expr(&self, ptr: &ScalarPtr<F>) -> Option<(Store<F>, Ptr<F>)> {
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
    pub fn get_str_tails(&self, ptr: ScalarPtr<F>) -> Option<Vec<(char, ScalarPtr<F>)>> {
        let mut vec = Vec::new();
        let mut ptr = ptr;
        while ptr != ScalarPtr::from_parts(Tag::Str.as_field(), F::zero()) {
            //println!("str_tails ptr {}", ptr);
            let (head, tail) = self.scalar_map.get(&ptr).and_then(|x| match x {
                Some(ScalarExpression::StrCons(head, tail)) => Some((head, tail)),
                _ => None,
            })?;
            let chr = self.scalar_map.get(&head).and_then(|x| match x {
                Some(ScalarExpression::Char(f)) => f.to_char(),
                _ => None,
            })?;
            vec.push((chr, *tail));
            ptr = *tail;
        }
        Some(vec)
    }
    pub fn get_str(&self, ptr: ScalarPtr<F>) -> Option<String> {
        let s: String = self
            .get_str_tails(ptr)?
            .into_iter()
            .map(|(x, _)| x)
            .collect();
        Some(s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ScalarExpression<F: LurkField> {
    Cons(ScalarPtr<F>, ScalarPtr<F>),
    Comm(F, ScalarPtr<F>),
    Sym(ScalarPtr<F>),
    Fun(ScalarPtr<F>, ScalarPtr<F>, ScalarPtr<F>),
    Num(F),
    StrCons(ScalarPtr<F>, ScalarPtr<F>),
    StrNil,
    Thunk(ScalarThunk<F>),
    Char(F),
    UInt(F),
}

impl<'a, F: LurkField> fmt::Display for ScalarExpression<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cons(x, y) => write!(f, "Cons({}, {})", x, y),
            Self::Comm(x, y) => write!(f, "Comm({:?}, {})", x, y),
            Self::Sym(x) => write!(f, "Sym({})", x),
            Self::Fun(x, y, z) => write!(f, "Fun({}, {}, {})", x, y, z),
            Self::Num(x) => {
                if let Some(x) = x.to_u64() {
                    write!(f, "Num({})", x)
                } else {
                    write!(f, "Num({:?})", x)
                }
            }
            Self::UInt(x) => {
                if let Some(x) = x.to_u64() {
                    write!(f, "UInt({})", x)
                } else {
                    write!(f, "UInt({:?})", x)
                }
            }
            Self::Char(x) => {
                if let Some(x) = x.to_char() {
                    write!(f, "Char('{}')", x)
                } else {
                    write!(f, "Char({:?})", x)
                }
            }
            Self::StrCons(x, y) => write!(f, "StrCons({}, {})", x, y),
            Self::StrNil => write!(f, "StrNil"),
            Self::Thunk(x) => write!(f, "Thunk({:?})", x),
        }
    }
}

impl<'a, F: LurkField> Default for ScalarExpression<F> {
    fn default() -> Self {
        Self::Num(F::zero())
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
                (100, Box::new(|_| Self::StrNil)),
                (
                    100,
                    Box::new(|g| Self::Cons(ScalarPtr::arbitrary(g), ScalarPtr::arbitrary(g))),
                ),
                (100, Box::new(|g| Self::Sym(ScalarPtr::arbitrary(g)))),
                (
                    100,
                    Box::new(|g| Self::StrCons(ScalarPtr::arbitrary(g), ScalarPtr::arbitrary(g))),
                ),
                (
                    100,
                    Box::new(|g| {
                        let f = FWrap::arbitrary(g);
                        Self::Num(f.0)
                    }),
                ),
                (
                    100,
                    Box::new(|g| {
                        Self::Fun(
                            ScalarPtr::arbitrary(g),
                            ScalarPtr::arbitrary(g),
                            ScalarPtr::arbitrary(g),
                        )
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

    #[quickcheck]
    fn prop_scalar_expression_ipld(x: ScalarExpression<Fr>) -> bool {
        match to_ipld(x.clone()) {
            Ok(ipld) => match from_ipld(ipld.clone()) {
                Ok(y) => {
                    println!("x: {:?}", x);
                    println!("y: {:?}", y);
                    x == y
                }
                Err(e) => {
                    println!("ser x: {:?}", x);
                    println!("de ipld: {:?}", ipld);
                    println!("err e: {:?}", e);
                    false
                }
            },
            Err(e) => {
                println!("ser x: {:?}", x);
                println!("err e: {:?}", e);
                false
            }
        }
    }

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
    fn units_scalar_store_conversion() {
        let test = |src| {
            let mut store1 = Store::<Fr>::default();
            let expr1 = store1.read(src).unwrap();
            store1.hydrate_scalar_cache();
            let (scalar_store1, scalar_expr1) = ScalarStore::new_with_expr(&store1, &expr1)?;
            println!("{}", scalar_store1);
            println!("{}", scalar_expr1);
            let (mut store2, expr2) =
                ScalarStore::to_store_with_expr(&scalar_store1, &scalar_expr1)?;
            store2.hydrate_scalar_cache();
            //println!("{:?}", store2);
            //println!("{:?}", expr2);
            let (scalar_store2, scalar_expr2) = ScalarStore::new_with_expr(&store2, &expr2)?;
            println!("{}", scalar_store2);
            println!("{}", scalar_expr2);
            Some(scalar_store1 == scalar_store2 && scalar_expr1 == scalar_expr2)
        };
        let test = |src| test(src) == Some(true);

        assert!(test("1"));
        assert!(test("\"s\""));
        assert!(test("symbol"));
        assert!(test("#\\a#"));
        assert!(test("(1 . 2)"));
        assert!(test("(\"foo\" . \"bar\")"));
        assert!(test("(foo . bar)"));
        assert!(test("(1 . 2)"));
        assert!(test("(+ 1 2 3)"));
        assert!(test("(+ 1 2 (* 3 4))"));
        assert!(test("(+ 1 2 (* 3 4) \"asdf\" )"));
        assert!(test("(+ 1 2 2 (* 3 4) \"asdf\" \"asdf\")"));
    }

    #[test]
    fn test_expr_ipld() {
        let test = |src| {
            let mut store1 = Store::<Fr>::default();
            let expr1 = store1.read(src).unwrap();
            store1.hydrate_scalar_cache();

            if let Some((scalar_store, scalar_expr)) = ScalarStore::new_with_expr(&store1, &expr1) {
                let ipld = to_ipld(scalar_store.clone()).unwrap();
                let scalar_store2 = from_ipld(ipld).unwrap();
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
    fn units_scalar_store() {
        let test = |src, expected| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&s, &expr) {
                println!("{}", scalar_store);
                assert_eq!(expected, scalar_store.scalar_map.len());
            } else {
                assert!(false);
            }
        };

        // Four atoms, four conses (four-element list), and NIL.
        test("symbol", 14);
        test("(1 . 2)", 3);
        test("(\"foo\" . \"bar\")", 13);
        test("(foo . bar)", 15);
        test("(+ 1 2 3)", 18);
        test("(+ 1 2 (* 3 4))", 25);
        // String are handled.
        test("(+ 1 2 (* 3 4) \"asdf\" )", 34);
        // Duplicate strings or symbols appear only once.
        test("(+ 1 2 2 (* 3 4) \"asdf\" \"asdf\")", 36);
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
            println!("{}", scalar_store);
            println!("{:?}", scalar_store.scalar_map.len());
            // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
            assert_eq!(13, scalar_store.scalar_map.len());
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_scalar_store_opaque_sym() {
        let mut store = Store::<Fr>::default();

        let sym = store.sym(&"sym");
        let sym_hash = store.hash_expr(&sym).unwrap();
        // need a blank store since hash_expr fills the string tails
        let mut store = Store::<Fr>::default();
        let opaque_sym = store.intern_maybe_opaque_sym(*sym_hash.value());

        store.hydrate_scalar_cache();

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_sym) {
            println!("{}", scalar_store);
            println!("{}", scalar_store.scalar_map.len());
            // Only the symbol's string itself, not all of its substrings, appears in `ScalarStore`.
            assert_eq!(1, scalar_store.scalar_map.len());
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_scalar_store_opaque_str() {
        let mut store = Store::<Fr>::default();

        let str = store.str(&"str");
        let str_hash = store.hash_expr(&str).unwrap();
        // need a blank store since hash_expr fills the string tails
        let mut store = Store::<Fr>::default();
        let opaque_str = store.intern_maybe_opaque_sym(*str_hash.value());

        store.hydrate_scalar_cache();

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_str) {
            println!("{:?}", scalar_store.scalar_map);
            println!("{:?}", scalar_store.scalar_map.len());
            // Only the symbol's string itself, not all of its substrings, appears in `ScalarStore`.
            assert_eq!(1, scalar_store.scalar_map.len());
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_scalar_store_opaque_comm() {
        let mut store = Store::<Fr>::default();

        let num = store.num(987);
        let comm = store.intern_comm(Fr::from(123), num);
        let comm_hash = store.hash_expr(&comm).unwrap();
        let opaque_comm = store.intern_maybe_opaque_comm(*comm_hash.value());

        store.hydrate_scalar_cache();

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_comm) {
            println!("{}", scalar_store);
            println!("{:?}", scalar_store.scalar_map.len());
        } else {
            assert!(false);
        }
    }
}
