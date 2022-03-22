use std::collections::HashMap;

use ff::PrimeField;

use crate::num::Num;
use crate::store::{Op1, Op2, Pointer, Ptr, Rel2, ScalarContPtr, ScalarPtr, Store, Tag};

#[derive(Default)]
pub struct ScalarStore<F: PrimeField> {
    scalar_map: HashMap<ScalarPtr<F>, ScalarExpression<F>>,
    pending_scalar_ptrs: Vec<ScalarPtr<F>>,
}

impl<'a, F: PrimeField> ScalarStore<F> {
    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> Self {
        let mut new = Self::default();
        new.add_one_ptr(store, expr);
        new
    }

    pub fn add_one_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) {
        self.add_ptr(store, expr);
        self.finalize(store);
    }

    pub fn add_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) {
        if let Some(scalar_ptr) = store.get_expr_hash(expr) {
            self.add(store, expr, scalar_ptr);
        };
    }

    // NOTE: This requires that the scalar_cache has been hydrated.
    fn add_scalar_ptr(&mut self, store: &Store<F>, scalar_ptr: ScalarPtr<F>) {
        if let Some(ptr) = store.scalar_ptr_map.get(&scalar_ptr) {
            self.add(store, &*ptr, scalar_ptr);
        }
    }

    fn add(&mut self, store: &Store<F>, ptr: &Ptr<F>, scalar_ptr: ScalarPtr<F>) {
        let mut new_pending_scalar_ptrs: Vec<ScalarPtr<F>> = Default::default();

        self.scalar_map.entry(scalar_ptr).or_insert_with(|| {
            let scalar_expression =
                ScalarExpression::from_ptr(store, ptr).expect("ScalarExpression missing for ptr");
            if let Some(more_scalar_ptrs) = Self::child_scalar_ptrs(&scalar_expression) {
                new_pending_scalar_ptrs.extend(more_scalar_ptrs);
            };
            scalar_expression
        });

        self.pending_scalar_ptrs.extend(new_pending_scalar_ptrs);
    }

    fn child_scalar_ptrs(scalar_expression: &ScalarExpression<F>) -> Option<Vec<ScalarPtr<F>>> {
        match scalar_expression {
            ScalarExpression::Nil => None,
            ScalarExpression::Cons(car, cdr) => Some(vec![*car, *cdr]),
            ScalarExpression::Sym(_str) => None,
            ScalarExpression::Fun {
                arg,
                body,
                closed_env,
            } => Some(vec![*arg, *body, *closed_env]),
            ScalarExpression::Num(_) => None,
            ScalarExpression::Str(_) => None,
            ScalarExpression::Thunk(_) => None,
            ScalarExpression::OpaqueCons
            | ScalarExpression::OpaqueFun
            | ScalarExpression::OpaqueSym
            | ScalarExpression::OpaqueStr => None,
        }
    }

    fn add_pending_scalar_ptrs(&mut self, store: &Store<F>) {
        while let Some(scalar_ptr) = self.pending_scalar_ptrs.pop() {
            self.add_scalar_ptr(store, scalar_ptr);
        }
        assert!(self.pending_scalar_ptrs.is_empty());
    }

    fn finalize(&mut self, store: &Store<F>) {
        self.add_pending_scalar_ptrs(store);
    }
}

impl<'a, F: PrimeField> ScalarExpression<F> {
    fn from_ptr(store: &Store<F>, ptr: &Ptr<F>) -> Option<Self> {
        match ptr.tag() {
            Tag::Nil => Some(ScalarExpression::Nil),
            Tag::Cons => store
                .fetch_cons(ptr)
                .and_then(|(car, cdr)| {
                    store.get_expr_hash(car).and_then(|car| {
                        store
                            .get_expr_hash(cdr)
                            .map(|cdr| ScalarExpression::Cons(car, cdr))
                    })
                })
                .or(Some(ScalarExpression::OpaqueCons)),
            Tag::Sym => store
                .fetch_sym(ptr)
                .map(|str| ScalarExpression::Sym(str.into()))
                .or(Some(ScalarExpression::OpaqueSym)),
            Tag::Fun => store
                .fetch_fun(ptr)
                .and_then(|(arg, body, closed_env)| {
                    store.get_expr_hash(arg).and_then(|arg| {
                        store.get_expr_hash(body).and_then(|body| {
                            store.get_expr_hash(closed_env).map(|closed_env| {
                                ScalarExpression::Fun {
                                    arg,
                                    body,
                                    closed_env,
                                }
                            })
                        })
                    })
                })
                .or(Some(ScalarExpression::OpaqueFun)),
            Tag::Num => store.fetch_num(ptr).map(|num| ScalarExpression::Num(*num)),
            Tag::Str => store
                .fetch_str(ptr)
                .map(|str| ScalarExpression::Str(str.into()))
                .or(Some(ScalarExpression::OpaqueSym)),

            Tag::Thunk => unimplemented!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarExpression<F: PrimeField> {
    Nil,
    Cons(ScalarPtr<F>, ScalarPtr<F>),
    Sym(String),
    Fun {
        arg: ScalarPtr<F>,
        body: ScalarPtr<F>,
        closed_env: ScalarPtr<F>,
    },
    Num(Num<F>),
    Str(String),
    Thunk(ScalarThunk<F>),
    OpaqueCons,
    OpaqueFun,
    OpaqueSym,
    OpaqueStr,
}

impl<'a, F: PrimeField> Default for ScalarExpression<F> {
    fn default() -> Self {
        Self::Nil
    }
}

// Unused for now, but will be needed when we serialize Thunks to IPLD.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScalarThunk<F: PrimeField> {
    pub(crate) value: ScalarPtr<F>,
    pub(crate) continuation: ScalarContPtr<F>,
}

// Unused for now, but will be needed when we serialize Continuations to IPLD.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ScalarContinuation<F: PrimeField> {
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
    Relop {
        operator: Rel2,
        saved_env: ScalarPtr<F>,
        unevaled_args: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Relop2 {
        operator: Rel2,
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
        saved_env: ScalarPtr<F>,
        body: ScalarPtr<F>,
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
    use crate::store::ScalarPointer;
    use blstrs::Scalar as Fr;

    #[test]
    fn test_scalar_store() {
        let test = |src, expected| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            let scalar_store = ScalarStore::new_with_expr(&s, &expr);
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
        let opaque_cons = store.intern_opaque_cons(*cons_hash.value());

        store.hydrate_scalar_cache();

        let scalar_store = ScalarStore::new_with_expr(&store, &opaque_cons);

        assert_eq!(1, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_fun() {
        let mut store = Store::<Fr>::default();

        let arg = store.sym("A");
        let body = store.num(123);
        let empty_env = empty_sym_env(&store);
        let fun = store.intern_fun(arg, body, empty_env);
        let fun_hash = store.hash_expr(&fun).unwrap();
        let opaque_fun = store.intern_opaque_fun(*fun_hash.value());
        store.hydrate_scalar_cache();

        let scalar_store = ScalarStore::new_with_expr(&store, &opaque_fun);

        assert_eq!(1, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_sym() {
        let mut store = Store::<Fr>::default();

        let sym = store.sym(&"sym");
        let sym_hash = store.hash_expr(&sym).unwrap();
        let opaque_sym = store.intern_opaque_sym(*sym_hash.value());

        store.hydrate_scalar_cache();

        let scalar_store = ScalarStore::new_with_expr(&store, &opaque_sym);

        assert_eq!(1, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_str() {
        let mut store = Store::<Fr>::default();

        let str = store.str(&"str");
        let str_hash = store.hash_expr(&str).unwrap();
        let opaque_str = store.intern_opaque_sym(*str_hash.value());

        store.hydrate_scalar_cache();

        let scalar_store = ScalarStore::new_with_expr(&store, &opaque_str);

        assert_eq!(1, scalar_store.scalar_map.len());
    }
}
