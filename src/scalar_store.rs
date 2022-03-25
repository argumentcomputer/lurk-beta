use std::collections::BTreeMap;

use ff::PrimeField;

use crate::field::LurkField;
use libipld::Cid;
use libipld::Ipld;

use crate::ipld;
use crate::ipld::IpldEmbed;
use crate::ipld::IpldError;
use crate::store::{Op1, Op2, Pointer, Ptr, Rel2, ScalarContPtr, ScalarPtr, Store, Tag};
use crate::Num;

/// `ScalarStore` allows realization of a graph of `ScalarPtr`s suitable for serialization to IPLD. `ScalarExpression`s
/// are composed only of `ScalarPtr`s, so `scalar_map` suffices to allow traverseing an arbitrary DAG.
#[derive(Default)]
pub struct ScalarStore<F: LurkField> {
    scalar_map: BTreeMap<ScalarPtr<F>, ScalarExpression<F>>,
    pending_scalar_ptrs: Vec<ScalarPtr<F>>,
}

impl<'a, F: LurkField> ScalarStore<F> {
    /// Create a new `ScalarStore` and add all `ScalarPtr`s reachable in the scalar representation of `expr`.
    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> Self {
        let mut new = Self::default();
        new.add_one_ptr(store, expr);
        new
    }

    /// Add all ScalarPtrs representing and reachable from expr.
    pub fn add_one_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) {
        self.add_ptr(store, expr);
        self.finalize(store);
    }

    /// Add the `ScalarPtr` representing `expr`, and queue it for proceessing.
    pub fn add_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) {
        // Find the scalar_ptr representing ptr.
        if let Some(scalar_ptr) = store.get_expr_hash(expr) {
            self.add(store, expr, scalar_ptr);
        };
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
            let scalar_expression =
                ScalarExpression::from_ptr(store, ptr).expect("ScalarExpression missing for ptr");
            if let Some(more_scalar_ptrs) = Self::child_scalar_ptrs(&scalar_expression) {
                new_pending_scalar_ptrs.extend(more_scalar_ptrs);
            };
            scalar_expression
        });

        self.pending_scalar_ptrs.extend(new_pending_scalar_ptrs);
    }

    /// All the `ScalarPtr`s directly reachable from `scalar_expression`, if any.
    fn child_scalar_ptrs(scalar_expression: &ScalarExpression<F>) -> Option<Vec<ScalarPtr<F>>> {
        match scalar_expression {
            ScalarExpression::Nil => None,
            ScalarExpression::Cons(car, cdr) => Some([*car, *cdr].into()),
            ScalarExpression::Sym(_str) => None,
            ScalarExpression::Fun {
                arg,
                body,
                closed_env,
            } => Some([*arg, *body, *closed_env].into()),
            ScalarExpression::Num(_) => None,
            ScalarExpression::Str(_) => None,
            ScalarExpression::Thunk(_) => None,
            ScalarExpression::OpaqueCons
            | ScalarExpression::OpaqueFun
            | ScalarExpression::OpaqueSym
            | ScalarExpression::OpaqueStr => None,
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
}

impl<F: LurkField> IpldEmbed for ScalarStore<F> {
    fn to_ipld(&self) -> Ipld {
        let map: Vec<(ScalarPtr<F>, ScalarExpression<F>)> = self
            .scalar_map
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        let mut pending = self.pending_scalar_ptrs.clone();
        pending.sort();
        Ipld::List([map.to_ipld(), pending.to_ipld()].into())
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::List(xs) => match xs.as_slice() {
                [map, pending] => {
                    let map: Vec<(ScalarPtr<F>, ScalarExpression<F>)> = IpldEmbed::from_ipld(map)?;
                    let pending: Vec<ScalarPtr<F>> = IpldEmbed::from_ipld(pending)?;
                    Ok(ScalarStore {
                        scalar_map: map.into_iter().collect(),
                        pending_scalar_ptrs: pending,
                    })
                }
                xs => Err(IpldError::expected(
                    "ScalarStore",
                    &Ipld::List(xs.to_owned()),
                )),
            },
            x => Err(IpldError::expected("ScalarStore", x)),
        }
    }
}

impl<'a, F: LurkField> ScalarExpression<F> {
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
pub enum ScalarExpression<F: LurkField> {
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
    /// The `Opaque` variants represent potentially private data which has been added to the store for use in a proof or
    /// computation, but for which no corresponding `Expression` is known. opaque `ScalarExpressions` therefore have no
    /// children for the purpose of graph creation or traversal.
    OpaqueCons,
    OpaqueFun,
    OpaqueSym,
    OpaqueStr,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum OpaqueTag {
    Nil = 0b1000_0000_0000_0000,
    Cons,
    Sym,
    Fun,
    Num,
    Thunk,
    Str,
}

impl<'a, F: LurkField> Default for ScalarExpression<F> {
    fn default() -> Self {
        Self::Nil
    }
}

impl<F: LurkField> IpldEmbed for ScalarExpression<F> {
    fn to_ipld(&self) -> Ipld {
        match self {
            Self::Nil => Ipld::List([Ipld::Integer(Tag::Nil as i128)].into()),
            Self::Cons(car, cdr) => Ipld::List(
                [
                    Ipld::Integer(Tag::Cons as i128),
                    car.to_ipld(),
                    cdr.to_ipld(),
                ]
                .into(),
            ),
            Self::Sym(sym) => Ipld::List(
                [
                    Ipld::Integer(Tag::Sym as i128),
                    Ipld::String(String::from(sym.clone())),
                ]
                .into(),
            ),
            Self::Fun {
                arg,
                body,
                closed_env,
            } => Ipld::List(
                [
                    Ipld::Integer(Tag::Fun as i128),
                    arg.to_ipld(),
                    body.to_ipld(),
                    closed_env.to_ipld(),
                ]
                .into(),
            ),
            Self::Num(x) => Ipld::List([Ipld::Integer(Tag::Num as i128), x.to_ipld()].into()),
            Self::Str(sym) => Ipld::List(
                [
                    Ipld::Integer(Tag::Str as i128),
                    Ipld::String(String::from(sym.clone())),
                ]
                .into(),
            ),
            Self::Thunk(thunk) => {
                Ipld::List([Ipld::Integer(Tag::Thunk as i128), thunk.to_ipld()].into())
            }
            Self::OpaqueCons => Ipld::List([Ipld::Integer(OpaqueTag::Cons as i128)].into()),
            Self::OpaqueFun => Ipld::List([Ipld::Integer(OpaqueTag::Fun as i128)].into()),
            Self::OpaqueSym => Ipld::List([Ipld::Integer(OpaqueTag::Sym as i128)].into()),
            Self::OpaqueStr => Ipld::List([Ipld::Integer(OpaqueTag::Str as i128)].into()),
        }
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        use Ipld::*;
        match ipld {
            List(xs) => match xs.as_slice() {
                [Integer(t)] if *t == Tag::Nil as i128 => Ok(Self::Nil),
                [Integer(t), car, cdr] if *t == Tag::Cons as i128 => {
                    let car = ScalarPtr::from_ipld(car)?;
                    let cdr = ScalarPtr::from_ipld(cdr)?;
                    Ok(Self::Cons(car, cdr))
                }
                [Integer(t), String(s)] if *t == Tag::Sym as i128 => Ok(Self::Sym(s.clone())),
                [Integer(t), arg, body, env] if *t == Tag::Fun as i128 => {
                    let arg = ScalarPtr::from_ipld(arg)?;
                    let body = ScalarPtr::from_ipld(body)?;
                    let closed_env = ScalarPtr::from_ipld(env)?;
                    Ok(Self::Fun {
                        arg,
                        body,
                        closed_env,
                    })
                }
                [Integer(t), num] if *t == Tag::Num as i128 => {
                    let num = Num::from_ipld(num)?;
                    Ok(Self::Num(num))
                }
                [Integer(t), String(s)] if *t == Tag::Str as i128 => Ok(Self::Str(s.clone())),
                [Integer(t), thunk] if *t == Tag::Thunk as i128 => {
                    let thunk = ScalarThunk::from_ipld(thunk)?;
                    Ok(Self::Thunk(thunk))
                }
                [Integer(t)] if *t == OpaqueTag::Cons as i128 => Ok(Self::OpaqueCons),
                [Integer(t)] if *t == OpaqueTag::Fun as i128 => Ok(Self::OpaqueFun),
                [Integer(t)] if *t == OpaqueTag::Sym as i128 => Ok(Self::OpaqueSym),
                [Integer(t)] if *t == OpaqueTag::Str as i128 => Ok(Self::OpaqueStr),
                xs => Err(IpldError::expected("Expr", &List(xs.to_owned()))),
            },
            x => Err(IpldError::expected("Expr", x)),
        }
    }
}

// Unused for now, but will be needed when we serialize Thunks to IPLD.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarThunk<F: LurkField> {
    pub(crate) value: ScalarPtr<F>,
    pub(crate) continuation: ScalarContPtr<F>,
}

impl<F: LurkField> Copy for ScalarThunk<F> {}

impl<F: LurkField> IpldEmbed for ScalarThunk<F> {
    fn to_ipld(&self) -> Ipld {
        Ipld::List([self.value.to_ipld(), self.continuation.to_ipld()].into())
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::List(xs) => match xs.as_slice() {
                [val, cont] => {
                    let value = ScalarPtr::from_ipld(val)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(ScalarThunk {
                        value,
                        continuation,
                    })
                }
                xs => Err(IpldError::expected(
                    "ScalarThunk",
                    &Ipld::List(xs.to_owned()),
                )),
            },
            x => Err(IpldError::expected("ScalarThunk", x)),
        }
    }
}

// Unused for now, but will be needed when we serialize Continuations to IPLD.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
