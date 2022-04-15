use std::collections::BTreeMap;

use crate::field::LurkField;
use libipld::Ipld;

use crate::ipld::FWrap;
use crate::ipld::IpldEmbed;
use crate::ipld::IpldError;
use crate::store::{ContTag, Op1, Op2, Pointer, Ptr, Rel2, ScalarContPtr, ScalarPtr, Store, Tag};
use crate::Num;

/// `ScalarStore` allows realization of a graph of `ScalarPtr`s suitable for serialization to IPLD. `ScalarExpression`s
/// are composed only of `ScalarPtr`s, so `scalar_map` suffices to allow traverseing an arbitrary DAG.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ScalarStore<F: LurkField> {
    scalar_map: BTreeMap<ScalarPtr<F>, Option<ScalarExpression<F>>>,
    scalar_cont_map: BTreeMap<ScalarContPtr<F>, Option<ScalarContinuation<F>>>,
    pending_scalar_ptrs: Vec<ScalarPtr<F>>,
}

impl<'a, F: LurkField> ScalarStore<F> {
    /// Create a new `ScalarStore` and add all `ScalarPtr`s reachable in the scalar representation of `expr`.
    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> Option<(Self, ScalarPtr<F>)> {
        let mut new = Self::default();
        let scalar_ptr = new.add_one_ptr(store, expr)?;
        Some((new, scalar_ptr))
    }

    /// Add all ScalarPtrs representing and reachable from expr.
    pub fn add_one_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) -> Option<ScalarPtr<F>> {
        let scalar_ptr = self.add_ptr(store, expr)?;
        self.finalize(store);
        Some(scalar_ptr)
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
            let scalar_expression =
                ScalarExpression::from_ptr(store, ptr).expect("ScalarExpression missing for ptr");
            if let Some(more_scalar_ptrs) = Self::child_scalar_ptrs(&scalar_expression) {
                new_pending_scalar_ptrs.extend(more_scalar_ptrs);
            };
            Some(scalar_expression)
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
    pub fn to_store(&mut self) -> Option<Store<F>> {
        if self.pending_scalar_ptrs.is_empty() {
            None
        } else {
            let mut store = Store::new();

            for ptr in self.scalar_map.keys() {
                store.intern_scalar_ptr(*ptr, self);
            }
            for ptr in self.scalar_cont_map.keys() {
                store.intern_scalar_cont_ptr(*ptr, self);
            }
            Some(store)
        }
    }
}

impl<F: LurkField> IpldEmbed for ScalarStore<F> {
    fn to_ipld(&self) -> Ipld {
        let map: Vec<(ScalarPtr<F>, Option<ScalarExpression<F>>)> = self
            .scalar_map
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        let cont_map: Vec<(ScalarContPtr<F>, Option<ScalarContinuation<F>>)> = self
            .scalar_cont_map
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        Ipld::List([map.to_ipld(), cont_map.to_ipld()].into())
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::List(xs) => match xs.as_slice() {
                [map, cont_map] => {
                    let map: Vec<(ScalarPtr<F>, Option<ScalarExpression<F>>)> =
                        IpldEmbed::from_ipld(map)?;
                    let cont_map: Vec<(ScalarContPtr<F>, Option<ScalarContinuation<F>>)> =
                        IpldEmbed::from_ipld(cont_map)?;
                    let pending: Vec<ScalarPtr<F>> = Vec::new();
                    Ok(ScalarStore {
                        scalar_map: map.into_iter().collect(),
                        scalar_cont_map: cont_map.into_iter().collect(),
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
            Tag::Cons => store.fetch_cons(ptr).and_then(|(car, cdr)| {
                store.get_expr_hash(car).and_then(|car| {
                    store
                        .get_expr_hash(cdr)
                        .map(|cdr| ScalarExpression::Cons(car, cdr))
                })
            }),
            Tag::Sym => store
                .fetch_sym(ptr)
                .map(|str| ScalarExpression::Sym(str.into())),
            Tag::Fun => store.fetch_fun(ptr).and_then(|(arg, body, closed_env)| {
                store.get_expr_hash(arg).and_then(|arg| {
                    store.get_expr_hash(body).and_then(|body| {
                        store
                            .get_expr_hash(closed_env)
                            .map(|closed_env| ScalarExpression::Fun {
                                arg,
                                body,
                                closed_env,
                            })
                    })
                })
            }),
            Tag::Num => store.fetch_num(ptr).map(|num| match num {
                Num::U64(x) => ScalarExpression::Num((*x).into()),
                Num::Scalar(x) => ScalarExpression::Num(*x),
            }),

            Tag::Str => store
                .fetch_str(ptr)
                .map(|str| ScalarExpression::Str(str.into())),

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
    Num(F),
    Str(String),
    Thunk(ScalarThunk<F>),
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
            Self::Sym(sym) => {
                Ipld::List([Ipld::Integer(Tag::Sym as i128), Ipld::String(sym.clone())].into())
            }
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
            Self::Num(x) => {
                Ipld::List([Ipld::Integer(Tag::Num as i128), FWrap(*x).to_ipld()].into())
            }
            Self::Str(s) => {
                Ipld::List([Ipld::Integer(Tag::Str as i128), Ipld::String(s.clone())].into())
            }
            Self::Thunk(thunk) => {
                Ipld::List([Ipld::Integer(Tag::Thunk as i128), thunk.to_ipld()].into())
            }
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
                    let num = FWrap::from_ipld(num)?;
                    Ok(Self::Num(num.0))
                }
                [Integer(t), String(s)] if *t == Tag::Str as i128 => Ok(Self::Str(s.clone())),
                [Integer(t), thunk] if *t == Tag::Thunk as i128 => {
                    let thunk = ScalarThunk::from_ipld(thunk)?;
                    Ok(Self::Thunk(thunk))
                }
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

// It is important that the order of list elements for each ScalarContinuation
// are consistent with the order of field elements in the
// `get_hash_components_*` functions
impl<F: LurkField> IpldEmbed for ScalarContinuation<F> {
    fn to_ipld(&self) -> Ipld {
        match self {
            Self::Outermost => Ipld::List([Ipld::Integer(ContTag::Outermost as i128)].into()),
            Self::Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Call as i128),
                unevaled_arg.to_ipld(),
                saved_env.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Call2 {
                function,
                saved_env,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Call2 as i128),
                function.to_ipld(),
                saved_env.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Tail {
                saved_env,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Tail as i128),
                saved_env.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Error => Ipld::List(vec![Ipld::Integer(ContTag::Error as i128)]),
            Self::Lookup {
                saved_env,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Lookup as i128),
                saved_env.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Unop {
                operator,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Unop as i128),
                operator.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Binop as i128),
                operator.to_ipld(),
                saved_env.to_ipld(),
                unevaled_args.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Binop2 as i128),
                operator.to_ipld(),
                evaled_arg.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Relop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Relop as i128),
                operator.to_ipld(),
                saved_env.to_ipld(),
                unevaled_args.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Relop2 {
                operator,
                evaled_arg,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Relop2 as i128),
                operator.to_ipld(),
                evaled_arg.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::If {
                unevaled_args,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::If as i128),
                unevaled_args.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Let {
                var,
                body,
                saved_env,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::Let as i128),
                var.to_ipld(),
                body.to_ipld(),
                saved_env.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::LetRec {
                var,
                saved_env,
                body,
                continuation,
            } => Ipld::List(vec![
                Ipld::Integer(ContTag::LetRec as i128),
                var.to_ipld(),
                body.to_ipld(),
                saved_env.to_ipld(),
                continuation.to_ipld(),
            ]),
            Self::Emit { continuation } => Ipld::List(vec![
                Ipld::Integer(ContTag::Emit as i128),
                continuation.to_ipld(),
            ]),
            Self::Dummy => Ipld::List(vec![Ipld::Integer(ContTag::Dummy as i128)]),
            Self::Terminal => Ipld::List(vec![Ipld::Integer(ContTag::Terminal as i128)]),
        }
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        use Ipld::Integer;
        match ipld {
            Ipld::List(xs) => match xs.as_slice() {
                [Integer(t)] if *t == ContTag::Outermost as i128 => Ok(Self::Outermost),
                [Integer(t), arg, env, cont] if *t == ContTag::Call as i128 => {
                    let unevaled_arg = ScalarPtr::from_ipld(arg)?;
                    let saved_env = ScalarPtr::from_ipld(env)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Call {
                        unevaled_arg,
                        saved_env,
                        continuation,
                    })
                }
                [Integer(t), fun, env, cont] if *t == ContTag::Call2 as i128 => {
                    let function = ScalarPtr::from_ipld(fun)?;
                    let saved_env = ScalarPtr::from_ipld(env)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Call2 {
                        function,
                        saved_env,
                        continuation,
                    })
                }
                [Integer(t), env, cont] if *t == ContTag::Tail as i128 => {
                    let saved_env = ScalarPtr::from_ipld(env)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Tail {
                        saved_env,
                        continuation,
                    })
                }
                [Integer(t)] if *t == ContTag::Error as i128 => Ok(Self::Error),
                [Integer(t), env, cont] if *t == ContTag::Lookup as i128 => {
                    let saved_env = ScalarPtr::from_ipld(env)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Lookup {
                        saved_env,
                        continuation,
                    })
                }
                [Integer(t), opr, cont] if *t == ContTag::Unop as i128 => {
                    let operator = Op1::from_ipld(opr)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Unop {
                        operator,
                        continuation,
                    })
                }
                [Integer(t), opr, env, arg, cont] if *t == ContTag::Binop as i128 => {
                    let operator = Op2::from_ipld(opr)?;
                    let saved_env = ScalarPtr::from_ipld(env)?;
                    let unevaled_args = ScalarPtr::from_ipld(arg)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Binop {
                        operator,
                        saved_env,
                        unevaled_args,
                        continuation,
                    })
                }
                [Integer(t), opr, arg, cont] if *t == ContTag::Binop2 as i128 => {
                    let operator = Op2::from_ipld(opr)?;
                    let evaled_arg = ScalarPtr::from_ipld(arg)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Binop2 {
                        operator,
                        evaled_arg,
                        continuation,
                    })
                }
                [Integer(t), opr, env, arg, cont] if *t == ContTag::Relop as i128 => {
                    let operator = Rel2::from_ipld(opr)?;
                    let saved_env = ScalarPtr::from_ipld(env)?;
                    let unevaled_args = ScalarPtr::from_ipld(arg)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Relop {
                        operator,
                        saved_env,
                        unevaled_args,
                        continuation,
                    })
                }
                [Integer(t), opr, arg, cont] if *t == ContTag::Relop2 as i128 => {
                    let operator = Rel2::from_ipld(opr)?;
                    let evaled_arg = ScalarPtr::from_ipld(arg)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Relop2 {
                        operator,
                        evaled_arg,
                        continuation,
                    })
                }
                [Integer(t), arg, cont] if *t == ContTag::If as i128 => {
                    let unevaled_args = ScalarPtr::from_ipld(arg)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::If {
                        unevaled_args,
                        continuation,
                    })
                }
                [Integer(t), var, body, env, cont] if *t == ContTag::Let as i128 => {
                    let var = ScalarPtr::from_ipld(var)?;
                    let body = ScalarPtr::from_ipld(body)?;
                    let saved_env = ScalarPtr::from_ipld(env)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Let {
                        var,
                        body,
                        saved_env,
                        continuation,
                    })
                }
                [Integer(t), var, body, env, cont] if *t == ContTag::LetRec as i128 => {
                    let var = ScalarPtr::from_ipld(var)?;
                    let saved_env = ScalarPtr::from_ipld(env)?;
                    let body = ScalarPtr::from_ipld(body)?;
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::LetRec {
                        var,
                        body,
                        saved_env,
                        continuation,
                    })
                }
                [Integer(t), cont] if *t == ContTag::Emit as i128 => {
                    let continuation = ScalarContPtr::from_ipld(cont)?;
                    Ok(Self::Emit { continuation })
                }
                [Integer(t)] if *t == ContTag::Dummy as i128 => Ok(Self::Dummy),
                [Integer(t)] if *t == ContTag::Terminal as i128 => Ok(Self::Terminal),
                xs => Err(IpldError::expected(
                    "ScalarContinuation",
                    &Ipld::List(xs.to_owned()),
                )),
            },
            x => Err(IpldError::expected("ScalarContinuation", x)),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::eval::empty_sym_env;
    use crate::store::ScalarPointer;
    use blstrs::Scalar as Fr;

    use pasta_curves::pallas::Scalar;
    use quickcheck::{Arbitrary, Gen};

    use crate::test::frequency;

    impl Arbitrary for ScalarThunk<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            ScalarThunk {
                value: Arbitrary::arbitrary(g),
                continuation: Arbitrary::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn test_scalar_thunk_ipld_embed(x: ScalarThunk<Fr>) -> bool {
        match ScalarThunk::from_ipld(&x.to_ipld()) {
            Ok(y) if x == y => true,
            Ok(y) => {
                println!("x: {:?}", x);
                println!("y: {:?}", y);
                false
            }
            Err(e) => {
                println!("{:?}", x);
                println!("{:?}", e);
                false
            }
        }
    }

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
                    Box::new(|g| Self::Relop {
                        operator: Rel2::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        unevaled_args: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Relop2 {
                        operator: Rel2::arbitrary(g),
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
    fn test_scalar_expr_ipld_embed(x: ScalarExpression<Fr>) -> bool {
        match ScalarExpression::from_ipld(&x.to_ipld()) {
            Ok(y) if x == y => true,
            Ok(y) => {
                println!("x: {:?}", x);
                println!("y: {:?}", y);
                false
            }
            Err(e) => {
                println!("{:?}", x);
                println!("{:?}", e);
                false
            }
        }
    }

    #[quickcheck]
    fn test_scalar_cont_ipld_embed(x: ScalarContinuation<Fr>) -> bool {
        match ScalarContinuation::from_ipld(&x.to_ipld()) {
            Ok(y) if x == y => true,
            Ok(y) => {
                println!("x: {:?}", x);
                println!("y: {:?}", y);
                false
            }
            Err(e) => {
                println!("{:?}", x);
                println!("{:?}", e);
                false
            }
        }
    }

    //// This doesn't create well-defined ScalarStores, but is still useful for
    //// testing ipld
    impl Arbitrary for ScalarStore<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            let map: Vec<(ScalarPtr<Fr>, Option<ScalarExpression<Fr>>)> = Arbitrary::arbitrary(g);
            let cont_map: Vec<(ScalarContPtr<Fr>, Option<ScalarContinuation<Fr>>)> =
                Arbitrary::arbitrary(g);
            ScalarStore {
                scalar_map: map.into_iter().collect(),
                scalar_cont_map: cont_map.into_iter().collect(),
                pending_scalar_ptrs: Vec::new(),
            }
        }
    }

    #[quickcheck]
    fn test_scalar_store_ipld_embed(x: ScalarStore<Fr>) -> bool {
        match ScalarStore::from_ipld(&x.to_ipld()) {
            Ok(y) if x == y => true,
            Ok(y) => {
                println!("x: {:?}", x);
                println!("y: {:?}", y);
                false
            }
            Err(e) => {
                println!("{:?}", x);
                println!("{:?}", e);
                false
            }
        }
    }

    #[test]
    fn test_expr_ipld() {
        let test = |src| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&s, &expr) {
                let ipld = scalar_store.to_ipld();
                println!("{:?}", scalar_store);
                println!("{:?}", ipld);
                let scalar_store2 = ScalarStore::<Fr>::from_ipld(&ipld).unwrap();
                assert_eq!(scalar_store, scalar_store2);
            } else {
                assert!(false)
            }
        };

        test("symbol");
        test("(1 . 2)");
        test("(+ 1 2 3)");
        test("(+ 1 2 (* 3 4))");
        test("(+ 1 2 (* 3 4) \"asdf\" )");
        test("(+ 1 2 2 (* 3 4) \"asdf\" \"asdf\")");
        assert!(false);
    }

    #[test]
    fn test_scalar_store() {
        let test = |src, expected| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&s, &expr) {
                assert_eq!(expected, scalar_store.scalar_map.len());
            } else {
                assert!(false)
            }
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

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_cons) {
            assert_eq!(1, scalar_store.scalar_map.len());
        } else {
            assert!(false)
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
        let opaque_fun = store.intern_opaque_fun(*fun_hash.value());
        store.hydrate_scalar_cache();

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_fun) {
            assert_eq!(1, scalar_store.scalar_map.len());
        } else {
            assert!(false)
        }
    }
    #[test]
    fn test_scalar_store_opaque_sym() {
        let mut store = Store::<Fr>::default();

        let sym = store.sym(&"sym");
        let sym_hash = store.hash_expr(&sym).unwrap();
        let opaque_sym = store.intern_opaque_sym(*sym_hash.value());

        store.hydrate_scalar_cache();

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_sym) {
            assert_eq!(1, scalar_store.scalar_map.len());
        } else {
            assert!(false)
        }
    }
    #[test]
    fn test_scalar_store_opaque_str() {
        let mut store = Store::<Fr>::default();

        let str = store.str(&"str");
        let str_hash = store.hash_expr(&str).unwrap();
        let opaque_str = store.intern_opaque_sym(*str_hash.value());

        store.hydrate_scalar_cache();

        if let Some((scalar_store, _)) = ScalarStore::new_with_expr(&store, &opaque_str) {
            assert_eq!(1, scalar_store.scalar_map.len());
        } else {
            assert!(false)
        }
    }
}
