use std::collections::BTreeMap;

use crate::field::LurkField;

use crate::cont::Continuation;
use crate::expr;
#[cfg(not(target_arch = "wasm32"))]
use crate::field::FWrap;
use crate::ptr::{ContPtr, Ptr};
use crate::store::Store;
use crate::tag::ContTag;
use crate::tag::{ExprTag, Op1, Op2};
use crate::z_data::{ZContPtr, ZExprPtr, ZStore};
use crate::{Num, Sym, UInt};
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::Deserialize;
use serde::Serialize;

/// `ScalarStore` allows realization of a graph of `ZExprPtr`s suitable for serialization to IPLD. `ScalarExpression`s
/// are composed only of `ZExprPtr`s, so `scalar_map` suffices to allow traversing an arbitrary DAG.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScalarStore<F: LurkField> {
    scalar_map: BTreeMap<ZExprPtr<F>, Option<ScalarExpression<F>>>,
    scalar_cont_map: BTreeMap<ZContPtr<F>, Option<ScalarContinuation<F>>>,
    #[serde(skip)]
    pending_scalar_ptrs: Vec<ZExprPtr<F>>,
}

impl<F: LurkField> ScalarStore<F> {
    /// Create a new `ScalarStore` and add all `ZExprPtr`s reachable in the scalar representation of `expr`.
    pub fn new_with_expr(store: &Store<F>, expr: &Ptr<F>) -> (Self, Option<ZExprPtr<F>>) {
        let mut new = Self::default();
        let scalar_ptr = new.add_one_ptr(store, expr);
        (new, scalar_ptr)
    }

    /// Add all ZExprPtrs representing and reachable from expr.
    pub fn add_one_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) -> Option<ZExprPtr<F>> {
        let scalar_ptr = self.add_ptr(store, expr);
        self.finalize(store);
        scalar_ptr
    }

    /// Add the `ZExprPtr` representing `expr`, and queue it for proceessing.
    pub fn add_ptr(&mut self, store: &Store<F>, expr: &Ptr<F>) -> Option<ZExprPtr<F>> {
        // Find the scalar_ptr representing ptr.
        if let Some(scalar_ptr) = store.get_expr_hash(expr) {
            self.add(store, expr, scalar_ptr);
            Some(scalar_ptr)
        } else {
            None
        }
    }

    /// Add a single `ZExprPtr` and queue it for processing.
    /// NOTE: This requires that `store.scalar_cache` has been hydrated.
    fn add_scalar_ptr(&mut self, store: &Store<F>, scalar_ptr: ZExprPtr<F>) {
        // Find the ptr corresponding to scalar_ptr.
        if let Some(ptr) = store.scalar_ptr_map.get(&scalar_ptr) {
            self.add(store, &*ptr, scalar_ptr);
        }
    }

    /// Add the `ZExprPtr` and `ScalarExpression` associated with `ptr`. The relationship between `ptr` and
    /// `scalar_ptr` is not checked here, so `add` should only be called by `add_ptr` and `add_scalar_ptr`, which
    /// enforce this relationship.
    fn add(&mut self, store: &Store<F>, ptr: &Ptr<F>, scalar_ptr: ZExprPtr<F>) {
        let mut new_pending_scalar_ptrs: Vec<ZExprPtr<F>> = Default::default();

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

    /// All the `ZExprPtr`s directly reachable from `scalar_expression`, if any.
    fn child_scalar_ptrs(scalar_expression: &ScalarExpression<F>) -> Option<Vec<ZExprPtr<F>>> {
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

    /// Unqueue all the pending `ZExprPtr`s and add them, queueing all of their children, then repeat until the queue
    /// is pending queue is empty.
    fn add_pending_scalar_ptrs(&mut self, store: &Store<F>) {
        while let Some(scalar_ptr) = self.pending_scalar_ptrs.pop() {
            self.add_scalar_ptr(store, scalar_ptr);
        }
        assert!(self.pending_scalar_ptrs.is_empty());
    }

    /// Method which finalizes the `ScalarStore`, ensuring that all reachable `ZExprPtr`s have been added.
    pub fn finalize(&mut self, store: &Store<F>) {
        self.add_pending_scalar_ptrs(store);
    }
    pub fn get_expr(&self, ptr: &ZExprPtr<F>) -> Option<&ScalarExpression<F>> {
        let x = self.scalar_map.get(ptr)?;
        (*x).as_ref()
    }

    pub fn get_cont(&self, ptr: &ZContPtr<F>) -> Option<&ScalarContinuation<F>> {
        let x = self.scalar_cont_map.get(ptr)?;
        (*x).as_ref()
    }

    pub fn to_store_with_expr(&mut self, ptr: &ZExprPtr<F>) -> Option<(Store<F>, Ptr<F>)> {
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
    pub fn insert_scalar_expression(
        &mut self,
        ptr: ZExprPtr<F>,
        expr: Option<ScalarExpression<F>>,
    ) -> Option<Option<ScalarExpression<F>>> {
        self.scalar_map.insert(ptr, expr)
    }
}

impl<F: LurkField> ScalarExpression<F> {
    fn from_ptr(store: &Store<F>, ptr: &Ptr<F>) -> Option<Self> {
        match ptr.tag {
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
    Cons(ZExprPtr<F>, ZExprPtr<F>),
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(
            strategy = "any::<(FWrap<F>, ZExprPtr<F>)>().prop_map(|(x, y)| Self::Comm(x.0, y))"
        )
    )]
    Comm(F, ZExprPtr<F>),
    Sym(Sym),
    Fun {
        arg: ZExprPtr<F>,
        body: ZExprPtr<F>,
        closed_env: ZExprPtr<F>,
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
    pub(crate) value: ZExprPtr<F>,
    pub(crate) continuation: ZContPtr<F>,
}

impl<F: LurkField> Copy for ScalarThunk<F> {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub enum ScalarContinuation<F: LurkField> {
    Outermost,
    Call {
        unevaled_arg: ZExprPtr<F>,
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Call2 {
        function: ZExprPtr<F>,
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Tail {
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Error,
    Lookup {
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Unop {
        operator: Op1,
        continuation: ZContPtr<F>,
    },
    Binop {
        operator: Op2,
        saved_env: ZExprPtr<F>,
        unevaled_args: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Binop2 {
        operator: Op2,
        evaled_arg: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    If {
        unevaled_args: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Let {
        var: ZExprPtr<F>,
        body: ZExprPtr<F>,
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    LetRec {
        var: ZExprPtr<F>,
        body: ZExprPtr<F>,
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Emit {
        continuation: ZContPtr<F>,
    },
    Dummy,
    Terminal,
}

impl<F: LurkField> Store<F> {
    pub fn intern_scalar_cont_ptr(
        &mut self,
        ptr: ZContPtr<F>,
        scalar_store: &ScalarStore<F>,
    ) -> Option<ContPtr<F>> {
        use ScalarContinuation::*;
        let tag: ContTag = ptr.tag();

        if let Some(cont) = scalar_store.get_cont(&ptr) {
            let continuation = match cont {
                Outermost => Continuation::Outermost,
                Dummy => Continuation::Dummy,
                Terminal => Continuation::Terminal,
                Call {
                    unevaled_arg,
                    saved_env,
                    continuation,
                } => Continuation::Call {
                    unevaled_arg: self.intern_scalar_ptr(*unevaled_arg, scalar_store)?,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },

                Call2 {
                    function,
                    saved_env,
                    continuation,
                } => Continuation::Call2 {
                    function: self.intern_scalar_ptr(*function, scalar_store)?,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Tail {
                    saved_env,
                    continuation,
                } => Continuation::Tail {
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Error => Continuation::Error,
                Lookup {
                    saved_env,
                    continuation,
                } => Continuation::Lookup {
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Unop {
                    operator,
                    continuation,
                } => Continuation::Unop {
                    operator: *operator,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Binop {
                    operator,
                    saved_env,
                    unevaled_args,
                    continuation,
                } => Continuation::Binop {
                    operator: *operator,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    unevaled_args: self.intern_scalar_ptr(*unevaled_args, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Binop2 {
                    operator,
                    evaled_arg,
                    continuation,
                } => Continuation::Binop2 {
                    operator: *operator,
                    evaled_arg: self.intern_scalar_ptr(*evaled_arg, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                If {
                    unevaled_args,
                    continuation,
                } => Continuation::If {
                    unevaled_args: self.intern_scalar_ptr(*unevaled_args, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Let {
                    var,
                    body,
                    saved_env,
                    continuation,
                } => Continuation::Let {
                    var: self.intern_scalar_ptr(*var, scalar_store)?,
                    body: self.intern_scalar_ptr(*body, scalar_store)?,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                LetRec {
                    var,
                    body,
                    saved_env,
                    continuation,
                } => Continuation::LetRec {
                    var: self.intern_scalar_ptr(*var, scalar_store)?,
                    body: self.intern_scalar_ptr(*body, scalar_store)?,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Emit { continuation } => Continuation::Emit {
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
            };

            if continuation.cont_tag() == tag {
                Some(continuation.intern_aux(self))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn intern_scalar_ptr(
        &mut self,
        scalar_ptr: ZExprPtr<F>,
        scalar_store: &ScalarStore<F>,
    ) -> Option<Ptr<F>> {
        if let Some(ptr) = self.fetch_scalar(&scalar_ptr) {
            Some(ptr)
        } else {
            use ScalarExpression::*;
            match (scalar_ptr.tag(), scalar_store.get_expr(&scalar_ptr)) {
                (ExprTag::Nil, Some(Nil)) => {
                    let ptr = self.intern_nil();
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Cons, Some(Cons(car, cdr))) => {
                    let car = self.intern_scalar_ptr(*car, scalar_store)?;
                    let cdr = self.intern_scalar_ptr(*cdr, scalar_store)?;
                    let ptr = self.intern_cons(car, cdr);
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Comm, Some(Comm(secret, payload))) => {
                    let payload = self.intern_scalar_ptr(*payload, scalar_store)?;
                    let ptr = self.intern_comm(*secret, payload);
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Str, Some(Str(s))) => {
                    let ptr = self.intern_str(s);
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Sym, Some(Sym(s))) => {
                    let ptr = self.intern_sym(s);
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Key, Some(Sym(k))) => {
                    let ptr = self.intern_key(k);
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Num, Some(Num(x))) => {
                    let ptr = self.intern_num(crate::Num::Scalar(*x));
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Char, Some(Char(x))) => Some((*x).into()),
                (ExprTag::Thunk, Some(Thunk(t))) => {
                    let value = self.intern_scalar_ptr(t.value, scalar_store)?;
                    let continuation = self.intern_scalar_cont_ptr(t.continuation, scalar_store)?;
                    let ptr = self.intern_thunk(expr::Thunk {
                        value,
                        continuation,
                    });
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (
                    ExprTag::Fun,
                    Some(Fun {
                        arg,
                        body,
                        closed_env,
                    }),
                ) => {
                    let arg = self.intern_scalar_ptr(*arg, scalar_store)?;
                    let body = self.intern_scalar_ptr(*body, scalar_store)?;
                    let env = self.intern_scalar_ptr(*closed_env, scalar_store)?;
                    let ptr = self.intern_fun(arg, body, env);
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                (tag, None) => {
                    let ptr = self.intern_maybe_opaque(tag, scalar_ptr.1);
                    self.create_scalar_ptr(ptr, *scalar_ptr.value());
                    Some(ptr)
                }
                _ => None,
            }
        }
    }
}

impl<F: LurkField> ZStore<F> {
    // fn insert_scalar_string(
    //     &self,
    //     ptr0: ZExprPtr<F>,
    //     store: &mut ScalarStore<F>,
    // ) -> anyhow::Result<String> {
    //     let mut s = String::new();
    //     let mut tail_ptrs = vec![];
    //     let mut ptr = ptr0;
    //     let strnil_ptr = ZExprPtr::from_parts(ExprTag::Str, F::zero());

    //     // TODO: this needs to bail on encountering an opaque pointer
    //     while let Some(ZExpr::StrCons(c, cs)) = self.get(&ptr).flatten() {
    //         let chr = c
    //             .value()
    //             .to_char()
    //             .ok_or_else(|| anyhow!("Non-char head in ZExpr::StrCons"))?;
    //         store.insert_scalar_expression(c, Some(ScalarExpression::Char(chr)));
    //         s.push(chr);
    //         if cs != strnil_ptr {
    //             tail_ptrs.push(cs);
    //         }
    //         ptr = cs
    //     }
    //     // Useful when called from insert_scalar_symbol
    //     if s.is_empty() {
    //         return Err(anyhow!(
    //             "encountered no StrCons in ZStore::insert_scalar_string, is this a string pointer?"
    //         ));
    //     }

    //     // If we've already inserted this string, no need to go through suffixes again
    //     if let Some(ScalarExpression::Str(old_value)) = store
    //         .insert_scalar_expression(ptr0, Some(ScalarExpression::Str(s.clone())))
    //         .flatten()
    //     {
    //         if old_value == s {
    //             return Ok(s);
    //         }
    //     }
    //     store.insert_scalar_expression(strnil_ptr, Some(ScalarExpression::Str(String::from(""))));

    //     let mut tail = String::new();
    //     for (ptr, c) in tail_ptrs.iter().rev().zip(s.chars().rev()) {
    //         tail = format!("{}{}", c, tail);
    //         store.insert_scalar_expression(*ptr, Some(ScalarExpression::Str(tail.clone())));
    //     }
    //     Ok(s)
    // }

    // fn insert_scalar_symbol(
    //     &self,
    //     ptr0: ZExprPtr<F>,
    //     store: &mut ScalarStore<F>,
    // ) -> anyhow::Result<Sym> {
    //     let mut path = Sym::root();
    //     let mut tail_ptrs = vec![ptr0];
    //     let mut ptr = ptr0;
    //     let symnil_ptr = ZExprPtr::from_parts(ExprTag::Sym, F::zero());

    //     // TODO: this needs to bail on encountering an opaque pointer
    //     while let Some(ZExpr::SymCons(s, ss)) = self.get(&ptr).flatten() {
    //         let string = if s == ZExprPtr::from_parts(ExprTag::Str, F::zero()) {
    //             Ok(String::new())
    //         } else {
    //             self.insert_scalar_string(s, store)
    //         }?;
    //         path = path.child(string);
    //         if ss != symnil_ptr {
    //             tail_ptrs.push(ss);
    //         }
    //         ptr = ss
    //     }

    //     // If we've already inserted this symbol, no need to go through suffixes again
    //     if let Some(old_value) =
    //         store.insert_scalar_expression(ptr0, Some(ScalarExpression::Sym(path.clone())))
    //     {
    //         if old_value == Some(ScalarExpression::Sym(path.clone())) {
    //             return Ok(path);
    //         }
    //     }
    //     store.insert_scalar_expression(symnil_ptr, Some(ScalarExpression::Sym(Sym::root())));

    //     let mut tail = Sym::root();
    //     for (ptr, string) in tail_ptrs.iter().rev().zip(path.path().iter().rev()) {
    //         tail = tail.child(string.clone());
    //         store.insert_scalar_expression(*ptr, Some(ScalarExpression::Sym(tail.clone())));
    //     }
    //     Ok(path)
    // }

    // fn intern_leaf(&self, ptr: ZExprPtr<F>, store: &mut ScalarStore<F>) -> anyhow::Result<()> {
    //     match ptr.tag() {
    //         ExprTag::Num => {
    //             store.insert_scalar_expression(ptr, Some(ScalarExpression::Num(*ptr.value())));
    //         }
    //         ExprTag::Char => {
    //             let c = ptr
    //                 .value()
    //                 .to_char()
    //                 .ok_or_else(|| anyhow!("Invalid char pointer: {ptr}"))?;
    //             store.insert_scalar_expression(ptr, Some(ScalarExpression::Char(c)));
    //         }
    //         ExprTag::U64 => {
    //             let u = ptr
    //                 .value()
    //                 .to_u64()
    //                 .ok_or_else(|| anyhow!("Invalid u64 pointer: {ptr}"))?;
    //             store.insert_scalar_expression(ptr, Some(ScalarExpression::UInt(u.into())));
    //         }
    //         ExprTag::Str => {
    //             store.insert_scalar_expression(ptr, Some(ScalarExpression::Str(String::new())));
    //         }
    //         ExprTag::Sym => {
    //             store.insert_scalar_expression(ptr, Some(ScalarExpression::Sym(Sym::root())));
    //         }
    //         _ => return Err(anyhow!("Invalid leaf pointer: {ptr}")),
    //     };
    //     Ok(())
    // }

    // fn intern_non_leaf(
    //     &self,
    //     ptr: ZExprPtr<F>,
    //     store: &mut ScalarStore<F>,
    //     stack: &mut Vec<ZExprPtr<F>>,
    // ) -> anyhow::Result<()> {
    //     match self.get(&ptr) {
    //         None => return Err(anyhow!("ZExpr not found for pointer {ptr}")),
    //         Some(None) => {
    //             // opaque data
    //             store.insert_scalar_expression(ptr, None);
    //         }
    //         Some(Some(expr)) => match (ptr.tag(), expr.clone()) {
    //             (ExprTag::Nil, ZExpr::Nil) => {
    //                 // We also need to intern the `.LURK.NIL` symbol
    //                 stack.push(ZExprPtr::from_parts(ExprTag::Sym, *ptr.value()));
    //                 store.insert_scalar_expression(ptr, Some(ScalarExpression::Nil));
    //             }
    //             (ExprTag::Cons, ZExpr::Cons(x, y)) => {
    //                 stack.push(x);
    //                 stack.push(y);
    //                 store.insert_scalar_expression(ptr, Some(ScalarExpression::Cons(x, y)));
    //             }
    //             (ExprTag::Comm, ZExpr::Comm(f, x)) => {
    //                 stack.push(x);
    //                 store.insert_scalar_expression(ptr, Some(ScalarExpression::Comm(f, x)));
    //             }
    //             (ExprTag::Sym, ZExpr::SymCons(_, _)) => {
    //                 self.insert_scalar_symbol(ptr, store)?;
    //             }
    //             (ExprTag::Str, ZExpr::StrCons(_, _)) => {
    //                 self.insert_scalar_string(ptr, store)?;
    //             }
    //             (tag, _) => {
    //                 return Err(anyhow!(
    //                     "Unsupported pair of tag and ZExpr: ({tag}, {expr})"
    //                 ))
    //             }
    //         },
    //     };
    //     Ok(())
    // }

    // /// Eagerly traverses the ZStore starting out from a ZExprPtr, adding
    // /// pointers and their respective expressions to a target ScalarStore. When
    // /// handling non-leaf pointers, their corresponding expressions might
    // /// add more pointers to be visited to a stack.
    // ///
    // /// TODO: add a cycle detection logic
    // fn intern_ptr_data(
    //     &self,
    //     ptr0: ZExprPtr<F>,
    //     store: &mut ScalarStore<F>,
    // ) -> anyhow::Result<()> {
    //     let mut stack = Vec::new();
    //     stack.push(ptr0);
    //     while let Some(ptr) = stack.pop() {
    //         if store.get_expr(&ptr).is_some() {
    //             continue;
    //         }
    //         if self.is_ptr_leaf(ptr) {
    //             self.intern_leaf(ptr, store)?;
    //         } else {
    //             self.intern_non_leaf(ptr, store, &mut stack)?;
    //         }
    //     }
    //     Ok(())
    // }

    /// Convert ZStore to ScalarStore.
    fn to_scalar_store(&self) -> anyhow::Result<ScalarStore<F>> {
        todo!()
        // let mut store = ScalarStore::default();
        // for ptr in self.scalar_map.keys() {
        //     if self.is_ptr_leaf(*ptr) {
        //         return Err(anyhow!("Leaf pointer found in ZStore: {ptr}"));
        //     }
        //     self.intern_ptr_data(*ptr, &mut store)?;
        // }
        // Ok(store)
    }
}

impl<F: LurkField> TryFrom<ZStore<F>> for ScalarStore<F> {
    type Error = anyhow::Error;

    fn try_from(store: ZStore<F>) -> Result<Self, Self::Error> {
        store.to_scalar_store()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
    };

    use blstrs::Scalar as Fr;

    use tap::TapFallible;

    use crate::z_data::ZExpr;
    use libipld::serde::from_ipld;
    use libipld::serde::to_ipld;

    use pasta_curves::pallas::Scalar;
    use std::collections::BTreeMap;

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
                any::<ZExprPtr<Fr>>(),
                any::<Option<ScalarExpression<Fr>>>(),
                0..1,
            ),
            prop::collection::btree_map(
                any::<ZContPtr<Fr>>(),
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
            let lang: Lang<Fr, Coproc<Fr>> = Lang::new();
            let mut eval = eval::Evaluator::new(expr, env, &mut s, 100, &lang);
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

    #[test]
    fn test_convert_z_store_with_strings_and_symbols() {
        // inserts the strings "hi" and "yo", then the symbols `.hi` and `.hi.yo`
        let (str1_c1, str1_c2) = ('h', 'i');
        let (str2_c1, str2_c2) = ('y', 'o');
        let str1_c1_ptr = ZExprPtr::from_parts(ExprTag::Char, Scalar::from_char(str1_c1));
        let str1_c2_ptr = ZExprPtr::from_parts(ExprTag::Char, Scalar::from_char(str1_c2));
        let str2_c1_ptr = ZExprPtr::from_parts(ExprTag::Char, Scalar::from_char(str2_c1));
        let str2_c2_ptr = ZExprPtr::from_parts(ExprTag::Char, Scalar::from_char(str2_c2));

        let str_nil = ZExprPtr::from_parts(ExprTag::Str, Scalar::zero());
        let sym_nil = ZExprPtr::from_parts(ExprTag::Sym, Scalar::zero());

        // placeholder hashes
        let str1_ptr_half = ZExprPtr::from_parts(ExprTag::Str, Scalar::from_u64(1));
        let str1_ptr_full = ZExprPtr::from_parts(ExprTag::Str, Scalar::from_u64(2));
        let str2_ptr_half = ZExprPtr::from_parts(ExprTag::Str, Scalar::from_u64(3));
        let str2_ptr_full = ZExprPtr::from_parts(ExprTag::Str, Scalar::from_u64(4));

        let sym_ptr_half = ZExprPtr::from_parts(ExprTag::Sym, Scalar::from_u64(5));
        let sym_ptr_full = ZExprPtr::from_parts(ExprTag::Sym, Scalar::from_u64(6));

        let mut z_store = BTreeMap::new();
        z_store.insert(str1_ptr_half, Some(ZExpr::StrCons(str1_c2_ptr, str_nil)));
        z_store.insert(
            str1_ptr_full,
            Some(ZExpr::StrCons(str1_c1_ptr, str1_ptr_half)),
        );
        z_store.insert(str2_ptr_half, Some(ZExpr::StrCons(str2_c2_ptr, str_nil)));
        z_store.insert(
            str2_ptr_full,
            Some(ZExpr::StrCons(str2_c1_ptr, str2_ptr_half)),
        );

        z_store.insert(sym_ptr_half, Some(ZExpr::SymCons(str1_ptr_full, sym_nil)));
        z_store.insert(
            sym_ptr_full,
            Some(ZExpr::SymCons(str2_ptr_full, sym_ptr_half)),
        );

        let expected_output = {
            let mut output = ScalarStore::default();

            output.insert_scalar_expression(str1_c1_ptr, Some(ScalarExpression::Char(str1_c1)));
            output.insert_scalar_expression(str1_c2_ptr, Some(ScalarExpression::Char(str1_c2)));
            output.insert_scalar_expression(str2_c1_ptr, Some(ScalarExpression::Char(str2_c1)));
            output.insert_scalar_expression(str2_c2_ptr, Some(ScalarExpression::Char(str2_c2)));

            output.insert_scalar_expression(str_nil, Some(ScalarExpression::Str(String::new())));

            let str1 = str1_c1.to_string() + &str1_c2.to_string();
            let str2 = str2_c1.to_string() + &str2_c2.to_string();
            output.insert_scalar_expression(
                str1_ptr_half,
                Some(ScalarExpression::Str(str1_c2.to_string())),
            );
            output
                .insert_scalar_expression(str1_ptr_full, Some(ScalarExpression::Str(str1.clone())));
            output.insert_scalar_expression(
                str2_ptr_half,
                Some(ScalarExpression::Str(str2_c2.to_string())),
            );

            let sym_root = Sym::root();
            output.insert_scalar_expression(sym_nil, Some(ScalarExpression::Sym(sym_root.clone())));
            output
                .insert_scalar_expression(str2_ptr_full, Some(ScalarExpression::Str(str2.clone())));
            let sym_half = sym_root.child(str1);
            let sym_full = sym_half.child(str2);
            output.insert_scalar_expression(sym_ptr_half, Some(ScalarExpression::Sym(sym_half)));
            output.insert_scalar_expression(sym_ptr_full, Some(ScalarExpression::Sym(sym_full)));

            output
        };

        assert_eq!(
            ZStore::to_scalar_store(&ZStore {
                expr_map: z_store,
                cont_map: Default::default()
            })
            .unwrap(),
            expected_output
        );
    }
}
