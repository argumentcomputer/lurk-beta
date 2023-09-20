use std::hash::Hash;

use crate::field::LurkField;
use crate::ptr::{ContPtr, Ptr};
use crate::tag::{ContTag, Op1, Op2};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Continuation<F: LurkField> {
    Outermost,
    Call0 {
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Call {
        unevaled_arg: Ptr<F>,
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Call2 {
        saved_env: Ptr<F>,
        function: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Tail {
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Error,
    Lookup {
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Unop {
        operator: Op1,
        continuation: ContPtr<F>,
    },
    Binop {
        operator: Op2,
        saved_env: Ptr<F>,
        unevaled_args: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Binop2 {
        operator: Op2,
        evaled_arg: Ptr<F>,
        continuation: ContPtr<F>,
    },
    If {
        unevaled_args: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Let {
        var: Ptr<F>,
        body: Ptr<F>,
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    LetRec {
        var: Ptr<F>,
        body: Ptr<F>,
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Emit {
        continuation: ContPtr<F>,
    },
    Dummy,
    Terminal,
}

impl<F: LurkField> Continuation<F> {
    pub(crate) fn intern_aux(&self, store: &mut crate::store::Store<F>) -> ContPtr<F> {
        match self {
            Self::Outermost | Self::Dummy | Self::Error | Self::Terminal => {
                let cont_ptr = self.get_simple_cont();
                store.mark_dehydrated_cont(cont_ptr);
                cont_ptr
            }
            _ => {
                let (p, inserted) = self.insert_in_store(store);
                let ptr = ContPtr::index(self.cont_tag(), p);
                if inserted {
                    store.dehydrated_cont.push(ptr)
                }
                ptr
            }
        }
    }
    pub fn insert_in_store(&self, store: &mut crate::store::Store<F>) -> (usize, bool) {
        match self {
            Self::Outermost | Self::Dummy | Self::Error | Self::Terminal => (0, false),
            Self::Call0 {
                saved_env,
                continuation,
            } => store
                .call0_store
                .insert_probe(Box::new((*saved_env, *continuation))),
            Self::Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => {
                store
                    .call_store
                    .insert_probe(Box::new((*unevaled_arg, *saved_env, *continuation)))
            }
            Self::Call2 {
                function,
                saved_env,
                continuation,
            } => store
                .call2_store
                .insert_probe(Box::new((*function, *saved_env, *continuation))),
            Self::Tail {
                saved_env,
                continuation,
            } => store
                .tail_store
                .insert_probe(Box::new((*saved_env, *continuation))),
            Self::Lookup {
                saved_env,
                continuation,
            } => store
                .lookup_store
                .insert_probe(Box::new((*saved_env, *continuation))),
            Self::Unop {
                operator,
                continuation,
            } => store
                .unop_store
                .insert_probe(Box::new((*operator, *continuation))),
            Self::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => store.binop_store.insert_probe(Box::new((
                *operator,
                *saved_env,
                *unevaled_args,
                *continuation,
            ))),
            Self::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => store
                .binop2_store
                .insert_probe(Box::new((*operator, *evaled_arg, *continuation))),
            Self::If {
                unevaled_args,
                continuation,
            } => store
                .if_store
                .insert_probe(Box::new((*unevaled_args, *continuation))),
            Self::Let {
                var,
                body,
                saved_env,
                continuation,
            } => store
                .let_store
                .insert_probe(Box::new((*var, *body, *saved_env, *continuation))),
            Self::LetRec {
                var,
                body,
                saved_env,
                continuation,
            } => {
                store
                    .letrec_store
                    .insert_probe(Box::new((*var, *body, *saved_env, *continuation)))
            }
            Self::Emit { continuation } => store.emit_store.insert_probe(Box::new(*continuation)),
        }
    }

    pub const fn cont_tag(&self) -> ContTag {
        match self {
            Self::Outermost => ContTag::Outermost,
            Self::Dummy => ContTag::Dummy,
            Self::Error => ContTag::Error,
            Self::Terminal => ContTag::Terminal,
            Self::Call0 {
                saved_env: _,
                continuation: _,
            } => ContTag::Call0,
            Self::Call {
                unevaled_arg: _,
                saved_env: _,
                continuation: _,
            } => ContTag::Call,
            Self::Call2 {
                function: _,
                saved_env: _,
                continuation: _,
            } => ContTag::Call2,
            Self::Tail {
                saved_env: _,
                continuation: _,
            } => ContTag::Tail,
            Self::Lookup {
                saved_env: _,
                continuation: _,
            } => ContTag::Lookup,
            Self::Unop {
                operator: _,
                continuation: _,
            } => ContTag::Unop,
            Self::Binop {
                operator: _,
                saved_env: _,
                unevaled_args: _,
                continuation: _,
            } => ContTag::Binop,
            Self::Binop2 {
                operator: _,
                evaled_arg: _,
                continuation: _,
            } => ContTag::Binop2,
            Self::If {
                unevaled_args: _,
                continuation: _,
            } => ContTag::If,
            Self::Let {
                var: _,
                body: _,
                saved_env: _,
                continuation: _,
            } => ContTag::Let,
            Self::LetRec {
                var: _,
                body: _,
                saved_env: _,
                continuation: _,
            } => ContTag::LetRec,
            Self::Emit { continuation: _ } => ContTag::Emit,
        }
    }
    pub fn get_simple_cont(&self) -> ContPtr<F> {
        match self {
            Self::Outermost | Self::Dummy | Self::Error | Self::Terminal => {
                ContPtr::null(self.cont_tag())
            }

            _ => unreachable!("Not a simple Continuation: {:?}", self),
        }
    }
}
