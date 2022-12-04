use crate::ptr::Ptr;
use lurk_ff::field::LurkField;
use lurk_ff::tag::{ExprTag, Op1Tag, Op2Tag};

use crate::hash::PoseidonCache;
// user-level expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<F: LurkField> {
    ConsNil,
    Cons(Ptr<F>, Ptr<F>),        // car, cdr
    Comm(F, Ptr<F>),             // secret, val
    SymNil,                      //
    SymCons(Ptr<F>, Ptr<F>),     // head, tail
    Keyword(Ptr<F>),             // symbol
    StrNil,                      //
    StrCons(Ptr<F>, Ptr<F>),     // head, tail
    Thunk(Ptr<F>, Ptr<F>),       // val, cont
    Fun(Ptr<F>, Ptr<F>, Ptr<F>), // arg, body, env
    Num(F),                      //
    Char(F),                     //
    U64(F),                      //
    Map(Ptr<F>),                 // symbol
    Link(Ptr<F>, Ptr<F>),        // ctx, data
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cont<F: LurkField> {
    Outermost,
    Call(Ptr<F>, Ptr<F>, Ptr<F>),  // arg, env, cont
    Call0(Ptr<F>, Ptr<F>),         // env, cont
    Call2(Ptr<F>, Ptr<F>, Ptr<F>), // fun, env, cont
    Tail(Ptr<F>, Ptr<F>),          // env, cont
    Error,
    Lookup(Ptr<F>, Ptr<F>),                 // env, cont
    Unop(Op1Tag, Ptr<F>),                   // op, cont
    Binop(Op2Tag, Ptr<F>, Ptr<F>, Ptr<F>),  // op, env, args cont
    Binop2(Op2Tag, Ptr<F>, Ptr<F>),         // op, arg, cont
    If(Ptr<F>, Ptr<F>),                     // args, cont
    Let(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>),    // var, body, env, cont
    LetRec(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>), // var, body, env, cont
    Emit(Ptr<F>),                           // cont
    Dummy,
    Terminal,
}

impl<'a, F: LurkField> Expr<F> {
    /// All the `Ptr`s directly reachable from `expr`, if any.
    pub fn child_ptrs(expr: &Expr<F>) -> Vec<Ptr<F>> {
        match expr {
            Expr::ConsNil => vec![],
            Expr::Cons(car, cdr) => vec![*car, *cdr],
            Expr::Comm(_, payload) => vec![*payload],
            Expr::SymNil => vec![],
            Expr::SymCons(head, tail) => vec![*head, *tail],
            Expr::Keyword(symbol) => vec![*symbol],
            Expr::Fun(arg, body, closed_env) => vec![*arg, *body, *closed_env],
            Expr::Num(_) => vec![],
            Expr::StrNil => vec![],
            Expr::StrCons(head, tail) => vec![*head, *tail],
            Expr::Thunk(val, cont) => vec![*val, *cont],
            Expr::Char(_) => vec![],
            Expr::U64(_) => vec![],
            Expr::Map(map) => vec![*map],
            Expr::Link(ctx, data) => vec![*ctx, *data],
        }
    }

    pub fn ptr(&self, cache: &PoseidonCache<F>) -> Ptr<F> {
        match self {
            Expr::ConsNil => Ptr {
                tag: F::make_expr_tag(ExprTag::Cons),
                val: F::zero(),
            },
            Expr::Cons(car, cdr) => Ptr {
                tag: F::make_expr_tag(ExprTag::Cons),
                val: cache.hash4(&[
                    F::from_tag_unchecked(car.tag),
                    car.val,
                    F::from_tag_unchecked(cdr.tag),
                    cdr.val,
                ]),
            },
            Expr::Comm(secret, val) => Ptr {
                tag: F::make_expr_tag(ExprTag::Comm),
                val: cache.hash3(&[*secret, F::from_tag_unchecked(val.tag), val.val]),
            },
            Expr::SymNil => Ptr {
                tag: F::make_expr_tag(ExprTag::Sym),
                val: F::zero(),
            },
            Expr::SymCons(head, tail) => Ptr {
                tag: F::make_expr_tag(ExprTag::Sym),
                val: cache.hash4(&[
                    F::from_tag_unchecked(head.tag),
                    head.val,
                    F::from_tag_unchecked(tail.tag),
                    tail.val,
                ]),
            },
            Expr::Keyword(symbol) => Ptr {
                tag: F::make_expr_tag(ExprTag::Key),
                val: symbol.val,
            },
            Expr::Fun(arg, body, env) => Ptr {
                tag: F::make_expr_tag(ExprTag::Fun),
                val: cache.hash6(&[
                    F::from_tag_unchecked(arg.tag),
                    arg.val,
                    F::from_tag_unchecked(body.tag),
                    body.val,
                    F::from_tag_unchecked(env.tag),
                    env.val,
                ]),
            },
            Expr::Num(f) => Ptr {
                tag: F::make_expr_tag(ExprTag::Num),
                val: *f,
            },
            Expr::StrNil => Ptr {
                tag: F::make_expr_tag(ExprTag::Str),
                val: F::zero(),
            },
            Expr::StrCons(head, tail) => Ptr {
                tag: F::make_expr_tag(ExprTag::Str),
                val: cache.hash4(&[
                    F::from_tag_unchecked(head.tag),
                    head.val,
                    F::from_tag_unchecked(tail.tag),
                    tail.val,
                ]),
            },
            Expr::Char(f) => Ptr {
                tag: F::make_expr_tag(ExprTag::Char),
                val: *f,
            },
            Expr::U64(f) => Ptr {
                tag: F::make_expr_tag(ExprTag::U64),
                val: *f,
            },
            Expr::Thunk(val, cont) => Ptr {
                tag: F::make_expr_tag(ExprTag::Thunk),
                val: cache.hash4(&[
                    F::from_tag_unchecked(val.tag),
                    val.val,
                    F::from_tag_unchecked(cont.tag),
                    cont.val,
                ]),
            },
            Expr::Map(map) => Ptr {
                tag: F::make_expr_tag(ExprTag::Map),
                val: map.val,
            },
            Expr::Link(ctx, data) => Ptr {
                tag: F::make_expr_tag(ExprTag::Link),
                val: cache.hash4(&[
                    F::from_tag_unchecked(ctx.tag),
                    ctx.val,
                    F::from_tag_unchecked(data.tag),
                    data.val,
                ]),
            },
        }
    }
}
