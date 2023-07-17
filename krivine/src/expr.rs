use crate::ptr::{Ptr, ZPtr};
use crate::tag::Tag;
use lurk::field::LurkField;
use lurk::hash::PoseidonCache;

pub enum Expr<F: LurkField> {
    Var(usize),
    Lam(Ptr<F>),
    App(Ptr<F>, Ptr<F>),
}

pub enum ZExpr<F: LurkField> {
    Var(F),
    Lam(ZPtr<F>),
    App(ZPtr<F>, ZPtr<F>),
}

impl<F: LurkField> ZExpr<F> {
    pub fn z_ptr(&self, cache: &PoseidonCache<F>) -> ZPtr<F> {
        match self {
            Self::Var(f) => ZPtr {
                tag: Tag::Var,
                val: *f,
            },
            // TODO: Needs hash of arity 2
            Self::Lam(bod) => ZPtr {
                tag: Tag::Lam,
                val: cache.hash3(&[bod.tag.to_field(), bod.val, F::ZERO]),
            },
            Self::App(fun, bod) => ZPtr {
                tag: Tag::App,
                val: cache.hash4(&[fun.tag.to_field(), fun.val, bod.tag.to_field(), bod.val]),
            },
        }
    }
}
