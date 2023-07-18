use crate::expr::Expr;
use crate::ptr::{Ptr, ZPtr};
use crate::tag::Tag;
use lurk::field::LurkField;
use lurk::hash::PoseidonCache;

// an environment is a list of Closures
pub enum Env<F: LurkField> {
    Empty,
    // a head of Closure and tail of Env
    Env(Ptr<F>, Ptr<F>),
}

// a closure is a pair of a term (Ind/Abs/App) and an environemnt
pub struct Closure<F: LurkField> {
    pub term: Ptr<F>,
    pub env: Ptr<F>,
}

// The state of the machine is an expression, a stack of closures and an environment
pub struct State<F: LurkField> {
    pub term: Ptr<F>,  // Ptr to Expr
    pub stack: Env<F>, // Ptr to Env
    pub env: Env<F>,   // Ptr to Env
}

type IndexSet<K> = indexmap::IndexSet<K, ahash::RandomState>;

#[derive(Debug)]
pub struct Store<F: LurkField> {
    pub abs_store: IndexSet<Ptr<F>>,
    pub lam_store: IndexSet<(Ptr<F>, Ptr<F>)>,
    pub env_store: IndexSet<(Ptr<F>, Ptr<F>)>,
    pub closure_store: IndexSet<(Ptr<F>, Ptr<F>)>,
    pub cache: PoseidonCache<F>,
}

//impl<F: LurkField> Store<F> {
//
//
//
//
//}
