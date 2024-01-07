use std::cmp::PartialEq;
use std::marker::PhantomData;

pub mod lang;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Frame<T: Copy, W: Copy, F, C> {
    pub input: T,
    pub output: T,
    pub i: usize,
    pub witness: W,
    pub _p: PhantomData<(C, F)>,
}
