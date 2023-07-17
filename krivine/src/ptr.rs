use lurk::field::LurkField;
use std::marker::PhantomData;

use crate::tag::Tag;

#[derive(Debug)]
pub struct Ptr<F: LurkField> {
    pub tag: Tag,
    pub val: usize,
    pub _f: PhantomData<F>,
}
pub enum RawPtr {
    Null,
    Opaque(usize),
    Index(usize),
}

pub struct ZPtr<F: LurkField> {
    pub tag: Tag,
    pub val: F,
}
