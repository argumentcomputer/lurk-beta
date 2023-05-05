use super::tag::Tag;

#[derive(Clone, Copy, PartialEq, std::cmp::Eq, Hash)]
pub enum PtrVal {
    Idx(usize),
    Null,
}

#[derive(Clone, Copy, PartialEq, std::cmp::Eq, Hash)]
pub struct Ptr {
    pub tag: Tag,
    pub val: PtrVal,
}
