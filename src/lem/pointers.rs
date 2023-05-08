use super::tag::Tag;

#[derive(Clone, Copy, PartialEq, std::cmp::Eq, Hash)]
pub enum PtrVal {
    Idx(usize),
    Char(char),
    U64(u64),
    Null,
}

#[derive(Clone, Copy, PartialEq, std::cmp::Eq, Hash)]
pub struct Ptr {
    pub tag: Tag,
    pub val: PtrVal,
}
