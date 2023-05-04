use super::tag::Tag;

#[derive(Clone, Copy, PartialEq, std::cmp::Eq, Hash)]
pub struct Ptr {
    pub tag: Tag,
    pub idx: usize,
}
