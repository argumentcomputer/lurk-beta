use crate::lem::AVec;

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct MatchMap<A, B> {
    pub cases: Vec<(AVec<A>, B)>,
    pub default: Option<Box<B>>,
}

impl<A: PartialEq, B> MatchMap<A, B> {
    pub fn get<'a>(&'a self, val: &A) -> Option<&'a B> {
        for (xs, y) in &self.cases {
            for x in xs.iter() {
                if x == val {
                    return Some(y);
                }
            }
        }
        self.default.as_ref().map(|y| &**y)
    }
}
