use std::collections::BTreeMap;

use crate::field::LurkField;

#[derive(PartialEq, Clone)]
pub struct MetaPtr<'a>(&'a str);

#[derive(Clone)]
pub enum OP<'a, F: LurkField> {
    HashFPtr(F, MetaPtr<'a>, &'a F, &'a MetaPtr<'a>),
    Hash2Ptrs(F, MetaPtr<'a>, [&'a MetaPtr<'a>; 2]),
    Hash3Ptrs(F, MetaPtr<'a>, [&'a MetaPtr<'a>; 3]),
    Hash4Ptrs(F, MetaPtr<'a>, [&'a MetaPtr<'a>; 4]),
    CarCdr(MetaPtr<'a>, MetaPtr<'a>, &'a MetaPtr<'a>), // car, cdr, cons src
    MatchTag(&'a MetaPtr<'a>, BTreeMap<F, OP<'a, F>>, Box<OP<'a, F>>),
    Err(&'a str),
    Seq(Vec<OP<'a, F>>),
}

pub struct LEM<'a, F: LurkField> {
    input: [MetaPtr<'a>; 3],
    output: [MetaPtr<'a>; 3],
    op: OP<'a, F>,
}

pub enum ExprTag {
    Nil,
    Num,
    U64,
    Char,
    Str,
    Comm,
    Fun,
    Cons,
    Name,
    Sym,
    Key,
    Thunk,
}

impl ExprTag {
    pub fn to_field<F: LurkField>(self) -> F {
        todo!()
    }
}

pub enum ContTag {}

impl ContTag {
    pub fn to_field<F: LurkField>(self) -> F {
        todo!()
    }
}

impl<'a, F: LurkField + std::cmp::Ord> LEM<'a, F> {
    pub fn assert_tag_eq(ptr: &'a MetaPtr<'a>, val: F, ff: OP<'a, F>, tt: OP<'a, F>) -> OP<'a, F> {
        let mut map = BTreeMap::new();
        map.insert(val, tt);
        OP::MatchTag(ptr, map, Box::new(ff))
    }

    pub fn assert_tag_or(
        ptr: &'a MetaPtr<'a>,
        val1: F,
        val2: F,
        ff: OP<'a, F>,
        tt: OP<'a, F>,
    ) -> OP<'a, F> {
        let mut map = BTreeMap::new();
        map.insert(val1, tt.clone());
        map.insert(val2, tt);
        OP::MatchTag(ptr, map, Box::new(ff))
    }

    pub fn assert_list(ptr: &'a MetaPtr<'a>, ff: OP<'a, F>, tt: OP<'a, F>) -> OP<'a, F> {
        Self::assert_tag_or(
            ptr,
            ExprTag::Cons.to_field(),
            ExprTag::Nil.to_field(),
            ff,
            tt,
        )
    }

    pub fn mk_comm(o: &'a str, s: &'a F, i: &'a MetaPtr<'a>) -> OP<'a, F> {
        OP::HashFPtr(ExprTag::Comm.to_field(), MetaPtr(o), s, i)
    }

    pub fn mk_cons(o: &'a str, i: [&'a MetaPtr<'a>; 2]) -> OP<'a, F> {
        OP::Hash2Ptrs(ExprTag::Cons.to_field(), MetaPtr(o), i)
    }

    pub fn mk_strcons(o: &'a str, i: [&'a MetaPtr<'a>; 2]) -> OP<'a, F> {
        Self::assert_tag_eq(
            &i[0],
            ExprTag::Char.to_field(),
            OP::Err("strcons requires a char as the first argument"),
            Self::assert_tag_eq(
                &i[1],
                ExprTag::Str.to_field(),
                OP::Err("strcons requires a str as the second argument"),
                OP::Hash2Ptrs(ExprTag::Str.to_field(), MetaPtr(o), i),
            ),
        )
    }

    pub fn mk_fun(o: &'a str, i: [&'a MetaPtr<'a>; 3]) -> OP<'a, F> {
        Self::assert_list(
            &i[0],
            OP::Err("The arguments must be a list"),
            Self::assert_list(
                &i[2],
                OP::Err("The closed env must be a list"),
                OP::Hash3Ptrs(ExprTag::Fun.to_field(), MetaPtr(o), i),
            ),
        )
    }

    pub fn check(&self) {
        for s in self.input.iter() {
            assert!(
                !self.output.contains(&s),
                "Input and output must be disjoint"
            )
        }
        // TODO: assert that used pointers have been previously defined
        // TODO: assert that input pointers aren't overwritten
        // TODO: assert that no pointer is overwritten within a match arm
        // TODO: assert that all input pointers are used
        // TODO: assert that all output pointers are defined
    }
}
