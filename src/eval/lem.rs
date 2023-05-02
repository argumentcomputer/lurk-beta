use crate::field::LurkField;

#[derive(PartialEq, Clone)]
pub struct MetaPtr<'a>(&'a str);

pub enum OP<'a, F: LurkField> {
    HashFPtr(F, MetaPtr<'a>, &'a F, &'a MetaPtr<'a>),
    Hash2Ptrs(F, MetaPtr<'a>, [&'a MetaPtr<'a>; 2]),
    Hash3Ptrs(F, MetaPtr<'a>, [&'a MetaPtr<'a>; 3]),
    Hash4Ptrs(F, MetaPtr<'a>, [&'a MetaPtr<'a>; 4]),
    CarCdr(MetaPtr<'a>, MetaPtr<'a>, MetaPtr<'a>), // car, cdr, cons src
    AssertTagEq(&'a MetaPtr<'a>, F, &'a str),
    AssertTagOr(&'a MetaPtr<'a>, F, F, &'a str),
    Seq(Vec<Box<OP<'a, F>>>),
    MatchTag(MetaPtr<'a>, Vec<(F, OP<'a, F>)>, &'a str),
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

impl<'a, F: LurkField> LEM<'a, F> {
    pub fn assert_list(ptr: &'a MetaPtr<'a>, err: &'a str) -> OP<'a, F> {
        OP::AssertTagOr(ptr, ExprTag::Cons.to_field(), ExprTag::Nil.to_field(), err)
    }

    pub fn mk_comm(o: &'a str, s: &'a F, i: &'a MetaPtr<'a>) -> OP<'a, F> {
        OP::HashFPtr(ExprTag::Comm.to_field(), MetaPtr(o), s, i)
    }
    
    pub fn mk_cons(o: &'a str, i: [&'a MetaPtr<'a>; 2]) -> OP<'a, F> {
        OP::Hash2Ptrs(ExprTag::Cons.to_field(), MetaPtr(o), i)
    }
    
    pub fn mk_strcons(o: &'a str, i: [&'a MetaPtr<'a>; 2]) -> OP<'a, F> {
        OP::Seq(vec![
            Box::new(OP::AssertTagEq(&i[0], ExprTag::Char.to_field(), "strcons requires a char as the first argument")),
            Box::new(OP::AssertTagEq(&i[1], ExprTag::Str.to_field(), "strcons requires a str as the second argument")),
            Box::new(OP::Hash2Ptrs(ExprTag::Str.to_field(), MetaPtr(o), i))
        ])
    }

    pub fn mk_fun(o: &'a str, i: [&'a MetaPtr<'a>; 3]) -> OP<'a, F> {
        OP::Seq(vec![
            Box::new(Self::assert_list(i[0], "The arguments must be a list")),
            Box::new(Self::assert_list(i[2], "The closed env must be a list")),
            Box::new(OP::Hash3Ptrs(ExprTag::Fun.to_field(), MetaPtr(o), i))
        ])
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
