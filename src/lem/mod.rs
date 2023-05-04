mod ptr;
mod store;
mod tag;

use std::collections::{BTreeMap, HashMap};

use crate::field::LurkField;

use self::{ptr::Ptr, store::Store, tag::Tag};

#[derive(PartialEq, Clone, Copy)]
pub struct MetaPtr<'a>(&'a str);

impl<'a> MetaPtr<'a> {
    #[inline]
    pub fn name(self) -> &'a str {
        self.0
    }
}

#[derive(Clone)]
pub enum OP<'a, F: LurkField> {
    Set(MetaPtr<'a>, F, F),
    Copy(MetaPtr<'a>, MetaPtr<'a>),
    HashFPtr(F, MetaPtr<'a>, F, MetaPtr<'a>),
    Hash2Ptrs(F, MetaPtr<'a>, [MetaPtr<'a>; 2]),
    Hash3Ptrs(F, MetaPtr<'a>, [MetaPtr<'a>; 3]),
    Hash4Ptrs(F, MetaPtr<'a>, [MetaPtr<'a>; 4]),
    CarCdr(MetaPtr<'a>, MetaPtr<'a>, MetaPtr<'a>), // car, cdr, cons src
    MatchTag(MetaPtr<'a>, BTreeMap<F, OP<'a, F>>, Box<OP<'a, F>>),
    Err(&'a str),
    Seq(Vec<OP<'a, F>>),
}

pub struct LEM<'a, F: LurkField> {
    input: [&'a str; 3],
    output: [&'a str; 3],
    op: OP<'a, F>,
}

impl<'a, F: LurkField + std::cmp::Ord + std::hash::Hash> LEM<'a, F> {
    pub fn assert_tag_eq(ptr: MetaPtr<'a>, val: F, ff: OP<'a, F>, tt: OP<'a, F>) -> OP<'a, F> {
        let mut map = BTreeMap::new();
        map.insert(val, tt);
        OP::MatchTag(ptr, map, Box::new(ff))
    }

    pub fn assert_tag_or(
        ptr: MetaPtr<'a>,
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

    pub fn assert_list(ptr: MetaPtr<'a>, ff: OP<'a, F>, tt: OP<'a, F>) -> OP<'a, F> {
        Self::assert_tag_or(ptr, Tag::Cons.to_field(), Tag::Nil.to_field(), ff, tt)
    }

    pub fn mk_comm(o: &'a str, s: F, i: MetaPtr<'a>) -> OP<'a, F> {
        OP::HashFPtr(Tag::Comm.to_field(), MetaPtr(o), s, i)
    }

    pub fn mk_cons(o: &'a str, i: [MetaPtr<'a>; 2]) -> OP<'a, F> {
        OP::Hash2Ptrs(Tag::Cons.to_field(), MetaPtr(o), i)
    }

    pub fn mk_strcons(o: &'a str, i: [MetaPtr<'a>; 2]) -> OP<'a, F> {
        Self::assert_tag_eq(
            i[0],
            Tag::Char.to_field(),
            OP::Err("strcons requires a char as the first argument"),
            Self::assert_tag_eq(
                i[1],
                Tag::Str.to_field(),
                OP::Err("strcons requires a str as the second argument"),
                OP::Hash2Ptrs(Tag::Str.to_field(), MetaPtr(o), i),
            ),
        )
    }

    pub fn mk_fun(o: &'a str, i: [MetaPtr<'a>; 3]) -> OP<'a, F> {
        Self::assert_list(
            i[0],
            OP::Err("The arguments must be a list"),
            Self::assert_list(
                i[2],
                OP::Err("The closed env must be a list"),
                OP::Hash3Ptrs(Tag::Fun.to_field(), MetaPtr(o), i),
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
        // TODO: assert that all tag field elements are in range
        // TODO: assert that used pointers have been previously defined
        // TODO: assert that input pointers aren't overwritten
        // TODO: assert that no pointer is overwritten within a match arm
        // TODO: assert that all input pointers are used
        // TODO: assert that all output pointers are defined
    }

    pub fn run(&self, i: [Ptr; 3], map: &mut HashMap<&'a str, Ptr>, store: &mut Store<F>) {
        map.insert(self.input[0], i[0]);
        map.insert(self.input[1], i[1]);
        map.insert(self.input[2], i[2]);
        let mut stack: Vec<&OP<'a, F>> = vec![&self.op];
        while let Some(op) = stack.pop() {
            match op {
                OP::HashFPtr(tag, dst, sct, src) => {
                    let src_ptr = map.get(src.name()).unwrap();
                    let (idx, _) = store.f_ptr_store.insert_full((*sct, *src_ptr));
                    let dst_ptr = Ptr {
                        tag: Tag::from_field(*tag).unwrap(),
                        idx,
                    };
                    map.insert(dst.name(), dst_ptr);
                }
                OP::Hash2Ptrs(tag, dst, src) => {
                    let src_ptr1 = map.get(src[0].name()).unwrap();
                    let src_ptr2 = map.get(src[1].name()).unwrap();
                    let (idx, _) = store.ptr2_store.insert_full((*src_ptr1, *src_ptr2));
                    let dst_ptr = Ptr {
                        tag: Tag::from_field(*tag).unwrap(),
                        idx,
                    };
                    map.insert(dst.name(), dst_ptr);
                }
                OP::Hash3Ptrs(tag, dst, src) => {
                    let src_ptr1 = map.get(src[0].name()).unwrap();
                    let src_ptr2 = map.get(src[1].name()).unwrap();
                    let src_ptr3 = map.get(src[2].name()).unwrap();
                    let (idx, _) = store
                        .ptr3_store
                        .insert_full((*src_ptr1, *src_ptr2, *src_ptr3));
                    let dst_ptr = Ptr {
                        tag: Tag::from_field(*tag).unwrap(),
                        idx,
                    };
                    map.insert(dst.name(), dst_ptr);
                }
                OP::Hash4Ptrs(tag, dst, src) => {
                    let src_ptr1 = map.get(src[0].name()).unwrap();
                    let src_ptr2 = map.get(src[1].name()).unwrap();
                    let src_ptr3 = map.get(src[2].name()).unwrap();
                    let src_ptr4 = map.get(src[3].name()).unwrap();
                    let (idx, _) = store
                        .ptr4_store
                        .insert_full((*src_ptr1, *src_ptr2, *src_ptr3, *src_ptr4));
                    let dst_ptr = Ptr {
                        tag: Tag::from_field(*tag).unwrap(),
                        idx,
                    };
                    map.insert(dst.name(), dst_ptr);
                }
                OP::Seq(ops) => stack.extend(ops.iter().rev()),
                _ => todo!(),
            }
        }
    }
}

pub fn step<'a, F: LurkField + std::cmp::Ord>() -> LEM<'a, F> {
    let input = ["expr_in", "env_in", "cont_in"];
    let output = ["expr_out", "env_out", "cont_out"];
    let op = OP::MatchTag(
        MetaPtr("expr_in"),
        {
            let mut match_map = BTreeMap::default();
            match_map.insert(
                Tag::Num.to_field(),
                OP::MatchTag(
                    MetaPtr("cont_in"),
                    {
                        let mut match_map = BTreeMap::default();
                        match_map.insert(
                            Tag::Outermost.to_field(),
                            OP::Seq(vec![
                                OP::Copy(MetaPtr("expr_out"), MetaPtr("expr_in")),
                                OP::Copy(MetaPtr("env_out"), MetaPtr("env_in")),
                                OP::Set(MetaPtr("cont_out"), Tag::Terminal.to_field(), F::zero()),
                            ]),
                        );
                        match_map
                    },
                    Box::new(OP::Err("todo")),
                ),
            );
            match_map
        },
        Box::new(OP::Err("todo")),
    );
    LEM { input, output, op }
}
