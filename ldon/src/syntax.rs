use crate::hash::PoseidonCache;
use crate::parser::position::Pos;
use crate::store::Store;
use lurk_ff::field::LurkField;
use std::collections::BTreeMap;
use std::fmt;

// LDON syntax
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Syn<F: LurkField> {
    Num(Pos, F),               // 1, 0xff
    U64(Pos, u64),             // 1u64, 0xffu64
    Symbol(Pos, Vec<String>),  // _ .foo.bar.baz.
    Keyword(Pos, Vec<String>), // :_ :lambda, :lurk:lambda
    String(Pos, String),       // "foobar", "foo\nbar"
    Char(Pos, char),           // 'a'
    // The end term of an improper list is not allowed to be a list
    List(Pos, Vec<Syn<F>>, Option<Box<Syn<F>>>), // (1 2 3) (1 2 . 3)
    // Note: The assoc-list in a Syn::Map must be in canonical order according
    // to the order of key's corresponding Ptr<F>.
    Map(Pos, Vec<(Syn<F>, Syn<F>)>),  // { foo: 1, blue: true }
    Link(Pos, Box<Syn<F>>, Vec<u64>), // sha256::ffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
}

impl<F: LurkField> Syn<F> {
    // Syn's Ord impl has bad asymptotics since it generates a fresh poseidon cache.
    // In those cases, `cached_cmp` allows for cache preserving comparisons
    pub fn cached_cmp(&self, other: &Self, cache: &PoseidonCache<F>) -> core::cmp::Ordering {
        let mut store = Store::new();
        let self_ptr = store.intern_syn(&cache, self);
        let other_ptr = store.intern_syn(&cache, other);
        self_ptr.cmp(&other_ptr)
    }
}

impl<F: LurkField> PartialOrd for Syn<F> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cached_cmp(other, &PoseidonCache::default()))
    }
}

impl<F: LurkField> Ord for Syn<F> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.cached_cmp(other, &PoseidonCache::default())
    }
}

impl<F: LurkField> fmt::Display for Syn<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Num(_, x) => {
                let le_bytes = x.to_repr();
                write!(f, "0x")?;
                for &b in le_bytes.as_ref().iter().rev() {
                    write!(f, "{:02x}", b)?;
                }
                Ok(())
            }
            Self::U64(_, x) => write!(f, "{}u64", x),
            Self::Symbol(_, xs) => {
                if xs.is_empty() {
                    write!(f, ".")
                } else {
                    for x in xs {
                        write!(f, ".{}", x)?;
                    }
                    Ok(())
                }
            }
            Self::Keyword(_, xs) => {
                if xs.is_empty() {
                    write!(f, ":")
                } else {
                    for x in xs {
                        write!(f, ":{}", x)?;
                    }
                    Ok(())
                }
            }
            Self::String(_, x) => write!(f, "\"{}\"", x),
            Self::Char(_, x) => write!(f, "'{}'", x),
            Self::List(_, xs, end) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    if let None = iter.peek() {
                        match end {
                            Some(end) => write!(f, "{} . {}", x, end)?,
                            None => write!(f, "{}", x)?,
                        }
                    } else {
                        write!(f, "{} ", x)?;
                    }
                }
                write!(f, ")")
            }
            Self::Map(_, xs) => {
                let mut iter = xs.iter().peekable();
                write!(f, "{{")?;
                while let Some((key, val)) = iter.next() {
                    if let None = iter.peek() {
                        write!(f, "{}: {}", key, val)?;
                    } else {
                        write!(f, "{}: {}, ", key, val)?;
                    }
                }
                write!(f, "}}")
            }
            Self::Link(_, ctx, xs) => {
                write!(f, "{}::", ctx)?;
                for x in xs {
                    write!(f, "{:016x}", x)?;
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use blstrs::Scalar as Fr;

    use quickcheck::{Arbitrary, Gen};

    use crate::test::frequency;
    use im::Vector;

    //#[test]
    //fn display_link() {
    //    println!(
    //        "{}",
    //        Syn::<Fr>::Link(
    //            Pos::No,
    //            Box::new(Syn::Symbol(Pos::No, vec![Sym::Sym("sha256".to_string())])),
    //            vec![u64::MAX, u64::MAX, u64::MAX, u64::MAX]
    //        )
    //    );
    //    assert!(false)
    //}

    // For working around the orphan trait impl rule
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct FWrap<F: LurkField>(pub F);

    impl<F: LurkField> Arbitrary for FWrap<F> {
        fn arbitrary(_: &mut Gen) -> Self {
            let f = F::random(rand::thread_rng());
            FWrap(f)
        }
    }

    impl Syn<Fr> {
        fn arbitrary_syn(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Syn<Fr>>)> = vec![
                (100, Box::new(|g| Self::Num(Pos::No, FWrap::arbitrary(g).0))),
                (100, Box::new(|g| Self::U64(Pos::No, u64::arbitrary(g)))),
                (100, Box::new(|g| Self::Char(Pos::No, char::arbitrary(g)))),
                (
                    100,
                    Box::new(|g| Self::String(Pos::No, Self::arbitrary_string(g))),
                ),
                (
                    50,
                    Box::new(|g| Self::Symbol(Pos::No, Self::arbitrary_symbol(g))),
                ),
                (
                    50,
                    Box::new(|g| Self::Keyword(Pos::No, Self::arbitrary_symbol(g))),
                ),
                (50, Box::new(|g| Self::arbitrary_list(g))),
                (50, Box::new(|g| Self::arbitrary_map(g))),
            ];
            frequency(g, input)
        }

        fn arbitrary_string(g: &mut Gen) -> String {
            let num_chars = usize::arbitrary(g) % 5;
            let mut s = String::new();
            for _ in 0..num_chars {
                let c = char::arbitrary(g);
                s.push(c);
            }
            s
        }

        fn arbitrary_symbol(g: &mut Gen) -> Vec<String> {
            let num_syms = usize::arbitrary(g) % 3;
            let mut sym = Vec::new();
            for _ in 0..num_syms {
                let s = Self::arbitrary_string(g);
                sym.push(s);
            }
            sym
        }

        fn arbitrary_list(g: &mut Gen) -> Self {
            let num_exprs: usize = Arbitrary::arbitrary(g);
            let num_exprs = num_exprs % 3;
            let mut exprs = Vec::new();
            for _ in 0..num_exprs {
                let expr = Syn::arbitrary_syn(g);
                exprs.push(expr);
            }
            let improper: bool = Arbitrary::arbitrary(g);
            let end = Syn::arbitrary_syn(g);
            if improper && num_exprs != 0 && !matches!(end, Syn::List(_, _, _)) {
                Syn::List(Pos::No, exprs, Some(Box::new(end)))
            } else {
                Syn::List(Pos::No, exprs, None)
            }
        }

        fn arbitrary_map(g: &mut Gen) -> Self {
            let num_exprs: usize = Arbitrary::arbitrary(g);
            let num_exprs = num_exprs % 3;
            // we use a BTreeMap to get the right ordering
            let mut map = BTreeMap::new();
            for _ in 0..num_exprs {
                let key = Syn::arbitrary_syn(g);
                let val = Syn::arbitrary_syn(g);
                map.insert(key, val);
            }
            Syn::Map(Pos::No, map.into_iter().collect())
        }
    }

    impl Arbitrary for Syn<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            Syn::arbitrary_syn(g)
        }
    }
    #[quickcheck]
    fn prop_syn_generates(syn: Syn<Fr>) -> bool {
        //println!("-------------");
        let mut store1 = Store::<Fr>::default();
        let cache = PoseidonCache::default();
        let ptr1 = store1.intern_syn(&cache, &syn);
        true
    }
}
