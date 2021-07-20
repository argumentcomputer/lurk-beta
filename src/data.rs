use bellperson::bls::{Bls12, Fr, FrRepr};
use core::hash::Hash;
use ff::{Field, PrimeField};
use generic_array::typenum::{U16, U2, U4, U8};
use itertools::Itertools;
use lazy_static::lazy_static;
use neptune::{hash_type::HashType, poseidon::Poseidon, poseidon::PoseidonConstants, Strength};
use std::collections::HashMap;
use std::hash::Hasher;

lazy_static! {
    pub static ref POSEIDON_CONSTANTS_2: PoseidonConstants::<Bls12, U2> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_4: PoseidonConstants::<Bls12, U4> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_8: PoseidonConstants::<Bls12, U8> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_16: PoseidonConstants::<Bls12, U16> =
        PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_VARIABLE: PoseidonConstants::<Bls12, U16> =
        PoseidonConstants::new_with_strength_and_type(Strength::Standard, HashType::VariableLength);
}

/// Order of these tag variants is significant, since it will be concretely
/// encoded into content-addressable data structures.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum Tag {
    Nil,
    Cons,
    Sym,
    Fun,
    Num,
    Cont,
}

pub fn fr_from_u64<Fr: PrimeField>(i: u64) -> Fr {
    Fr::from_repr(<Fr::Repr as From<u64>>::from(i)).unwrap()
}
pub fn fr_from_u64s(parts: [u64; 4]) -> Fr {
    Fr::from_repr(FrRepr(parts)).unwrap()
}

impl Tag {
    fn fr(self) -> Fr {
        fr_from_u64(self as u64)
    }
}

impl From<Fr> for Tag {
    fn from(fr: Fr) -> Self {
        unimplemented!();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
// This should probably be TaggedPointer, or something.
pub struct TaggedHash {
    tag: Fr,
    // Hash is misnamed. It could be a hash, or it could be an immediate value.
    hash: Fr,
}

impl Hash for TaggedHash {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.into_repr().0.hash(state);
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum Expression {
    Nil,
    Cons(TaggedHash, TaggedHash),
    Sym(String),
    Fun(),
    Num(Fr),
    Cont(),
}

fn binary_hash(a: &TaggedHash, b: &TaggedHash) -> Fr {
    let preimage = vec![a.tag, a.hash, b.tag, b.hash];
    Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_4).hash()
}

fn oct_hash(preimage: &[Fr]) -> Fr {
    Poseidon::new_with_preimage(preimage, &POSEIDON_CONSTANTS_8).hash()
}

fn hash_string(s: &str) -> Fr {
    // We should use HashType::VariableLength, once supported.
    // The following is just quick and dirty, but should be unique.
    let mut preimage = vec![Fr::zero(); 8];
    let mut x = fr_from_u64(s.len() as u64);
    s.chars()
        .map(|c| fr_from_u64(c.into()))
        .chunks(7)
        .into_iter()
        .for_each(|mut chunk| {
            preimage[0] = x;
            for i in 1..7 {
                chunk.next().map(|c| preimage[i] = c);
            }
            x = oct_hash(&preimage);
        });
    x
}

impl Tagged for Expression {
    fn tag(&self) -> Tag {
        match self {
            Nil => Tag::Nil,
            Cons(_, _) => Tag::Cons,
            Sym(_) => Tag::Sym,
            Fun() => Tag::Fun,
            Num(_) => Tag::Num,
            Cont() => Tag::Cont,
        }
    }
}

impl Expression {
    fn get_hash(&self) -> Fr {
        match self {
            Nil => hash_string("NIL"),
            Cons(car, cdr) => binary_hash(car, cdr),
            Sym(s) => hash_string(s),
            Fun() => todo!(),
            Num(fr) => *fr, // Nums are immediate.
            Cont() => todo!(),
        }
    }

    pub fn tagged_hash(&self) -> TaggedHash {
        let tag = self.tag().fr();
        let hash = self.get_hash();

        TaggedHash { tag, hash }
    }

    fn read_sym(s: &str) -> Expression {
        Sym(s.to_uppercase())
    }

    pub fn cons(a: &Expression, b: &Expression) -> Expression {
        Cons(a.tagged_hash(), b.tagged_hash())
    }

    pub fn num(n: u64) -> Expression {
        Num(fr_from_u64(n))
    }
}

use Expression::*;

pub trait Tagged {
    fn tag(&self) -> Tag;
    fn tag_fr(&self) -> Fr {
        self.tag().fr()
    }
}

pub struct Num {
    value: Fr,
}

impl Tagged for Num {
    fn tag(&self) -> Tag {
        Tag::Num
    }
}

#[derive(Clone, Debug, Default)]
pub struct Store {
    map: HashMap<TaggedHash, Expression>,
}

impl Store {
    pub fn fetch(&self, t: TaggedHash) -> Option<Expression> {
        match t.tag {
            // Nil has a unique identity.
            tag if tag == Tag::Nil.fr() => Some(Expression::Nil),
            // Nums are immediate so not looked up in map.
            tag if tag == Tag::Num.fr() => Some(Expression::Num(t.hash)),
            _ => self.map.get(&t).map(|x| x.clone()),
        }
    }

    pub fn store(&mut self, exp: &Expression) {
        self.map.entry(exp.tagged_hash()).or_insert(exp.clone());
    }

    // Consider a secondary map/index on symbol names, which would be proper
    // interning and save expensive rehashing each time. The same potentially
    // goes for other types.
    pub fn intern(&mut self, s: &str) -> Expression {
        let sym = Expression::read_sym(s);
        self.store(&sym);
        sym
    }

    pub fn cons(&mut self, car: &Expression, cdr: &Expression) -> Expression {
        let cons = Expression::cons(car, cdr);
        self.store(&cons);
        cons
    }

    pub fn car_cdr(&self, expr: &Expression) -> (Expression, Expression) {
        match expr {
            Cons(car, cdr) => (
                self.fetch(*car).expect("Car not found!").clone(),
                self.fetch(*cdr).expect("Cdr not found!").clone(),
            ),
            _ => panic!("Can only extract car_cdr from a Cons."),
        }
    }

    pub fn car(&self, expr: &Expression) -> Expression {
        self.car_cdr(expr).0
    }

    pub fn cdr(&self, expr: &Expression) -> Expression {
        self.car_cdr(expr).1
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn tag_vals() {
        assert_eq!(0, Tag::Nil as u64);
        assert_eq!(1, Tag::Cons as u64);
        assert_eq!(2, Tag::Sym as u64);
        assert_eq!(3, Tag::Fun as u64);
        assert_eq!(4, Tag::Num as u64);
        assert_eq!(5, Tag::Cont as u64);
    }

    #[test]
    fn test_hash_string() {
        assert_eq!(
            fr_from_u64s([
                0x5c03e517bec087a0,
                0xc22861c4b56986b2,
                0x730bf8397a7a2cf2,
                0x4bb2bffada9d35a2
            ]),
            hash_string(&"Test"),
        );

        assert_eq!(
            fr_from_u64s([
                0xaece3618ecf6d992,
                0xfccb6c0141aff847,
                0xc19882347797fbab,
                0x33e4e3e92bc14968
            ]),
            hash_string(&"NIL")
        );

        assert_eq!(
            fr_from_u64s([
                0xcd414517f70c8562,
                0x8df95fcf0e22705a,
                0xf14f6ff8429ddea0,
                0x6e952ecf9358ff3e
            ]),
            hash_string(&"RANDOM")
        );
    }

    #[test]
    fn sym_tagged_hash() {
        let s = Expression::read_sym("bubba");
        let t = s.tagged_hash();
        assert_eq!(Sym("BUBBA".to_string()), s);
        assert_eq!(Tag::Sym.fr(), t.tag);
        assert_eq!(
            fr_from_u64s([
                0x1c3939f30194d3b9,
                0x8e7208d4f2e73ed6,
                0x455900037c586565,
                0x638cabd52a433562
            ]),
            s.get_hash()
        );
    }

    #[test]
    fn nil_tagged_hash() {
        let nil = Expression::Nil;
        let t = nil.tagged_hash();
        assert_eq!(Tag::Nil.fr(), t.tag);
        assert_eq!(hash_string(&"NIL"), nil.get_hash());
        assert_eq!(
            fr_from_u64s([
                0xaece3618ecf6d992,
                0xfccb6c0141aff847,
                0xc19882347797fbab,
                0x33e4e3e92bc14968
            ]),
            nil.get_hash()
        );
    }

    #[test]
    fn cons_tagged_hash() {
        let nil = Expression::Nil;
        let apple = Expression::read_sym("apple");
        let cons = Expression::Cons(apple.tagged_hash(), nil.tagged_hash());
        assert_eq!(cons, Expression::cons(&apple, &nil));
        let t = cons.tagged_hash();
        assert_eq!(Tag::Cons.fr(), t.tag);
        assert_eq!(
            fr_from_u64s([
                0x3c0321b1e4d826b4,
                0x478de3220a74033e,
                0xcb314ea6d44ae65f,
                0x05c60d24e14cf749
            ]),
            cons.get_hash(),
        );
    }

    #[test]
    fn num_tagged_hash() {
        let num = Expression::num(123);
        let t = num.tagged_hash();
        assert_eq!(Expression::Num(fr_from_u64(123)), num);
        assert_eq!(Tag::Num.fr(), t.tag);
        assert_eq!(
            fr_from_u64s([
                0x000000000000007b,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000
            ]),
            num.get_hash()
        );
    }

    #[test]
    fn store() {
        let mut store = Store::default();

        let num = Expression::num(123);
        let num_t = num.tagged_hash();
        store.store(&num);
        let num_again = store.fetch(num_t).unwrap();

        assert_eq!(num, num_again.clone());

        let num2 = Expression::num(123);
    }

    #[test]
    fn equality() {
        let mut store = Store::default();

        let cons1 = Expression::cons(&Expression::num(123), &store.intern("pumpkin"));
        let cons2 = Expression::cons(&Expression::num(123), &store.intern("pumpkin"));

        store.store(&cons1);
        store.store(&cons2);

        assert_eq!(cons1, cons2);
        assert_eq!(store.car(&cons1), store.car(&cons2));
        assert_eq!(store.cdr(&cons1), store.cdr(&cons2));

        let (a, d) = store.car_cdr(&cons1);
        assert_eq!(store.car(&cons1), a);
        assert_eq!(store.cdr(&cons1), d);
    }
}
