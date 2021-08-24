use bellperson::bls::{Bls12, Fr, FrRepr};
use core::hash::Hash;
use ff::{Field, PrimeField};
use generic_array::typenum::{U10, U11, U16, U2, U3, U4, U5, U6, U7, U8, U9};
use itertools::Itertools;
use lazy_static::lazy_static;
use neptune::{hash_type::HashType, poseidon::Poseidon, poseidon::PoseidonConstants, Strength};
use std::collections::HashMap;
use std::hash::Hasher;
use std::iter::Peekable;
use std::string::ToString;

lazy_static! {
    pub static ref POSEIDON_CONSTANTS_2: PoseidonConstants::<Bls12, U2> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_3: PoseidonConstants::<Bls12, U3> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_4: PoseidonConstants::<Bls12, U4> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_5: PoseidonConstants::<Bls12, U5> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_6: PoseidonConstants::<Bls12, U6> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_7: PoseidonConstants::<Bls12, U7> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_8: PoseidonConstants::<Bls12, U8> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_9: PoseidonConstants::<Bls12, U9> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_10: PoseidonConstants::<Bls12, U10> =
        PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_11: PoseidonConstants::<Bls12, U11> =
        PoseidonConstants::new();
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
    Thunk,
}

/// Order of these tag variants is significant, since it will be concretely
/// encoded into content-addressable data structures.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum BaseContinuationTag {
    //
    Outermost,
    Simple,
    Call,
    Call2,
    Tail,
    Error,
    Lookup,
    Binop,
    Binop2,
    Relop,
    Relop2,
    If,
    Let,
    LetRecStar,
    Dummy,
    Terminal,
}

// For now, partition ContinuationTags into thunks and conts.
// If never used, we can collapse.
// We will likely want both if we ever make continuations (including
// thunks) first-class expressions, though.
impl BaseContinuationTag {
    pub fn cont_tag_val(&self) -> u64 {
        2 * *self as u64
    }

    pub fn cont_tag_fr(&self) -> Fr {
        fr_from_u64(self.cont_tag_val())
    }

    fn thunk_tag_val(&self) -> u64 {
        1 + self.cont_tag_val()
    }

    fn thunk_tag_fr(&self) -> Fr {
        fr_from_u64(self.thunk_tag_val())
    }
}

pub fn fr_from_u64<Fr: PrimeField>(i: u64) -> Fr {
    Fr::from_repr(<Fr::Repr as From<u64>>::from(i)).unwrap()
}
pub fn fr_from_u64s(parts: [u64; 4]) -> Fr {
    Fr::from_repr(FrRepr(parts)).unwrap()
}

impl Tag {
    pub fn fr(self) -> Fr {
        fr_from_u64(self as u64)
    }
}

impl From<Fr> for Tag {
    fn from(_fr: Fr) -> Self {
        unimplemented!();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
// This should probably be TaggedPointer, or something.
pub struct TaggedHash {
    pub tag: Fr,
    // Hash is misnamed. It could be a hash, or it could be an immediate value.
    pub hash: Fr,
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
    Fun(TaggedHash, TaggedHash, TaggedHash), // arg, body, closed env
    Num(Fr),
    Thunk(Thunk),
}

// #[allow(dead_code)]
// pub struct Function {
//     arg: Expression,
//     body: Expression,
//     closed_env: Expression,
// }

#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum Op2 {
    Sum,
    Diff,
    Product,
    Quotient,
}

impl Op2 {
    fn fr(&self) -> Fr {
        fr_from_u64(self.clone() as u64)
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum Rel2 {
    Equal,
}

impl Rel2 {
    fn fr(&self) -> Fr {
        fr_from_u64(self.clone() as u64)
    }
}

// TODO: Unify this with Expression::Thunk. For simplicity, keep separate for now.
// This separateness means that Expression and Continuation have separate namespaces.
// In practice, this means they have distinct tags, and the containing code must know
// statically which is expected.
#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub enum Continuation {
    Outermost,
    Simple(Box<Continuation>),
    Call(Expression, Expression, Box<Continuation>), // The unevaluated argument and the saved env.
    Call2(Expression, Expression, Box<Continuation>), // The function and the saved env.
    Tail(Expression, Box<Continuation>),             // The saved env
    Error,
    Lookup(Expression, Box<Continuation>),      // The saved env
    Binop(Op2, Expression, Box<Continuation>),  // Unevaluated arguments
    Binop2(Op2, Expression, Box<Continuation>), // The first argument
    Relop(Rel2, Expression, Box<Continuation>), // Unevaluated arguments
    Relop2(Rel2, Expression, Box<Continuation>), //The first argument
    If(Expression, Box<Continuation>),          //Unevaluated arguments
    Let(Expression, Expression, Expression, Box<Continuation>), // The var, the body, and the saved env.
    LetRecStar(Expression, Expression, Expression, Box<Continuation>), // The var, the saved env, and the body.
    Dummy,
    Terminal,
}

impl Continuation {
    // Consider making Continuation a first-class Expression.
    pub fn get_hash(&self) -> Fr {
        match self {
            Continuation::Outermost => simple_binary_hash(
                BaseContinuationTag::Outermost.cont_tag_fr(),
                Fr::zero(), // FIXME:
            ),
            Continuation::Simple(continuation) => tagged_1_hash(
                &BaseContinuationTag::Simple.cont_tag_fr(),
                &continuation.continuation_tagged_hash(),
            ),
            Continuation::Call(arg, saved_env, continuation) => simple_binary_hash(
                BaseContinuationTag::Call.cont_tag_fr(),
                tri_hash(
                    &arg.tagged_hash(),
                    &saved_env.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Call2(fun, saved_env, continuation) => simple_binary_hash(
                BaseContinuationTag::Call2.cont_tag_fr(),
                tri_hash(
                    &fun.tagged_hash(),
                    &saved_env.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Tail(saved_env, continuation) => simple_binary_hash(
                BaseContinuationTag::Tail.cont_tag_fr(),
                binary_hash(
                    &saved_env.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Error => {
                simple_binary_hash(
                    BaseContinuationTag::Error.cont_tag_fr(),
                    Fr::zero(), // FIXME
                )
            }
            Continuation::Lookup(saved_env, continuation) => simple_binary_hash(
                BaseContinuationTag::Lookup.cont_tag_fr(),
                binary_hash(
                    &saved_env.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Binop(op2, unevaled_args, continuation) => simple_binary_hash(
                BaseContinuationTag::Binop.cont_tag_fr(),
                tagged_2_hash(
                    &op2.fr(),
                    &unevaled_args.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Binop2(op2, arg1, continuation) => simple_binary_hash(
                BaseContinuationTag::Binop2.cont_tag_fr(),
                tagged_2_hash(
                    &op2.fr(),
                    &arg1.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Relop(rel2, unevaled_args, continuation) => simple_binary_hash(
                BaseContinuationTag::Relop.cont_tag_fr(),
                tagged_2_hash(
                    &rel2.fr(),
                    &unevaled_args.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Relop2(rel2, arg1, continuation) => simple_binary_hash(
                BaseContinuationTag::Relop2.cont_tag_fr(),
                tagged_2_hash(
                    &rel2.fr(),
                    &arg1.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::If(unevaled_args, continuation) => simple_binary_hash(
                BaseContinuationTag::If.cont_tag_fr(),
                binary_hash(
                    &unevaled_args.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Let(var, body, saved_env, continuation) => simple_binary_hash(
                BaseContinuationTag::Let.cont_tag_fr(),
                quad_hash(
                    &var.tagged_hash(),
                    &body.tagged_hash(),
                    &saved_env.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::LetRecStar(var, body, saved_env, continuation) => simple_binary_hash(
                BaseContinuationTag::LetRecStar.cont_tag_fr(),
                quad_hash(
                    &var.tagged_hash(),
                    &body.tagged_hash(),
                    &saved_env.tagged_hash(),
                    &continuation.continuation_tagged_hash(),
                ),
            ),
            Continuation::Dummy => {
                simple_binary_hash(BaseContinuationTag::Dummy.cont_tag_fr(), Fr::zero())
                // FIXME
            }
            Continuation::Terminal => {
                simple_binary_hash(BaseContinuationTag::Terminal.cont_tag_fr(), Fr::zero())
                // FIXME
            }
        }
    }

    pub fn get_continuation_tag(&self) -> BaseContinuationTag {
        match self {
            Continuation::Outermost => BaseContinuationTag::Outermost,
            Continuation::Simple(_) => BaseContinuationTag::Simple,
            Continuation::Call(_, _, _) => BaseContinuationTag::Call,
            Continuation::Call2(_, _, _) => BaseContinuationTag::Call2,
            Continuation::Tail(_, _) => BaseContinuationTag::Tail,
            Continuation::Error => BaseContinuationTag::Error,
            Continuation::Lookup(_, _) => BaseContinuationTag::Lookup,
            Continuation::Binop(_, _, _) => BaseContinuationTag::Binop,
            Continuation::Binop2(_, _, _) => BaseContinuationTag::Binop2,
            Continuation::Relop(_, _, _) => BaseContinuationTag::Relop,
            Continuation::Relop2(_, _, _) => BaseContinuationTag::Relop2,
            Continuation::If(_, _) => BaseContinuationTag::If,
            Continuation::Let(_, _, _, _) => BaseContinuationTag::Let,
            Continuation::LetRecStar(_, _, _, _) => BaseContinuationTag::LetRecStar,
            Continuation::Dummy => BaseContinuationTag::Dummy,
            Continuation::Terminal => BaseContinuationTag::Terminal,
        }
    }

    pub fn continuation_tagged_hash(&self) -> TaggedHash {
        TaggedHash {
            tag: self.get_continuation_tag().cont_tag_fr(),
            hash: self.get_hash(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, std::cmp::Eq)]
pub struct Thunk {
    pub value: Box<Expression>,
    pub continuation: Box<Continuation>,
}

fn binary_hash(a: &TaggedHash, b: &TaggedHash) -> Fr {
    let preimage = vec![a.tag, a.hash, b.tag, b.hash];
    Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_4).hash()
}

fn tri_hash(a: &TaggedHash, b: &TaggedHash, c: &TaggedHash) -> Fr {
    let preimage = vec![a.tag, a.hash, b.tag, b.hash, c.tag, c.hash];
    Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_6).hash()
}

fn quad_hash(a: &TaggedHash, b: &TaggedHash, c: &TaggedHash, d: &TaggedHash) -> Fr {
    let preimage = vec![a.tag, a.hash, b.tag, b.hash, c.tag, c.hash, d.tag, d.hash];
    Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_8).hash()
}

fn oct_hash(preimage: &[Fr]) -> Fr {
    Poseidon::new_with_preimage(preimage, &POSEIDON_CONSTANTS_8).hash()
}

fn simple_binary_hash(a: Fr, b: Fr) -> Fr {
    let preimage = vec![a, b];
    Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_2).hash()
}

fn tagged_1_hash(tag_fr: &Fr, a: &TaggedHash) -> Fr {
    let preimage = vec![*tag_fr, a.tag, a.hash];
    Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_3).hash()
}

fn tagged_2_hash(tag_fr: &Fr, a: &TaggedHash, b: &TaggedHash) -> Fr {
    let preimage = vec![*tag_fr, a.tag, a.hash, b.tag, b.hash];
    Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_5).hash()
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

use Expression::*;

pub trait Tagged {
    fn tag(&self) -> Tag;
    fn tag_fr(&self) -> Fr {
        self.tag().fr()
    }
}

impl Tagged for Expression {
    fn tag(&self) -> Tag {
        match self {
            Nil => Tag::Nil,
            Cons(_, _) => Tag::Cons,
            Sym(_) => Tag::Sym,
            Fun(_, _, _) => Tag::Fun,
            Num(_) => Tag::Num,
            Thunk(_) => Tag::Thunk,
        }
    }
}

impl Expression {
    pub fn get_hash(&self) -> Fr {
        match self {
            Nil => hash_string("NIL"),
            Cons(car, cdr) => binary_hash(car, cdr),
            Sym(s) => hash_string(s),
            Fun(arg, body, closed_env) => tri_hash(arg, body, closed_env),
            Num(fr) => *fr, // Nums are immediate.
            Thunk(_) => todo!(),
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

    pub fn fun(arg: &Expression, body: &Expression, closed_env: &Expression) -> Expression {
        match arg {
            // TODO: closed_env must be an env.
            Expression::Sym(_) => Fun(
                arg.tagged_hash(),
                body.tagged_hash(),
                closed_env.tagged_hash(),
            ),
            _ => {
                panic!("ARG must be a symbol.");
            }
        }
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

    pub fn list(&mut self, elts: Vec<Expression>) -> Expression {
        let mut elts = elts;
        elts.reverse();
        elts.iter()
            .fold(Expression::Nil, |acc, elt| self.cons(elt, &acc))
    }

    pub fn fun(
        &mut self,
        arg: &Expression,
        body: &Expression,
        closed_env: &Expression,
    ) -> Expression {
        let fun = Expression::fun(&arg, body, closed_env);
        self.store(&fun);
        fun
    }

    pub fn car_cdr(&self, expr: &Expression) -> (Expression, Expression) {
        match expr {
            Cons(car, cdr) => (
                self.fetch(*car).expect("Car not found!").clone(),
                self.fetch(*cdr).expect("Cdr not found!").clone(),
            ),
            Nil => (Nil, Nil),
            _ => panic!("Can only extract car_cdr from a Cons."),
        }
    }

    pub fn car(&self, expr: &Expression) -> Expression {
        self.car_cdr(expr).0
    }

    pub fn cdr(&self, expr: &Expression) -> Expression {
        self.car_cdr(expr).1
    }

    pub fn print_expr(&self, expr: &Expression) -> String {
        match expr {
            Nil => "NIL".to_string(),
            Sym(s) => s.clone(),
            Fun(arg, body, _closed_env) => {
                let arg = self.fetch(*arg).unwrap();
                let body = self.fetch(*body).unwrap();
                format!(
                    "<FUNCTION ({}) . {}>",
                    self.print_expr(&arg),
                    self.print_expr(&body)
                )
            }
            Num(fr) => format!("{}", fr),
            Thunk(f) => format!(
                "Cont value {:?}; cont: {:?}",
                self.print_expr(&f.value),
                f.continuation
            ),
            Cons(car, cdr) => {
                let car = self.fetch(*car).unwrap();
                let cdr = self.fetch(*cdr).unwrap();
                match cdr {
                    Expression::Nil => format!("({})", self.print_expr(&car)),
                    _ => format!("({} . {})", self.print_expr(&car), self.print_expr(&cdr)),
                }
            }
        }
    }

    pub fn read(&mut self, input: &str) -> Option<Expression> {
        let mut chars = input.chars().peekable();

        self.read_next(&mut chars)
    }

    fn read_next<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Expression> {
        while let Some(&c) = chars.peek() {
            if let Some(next_expr) = match c {
                '(' => self.read_list(chars),
                '0'..='9' => self.read_number(chars),
                ' ' | '\t' | '\n' | '\r' => {
                    // Skip whitespace.
                    chars.next();
                    None
                }
                x if is_symbol_char(&x) => self.read_symbol(chars),
                _ => {
                    panic!("bad input character: {}", c);
                }
            } {
                return Some(next_expr);
            }
        }
        None
    }

    // In this context, 'list' includes improper lists, i.e. dotted cons-pairs like (1 . 2).
    fn read_list<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Expression> {
        if let Some(&c) = chars.peek() {
            match c {
                '(' => {
                    chars.next(); // Discard.
                    self.read_tail(chars)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    // Read the tail of a list.
    fn read_tail<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Expression> {
        if let Some(c) = skip_whitespace_and_peek(chars) {
            match c {
                ')' => {
                    chars.next();
                    Some(Expression::Nil)
                }
                '.' => {
                    chars.next();
                    let cdr = self.read_next(chars).unwrap();
                    Some(cdr)
                }
                _ => {
                    let car = self.read_next(chars).unwrap();
                    let rest = self.read_tail(chars).unwrap();
                    Some(self.cons(&car, &rest))
                }
            }
        } else {
            panic!("premature end of input");
        }
    }

    fn read_number<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Expression> {
        // As written, read_number assumes the next char is known to be a digit.
        // So it will never return None.
        let mut acc = Fr::zero();
        let ten: Fr = fr_from_u64(10);

        while let Some(&c) = chars.peek() {
            if is_digit_char(&c) {
                if acc != Fr::zero() {
                    acc.mul_assign(&ten);
                }
                let digit_char = chars.next().unwrap();
                let digit = digit_char.to_digit(10).unwrap();
                let fr = fr_from_u64(digit.into());
                acc.add_assign(&fr);
            } else {
                break;
            }
        }
        return Some(Expression::Num(acc));
    }

    fn read_symbol<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Expression> {
        let mut name_chars: Vec<char> = Vec::new();
        while let Some(&c) = chars.peek() {
            if is_symbol_char(&c) {
                let c = chars.next().unwrap();
                name_chars.push(c);
            } else {
                break;
            }
        }
        let name: String = name_chars.into_iter().collect();
        let sym = self.intern(&name);

        match sym {
            Expression::Sym(s) if s == "NIL" => Some(Expression::Nil),
            _ => Some(sym),
        }
    }
}

fn is_symbol_char(c: &char) -> bool {
    match c {
        // FIXME: suppport more than just alpha.
        'a'..='z' | 'A'..='Z' | '+' | '-' | '*' | '/' | '=' => true,
        _ => false,
    }
}

fn is_digit_char(c: &char) -> bool {
    match c {
        '0'..='9' => true,
        _ => false,
    }
}

#[allow(dead_code)]
fn is_reserved_char(c: &char) -> bool {
    match c {
        '(' | ')' | '.' => true,
        _ => false,
    }
}

#[allow(dead_code)]
fn is_whitespace_char(c: &char) -> bool {
    match c {
        ' ' | '\t' | '\n' | '\r' => true,
        _ => false,
    }
}

fn skip_whitespace_and_peek<T: Iterator<Item = char>>(chars: &mut Peekable<T>) -> Option<char> {
    while let Some(&c) = chars.peek() {
        if is_whitespace_char(&c) {
            chars.next();
        } else {
            return Some(c);
        }
    }
    None
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
        assert_eq!(5, Tag::Thunk as u64);
    }

    #[test]
    fn cont_tag_vals() {
        use super::BaseContinuationTag::*;

        assert_eq!(0, Outermost.cont_tag_val());
        assert_eq!(1, Outermost.thunk_tag_val());
        assert_eq!(2, Simple.cont_tag_val());
        assert_eq!(3, Simple.thunk_tag_val());
        assert_eq!(4, Call.cont_tag_val());
        assert_eq!(5, Call.thunk_tag_val());
        assert_eq!(6, Call2.cont_tag_val());
        assert_eq!(7, Call2.thunk_tag_val());
        assert_eq!(8, Tail.cont_tag_val());
        assert_eq!(9, Tail.thunk_tag_val());
        assert_eq!(10, Error.cont_tag_val());
        assert_eq!(11, Error.thunk_tag_val());
        assert_eq!(12, Lookup.cont_tag_val());
        assert_eq!(13, Lookup.thunk_tag_val());
        assert_eq!(14, Binop.cont_tag_val());
        assert_eq!(15, Binop.thunk_tag_val());
        assert_eq!(16, Binop2.cont_tag_val());
        assert_eq!(17, Binop2.thunk_tag_val());
        assert_eq!(18, Relop.cont_tag_val());
        assert_eq!(19, Relop.thunk_tag_val());
        assert_eq!(20, Relop2.cont_tag_val());
        assert_eq!(21, Relop2.thunk_tag_val());
        assert_eq!(22, If.cont_tag_val());
        assert_eq!(23, If.thunk_tag_val());
        assert_eq!(24, Let.cont_tag_val());
        assert_eq!(25, Let.thunk_tag_val());
        assert_eq!(26, LetRecStar.cont_tag_val());
        assert_eq!(27, LetRecStar.thunk_tag_val());
        assert_eq!(28, Dummy.cont_tag_val());
        assert_eq!(29, Dummy.thunk_tag_val());
        assert_eq!(30, Terminal.cont_tag_val());
        assert_eq!(31, Terminal.thunk_tag_val());
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

    #[test]
    fn read_sym() {
        let test = |input, expected: &str| {
            let mut store = Store::default();
            let expr = store.read(input).unwrap();
            assert_eq!(Expression::Sym(expected.to_string()), expr);
        };
        test("asdf", "ASDF");
        test("asdf ", "ASDF");
        test("asdf(", "ASDF");
        test(" asdf", "ASDF");
        test(" asdf ", "ASDF");
        test(
            "
asdf(", "ASDF",
        );
    }

    #[test]
    fn read_nil() {
        let mut store = Store::default();
        let expr = store.read("nil").unwrap();
        assert_eq!(Expression::Nil, expr);
    }

    #[test]
    fn read_num() {
        let test = |input, expected: u64| {
            let mut store = Store::default();
            let expr = store.read(input).unwrap();
            assert_eq!(Expression::num(expected), expr);
        };
        test("123", 123);
        test("0987654321", 987654321);
        test("123)", 123);
        test("123 ", 123);
        test("123z", 123);
        test(" 123", 123);
        test(
            "
0987654321",
            987654321,
        );
    }

    #[test]
    fn read_list() {
        let mut store = Store::default();
        let test = |store: &mut Store, input, expected| {
            let expr = store.read(input).unwrap();
            assert_eq!(expected, &expr);
        };

        let expected = store.cons(&Expression::num(123), &Expression::Nil);
        test(&mut store, "(123)", &expected);

        let expected2 = store.cons(&Expression::num(321), &expected);
        test(&mut store, "(321 123)", &expected2);

        let expected3 = store.cons(&Expression::Sym("PUMPKIN".to_string()), &expected2);
        test(&mut store, "(pumpkin 321 123)", &expected3);

        let expected4 = store.cons(&expected, &Expression::Nil);
        test(&mut store, "((123))", &expected4);

        let alt = store.cons(&Expression::num(321), &Expression::Nil);
        let expected5 = store.cons(&alt, &expected4);
        test(&mut store, "((321) (123))", &expected5);

        let expected6 = store.cons(&expected2, &expected3);
        test(&mut store, "((321 123) pumpkin 321 123)", &expected6);
    }

    #[test]
    fn read_improper_list() {
        let mut store = Store::default();
        let test = |store: &mut Store, input, expected| {
            let expr = store.read(input).unwrap();
            assert_eq!(expected, &expr);
        };

        let expected = store.cons(&Expression::num(123), &Expression::num(321));
        test(&mut store, "(123 . 321)", &expected);

        assert_eq!(store.read("(123 321)"), store.read("(123 . ( 321 ))"))
    }
}
