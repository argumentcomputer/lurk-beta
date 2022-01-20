use crate::{PtrValue, Tagged, TaggedPtr};

use core::hash::Hash;
use std::collections::HashMap;
use std::hash::Hasher;
use std::io::{self, Write};
use std::iter::Peekable;
use std::string::ToString;

use Expression::*;

/// Order of these tag variants is significant, since it will be concretely
/// encoded into content-addressable data structures.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq)]
#[repr(u64)]
pub enum Tag {
    Nil,
    Cons,
    Sym,
    Fun,
    Num,
    Thunk,
    Str,
}

impl PartialEq<u64> for Tag {
    fn eq(&self, other: &u64) -> bool {
        *self as u64 == *other
    }
}

impl From<Tag> for u64 {
    fn from(t: Tag) -> Self {
        t as u64
    }
}

/// Order of these tag variants is significant, since it will be concretely
/// encoded into content-addressable data structures.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq)]
#[repr(u64)]
pub enum BaseContinuationTag {
    //
    Outermost,
    Simple,
    Call,
    Call2,
    Tail,
    Error,
    Lookup,
    Unop,
    Binop,
    Binop2,
    Relop,
    Relop2,
    If,
    LetStar,
    LetRecStar,
    Dummy,
    Terminal,
}

impl PartialEq<u64> for BaseContinuationTag {
    fn eq(&self, other: &u64) -> bool {
        *self as u64 == *other
    }
}

impl From<BaseContinuationTag> for u64 {
    fn from(t: BaseContinuationTag) -> Self {
        t as u64
    }
}

// For now, partition ContinuationTags into thunks and conts.
// If never used, we can collapse.
// We will likely want both if we ever make continuations (including
// thunks) first-class expressions, though.
impl BaseContinuationTag {
    pub fn cont_tag_val(&self) -> u64 {
        2 * *self as u64
    }

    #[allow(dead_code)]
    fn thunk_tag_val(&self) -> u64 {
        1 + self.cont_tag_val()
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq)]
pub enum Expression {
    Nil,
    Cons(TaggedPtr, TaggedPtr),
    Sym(String),
    Fun(TaggedPtr, TaggedPtr, TaggedPtr), // arg, body, closed env
    Num(u64),                             // TODO: support larger than 64bit numbers
    Thunk(Thunk),
    Str(String),
}

#[allow(clippy::derive_hash_xor_eq)]
impl Hash for Expression {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.tag() as u64).hash(state);

        match self {
            Expression::Nil => {}
            Expression::Cons(a, b) => {
                a.hash(state);
                b.hash(state);
            }
            Expression::Sym(name) => {
                name.hash(state);
            }
            Expression::Fun(arg, body, closed) => {
                arg.hash(state);
                body.hash(state);
                closed.hash(state);
            }
            Expression::Num(n) => {
                n.hash(state);
            }
            Expression::Thunk(t) => {
                t.hash(state);
            }
            Expression::Str(s) => {
                s.hash(state);
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub enum Op1 {
    Car,
    Cdr,
    Atom,
}

impl Op1 {
    pub fn tagged_ptr(&self) -> TaggedPtr {
        TaggedPtr::from_tag(*self as u64)
    }
}

impl ToString for Op1 {
    fn to_string(&self) -> String {
        match self {
            Op1::Car => "Car",
            Op1::Cdr => "Cdr",
            Op1::Atom => "Atom",
        }
        .into()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub enum Op2 {
    Sum,
    Diff,
    Product,
    Quotient,
    Cons,
}

impl Op2 {
    pub fn tagged_ptr(&self) -> TaggedPtr {
        TaggedPtr::from_tag(*self as u64)
    }
}

impl ToString for Op2 {
    fn to_string(&self) -> String {
        match self {
            Op2::Sum => "Sum",
            Op2::Diff => "Diff",
            Op2::Product => "Product",
            Op2::Quotient => "Quotient",
            Op2::Cons => "Cons",
        }
        .into()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub enum Rel2 {
    Equal,
    NumEqual,
}

impl Rel2 {
    pub fn tagged_ptr(&self) -> TaggedPtr {
        TaggedPtr::from_tag(*self as u64)
    }
}

impl ToString for Rel2 {
    fn to_string(&self) -> String {
        match self {
            Rel2::Equal => "Equal",
            Rel2::NumEqual => "NumEqual",
        }
        .into()
    }
}

// TODO: Unify this with Expression::Thunk. For simplicity, keep separate for now.
// This separateness means that Expression and Continuation have separate namespaces.
// In practice, this means they have distinct tags, and the containing code must know
// statically which is expected.
#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub enum Continuation {
    Outermost,
    Simple(Box<Continuation>),
    Call(Expression, Expression, Box<Continuation>), // The unevaluated argument and the saved env.
    Call2(Expression, Expression, Box<Continuation>), // The function and the saved env.
    Tail(Expression, Box<Continuation>),             // The saved env
    Error,
    Lookup(Expression, Box<Continuation>), // The saved env
    Unop(Op1, Box<Continuation>),
    Binop(Op2, Expression, Expression, Box<Continuation>), // The saved env and unevaluated argument
    Binop2(Op2, Expression, Box<Continuation>),            // First argument.
    Relop(Rel2, Expression, Expression, Box<Continuation>), // The saved env and unevaluated arguments
    Relop2(Rel2, Expression, Box<Continuation>),            //The first argument
    If(Expression, Box<Continuation>),                      //Unevaluated arguments
    LetStar(Expression, Expression, Expression, Box<Continuation>), // The var, the body, and the saved env.
    LetRecStar(Expression, Expression, Expression, Box<Continuation>), // The var, the saved env, and the body.
    Dummy,
    Terminal,
}

impl Continuation {
    fn get_hash_components(&self) -> [TaggedPtr; 4] {
        match self {
            Continuation::Outermost => [
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
            Continuation::Simple(continuation) => [
                continuation.tagged_ptr(),
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
            Continuation::Call(arg, saved_env, continuation) => [
                saved_env.tagged_ptr(),
                arg.tagged_ptr(),
                continuation.tagged_ptr(),
                TaggedPtr::null(),
            ],
            Continuation::Call2(fun, saved_env, continuation) => [
                saved_env.tagged_ptr(),
                fun.tagged_ptr(),
                continuation.tagged_ptr(),
                TaggedPtr::null(),
            ],
            Continuation::Tail(saved_env, continuation) => [
                saved_env.tagged_ptr(),
                continuation.tagged_ptr(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
            Continuation::Error => [
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
            Continuation::Lookup(saved_env, continuation) => [
                saved_env.tagged_ptr(),
                continuation.tagged_ptr(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
            Continuation::Unop(op1, continuation) => [
                op1.tagged_ptr(),
                continuation.tagged_ptr(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
            Continuation::Binop(op2, saved_env, unevaled_args, continuation) => [
                op2.tagged_ptr(),
                saved_env.tagged_ptr(),
                unevaled_args.tagged_ptr(),
                continuation.tagged_ptr(),
            ],
            Continuation::Binop2(op2, arg1, continuation) => [
                op2.tagged_ptr(),
                arg1.tagged_ptr(),
                continuation.tagged_ptr(),
                TaggedPtr::null(),
            ],
            Continuation::Relop(rel2, saved_env, unevaled_args, continuation) => [
                rel2.tagged_ptr(),
                saved_env.tagged_ptr(),
                unevaled_args.tagged_ptr(),
                continuation.tagged_ptr(),
            ],
            Continuation::Relop2(rel2, arg1, continuation) => [
                rel2.tagged_ptr(),
                arg1.tagged_ptr(),
                continuation.tagged_ptr(),
                TaggedPtr::null(),
            ],
            Continuation::If(unevaled_args, continuation) => [
                unevaled_args.tagged_ptr(),
                continuation.tagged_ptr(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
            Continuation::LetStar(var, body, saved_env, continuation) => [
                var.tagged_ptr(),
                body.tagged_ptr(),
                saved_env.tagged_ptr(),
                continuation.tagged_ptr(),
            ],
            Continuation::LetRecStar(var, body, saved_env, continuation) => [
                var.tagged_ptr(),
                body.tagged_ptr(),
                saved_env.tagged_ptr(),
                continuation.tagged_ptr(),
            ],
            Continuation::Dummy => [
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
            Continuation::Terminal => [
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
                TaggedPtr::null(),
            ],
        }
    }
}

impl Tagged for Continuation {
    type Tag = BaseContinuationTag;

    fn tag(&self) -> Self::Tag {
        match self {
            Continuation::Outermost => BaseContinuationTag::Outermost,
            Continuation::Simple(_) => BaseContinuationTag::Simple,
            Continuation::Call(_, _, _) => BaseContinuationTag::Call,
            Continuation::Call2(_, _, _) => BaseContinuationTag::Call2,
            Continuation::Tail(_, _) => BaseContinuationTag::Tail,
            Continuation::Error => BaseContinuationTag::Error,
            Continuation::Lookup(_, _) => BaseContinuationTag::Lookup,
            Continuation::Unop(_, _) => BaseContinuationTag::Unop,
            Continuation::Binop(_, _, _, _) => BaseContinuationTag::Binop,
            Continuation::Binop2(_, _, _) => BaseContinuationTag::Binop2,
            Continuation::Relop(_, _, _, _) => BaseContinuationTag::Relop,
            Continuation::Relop2(_, _, _) => BaseContinuationTag::Relop2,
            Continuation::If(_, _) => BaseContinuationTag::If,
            Continuation::LetStar(_, _, _, _) => BaseContinuationTag::LetStar,
            Continuation::LetRecStar(_, _, _, _) => BaseContinuationTag::LetRecStar,
            Continuation::Dummy => BaseContinuationTag::Dummy,
            Continuation::Terminal => BaseContinuationTag::Terminal,
        }
    }

    fn tagged_hash(&self) -> PtrValue {
        TaggedPtr::hash_many(&self.get_hash_components())
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub struct Thunk {
    pub value: Box<Expression>,
    pub continuation: Box<Continuation>,
}

impl Thunk {
    pub fn get_hash_components(&self) -> [TaggedPtr; 2] {
        let value = self.value.tagged_ptr();
        let continuation = self.continuation.tagged_ptr();

        [value, continuation]
    }
}

impl Tagged for Expression {
    type Tag = Tag;

    fn tag(&self) -> Self::Tag {
        match self {
            Nil => Tag::Nil,
            Cons(_, _) => Tag::Cons,
            Sym(_) => Tag::Sym,
            Str(_) => Tag::Str,
            Fun(_, _, _) => Tag::Fun,
            Num(_) => Tag::Num,
            Thunk(_) => Tag::Thunk,
        }
    }

    fn tagged_hash(&self) -> PtrValue {
        match self {
            Nil => TaggedPtr::hash_string("NIL"),
            Cons(car, cdr) => TaggedPtr::hash_many(&[*car, *cdr]),
            Sym(s) => TaggedPtr::hash_string(s),
            Str(s) => TaggedPtr::hash_string(s),
            Fun(arg, body, closed_env) => TaggedPtr::hash_many(&[*arg, *body, *closed_env]),
            Num(num) => {
                // Nums are immediate.
                TaggedPtr::hash_num(*num)
            }
            Thunk(thunk) => {
                let value = thunk.value.tagged_ptr();
                let continuation = (*thunk.continuation).tagged_ptr();

                TaggedPtr::hash_many(&[value, continuation])
            }
        }
    }
}

impl Expression {
    pub fn read_sym(s: &str) -> Expression {
        Sym(s.to_uppercase())
    }

    pub fn cons(a: &Expression, b: &Expression) -> Expression {
        Cons(a.tagged_ptr(), b.tagged_ptr())
    }

    pub fn num(n: u64) -> Expression {
        Num(n)
    }

    pub fn fun(arg: &Expression, body: &Expression, closed_env: &Expression) -> Expression {
        match arg {
            // TODO: closed_env must be an env.
            Expression::Sym(_) => Fun(arg.tagged_ptr(), body.tagged_ptr(), closed_env.tagged_ptr()),
            _ => {
                panic!("ARG must be a symbol.");
            }
        }
    }

    pub fn thunk(value: Expression, continuation: Continuation) -> Expression {
        Expression::Thunk(Thunk {
            value: Box::new(value),
            continuation: Box::new(continuation),
        })
    }

    pub fn is_keyword_sym(&self) -> bool {
        if let Self::Sym(s) = self {
            s.starts_with(':')
        } else {
            false
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Store {
    pub map: HashMap<TaggedPtr, Expression>,
    pub continuation_map: HashMap<TaggedPtr, Continuation>,
}

impl Store {
    pub fn fetch(&self, t: &TaggedPtr) -> Option<Expression> {
        match t.tag() {
            // Nil has a unique identity.
            tag if Tag::Nil == tag => Some(Expression::Nil),
            // Nums are immediate so not looked up in map.
            tag if Tag::Num == tag => Some(Expression::Num(t.value_as_num())),
            _ => self.map.get(t).cloned(),
        }
    }

    pub fn store(&mut self, exp: &Expression) {
        self.map
            .entry(exp.tagged_ptr())
            .or_insert_with(|| exp.clone());
    }

    pub fn fetch_continuation(&self, t: &TaggedPtr) -> Option<Continuation> {
        self.continuation_map.get(t).cloned()
    }

    pub fn store_continuation(&mut self, cont: &Continuation) {
        self.continuation_map
            .entry(cont.tagged_ptr())
            .or_insert_with(|| cont.clone());
    }

    // Consider a secondary map/index on symbol names, which would be proper
    // interning and save expensive rehashing each time. The same potentially
    // goes for other types.
    pub fn intern(&mut self, s: &str) -> Expression {
        let sym = Expression::read_sym(s);
        self.store(&sym);
        sym
    }

    pub fn intern_string(&mut self, s: &str) -> Expression {
        let str = Expression::Str(s.to_string());
        self.store(&str);
        str
    }

    pub fn cons(&mut self, car: &Expression, cdr: &Expression) -> Expression {
        let cons = Expression::cons(car, cdr);
        self.store(&cons);
        cons
    }

    pub fn list(&mut self, elts: &mut [Expression]) -> Expression {
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
        let fun = Expression::fun(arg, body, closed_env);
        self.store(&fun);
        fun
    }

    pub fn thunk(&mut self, value: Expression, continuation: Continuation) -> Expression {
        let t = Expression::thunk(value, continuation);
        self.store(&t);
        t
    }

    pub fn car_cdr(&self, expr: &Expression) -> (Expression, Expression) {
        match expr {
            Cons(car, cdr) => (
                self.fetch(car).expect("Car not found!"),
                self.fetch(cdr).expect("Cdr not found!"),
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

    pub fn write_expr_str(&self, expr: &Expression) -> String {
        let mut out = Vec::new();
        self.print_expr(expr, &mut out).expect("preallocated");
        String::from_utf8(out).expect("I know it")
    }

    pub fn print_expr(&self, expr: &Expression, w: &mut impl Write) -> io::Result<()> {
        match expr {
            Nil => write!(w, "NIL"),
            Sym(s) => write!(w, "{}", s),
            Str(s) => write!(w, "\"{}\"", s),
            Fun(arg, body, _closed_env) => {
                let arg = self.fetch(arg).unwrap();
                let body = self.fetch(body).unwrap();
                write!(w, "<FUNCTION (")?;
                self.print_expr(&arg, w)?;
                write!(w, ") . ")?;
                self.print_expr(&body, w)?;
                write!(w, ">")
            }
            Num(fr) => print_num(fr, w),
            Thunk(f) => {
                write!(
                    w,
                    "Thunk for cont {} with value: ",
                    self.write_cont_str(&f.continuation)
                )?;
                self.print_expr(&f.value, w)
            }
            Cons(_, _) => {
                write!(w, "(")?;
                self.print_tail(expr, w)
            }
        }
    }

    pub fn write_cont_str(&self, cont: &Continuation) -> String {
        let mut out = Vec::new();
        self.print_cont(cont, &mut out).expect("preallocated");
        String::from_utf8(out).expect("I know it")
    }

    pub fn print_cont(&self, cont: &Continuation, w: &mut impl Write) -> io::Result<()> {
        match cont {
            Continuation::Outermost => write!(w, "Outermost"),
            Continuation::Simple(cont) => {
                write!(w, "Simple(")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Call(expr1, expr2, cont) => {
                write!(w, "Call(")?;
                self.print_expr(expr1, w)?;
                write!(w, ", ")?;
                self.print_expr(expr2, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Call2(expr1, expr2, cont) => {
                write!(w, "Call2(")?;
                self.print_expr(expr1, w)?;
                write!(w, ", ")?;
                self.print_expr(expr2, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Tail(expr, cont) => {
                write!(w, "Tail(")?;
                self.print_expr(expr, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Error => write!(w, "Error"),
            Continuation::Lookup(expr, cont) => {
                write!(w, "Lookup(")?;
                self.print_expr(expr, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Unop(op1, cont) => {
                write!(w, "Unop(")?;
                write!(w, "{}", op1.to_string())?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Binop(op2, expr1, expr2, cont) => {
                write!(w, "Binop(")?;
                write!(w, "{}", op2.to_string())?;
                write!(w, ", ")?;
                self.print_expr(expr1, w)?;
                write!(w, ", ")?;
                self.print_expr(expr2, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Binop2(op2, expr, cont) => {
                write!(w, "Binop2(")?;
                write!(w, "{}", op2.to_string())?;
                write!(w, ", ")?;
                self.print_expr(expr, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Relop(rel2, expr1, expr2, cont) => {
                write!(w, "Relop(")?;
                write!(w, "{}", rel2.to_string())?;
                write!(w, ", ")?;
                self.print_expr(expr1, w)?;
                write!(w, ", ")?;
                self.print_expr(expr2, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Relop2(rel2, expr, cont) => {
                write!(w, "Relop2(")?;
                write!(w, "{}", rel2.to_string())?;
                write!(w, ", ")?;
                self.print_expr(expr, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::If(expr, cont) => {
                write!(w, "If(")?;
                self.print_expr(expr, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::LetStar(expr1, expr2, expr3, cont) => {
                write!(w, "LetStar(")?;
                self.print_expr(expr1, w)?;
                write!(w, ", ")?;
                self.print_expr(expr2, w)?;
                write!(w, ", ")?;
                self.print_expr(expr3, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::LetRecStar(expr1, expr2, expr3, cont) => {
                write!(w, "LetRecStar(")?;
                self.print_expr(expr1, w)?;
                write!(w, ", ")?;
                self.print_expr(expr2, w)?;
                write!(w, ", ")?;
                self.print_expr(expr3, w)?;
                write!(w, ", ")?;
                self.print_cont(cont, w)?;
                write!(w, ")")
            }
            Continuation::Dummy => write!(w, "Dummy"),
            Continuation::Terminal => write!(w, "Terminal"),
        }
    }

    pub fn print_tail(&self, expr: &Expression, w: &mut impl Write) -> io::Result<()> {
        match expr {
            Nil => write!(w, ")"),
            Cons(car, cdr) => {
                let car = self.fetch(car).unwrap();
                let cdr = self.fetch(cdr).unwrap();
                match cdr {
                    Expression::Nil => {
                        self.print_expr(&car, w)?;
                        write!(w, ")")
                    }
                    Expression::Cons(_, _) => {
                        self.print_expr(&car, w)?;
                        write!(w, " ")?;
                        self.print_tail(&cdr, w)
                    }
                    _ => {
                        self.print_expr(&car, w)?;
                        write!(w, " . ")?;
                        self.print_expr(&cdr, w)?;
                        write!(w, ")")
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn read(&mut self, input: &str) -> Option<Expression> {
        let mut chars = input.chars().peekable();

        self.read_next(&mut chars)
    }

    pub fn read_maybe_meta<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<(Expression, bool)> {
        if let Some(c) = skip_whitespace_and_peek(chars) {
            match c {
                '!' => {
                    chars.next();
                    if let Some(s) = self.read_string(chars) {
                        Some((s, true))
                    } else if let Some((e, is_meta)) = self.read_maybe_meta(chars) {
                        assert!(!is_meta);
                        Some((e, true))
                    } else {
                        None
                    }
                }
                _ => self.read_next(chars).map(|expr| (expr, false)),
            }
        } else {
            None
        }
    }

    pub fn read_next<T: Iterator<Item = char>>(
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
                    continue;
                }
                '\'' => {
                    chars.next();
                    let quote = self.intern("quote");
                    let quoted = self.read_next(chars)?;
                    let inner = self.list(&mut [quoted]);
                    Some(self.cons(&quote, &inner))
                }
                '\"' => self.read_string(chars),
                ';' => {
                    chars.next();
                    if skip_line_comment(chars) {
                        continue;
                    } else {
                        None
                    }
                }
                x if is_symbol_char(&x, true) => self.read_symbol(chars),
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
                    let remaining_tail = self.read_tail(chars).unwrap();
                    assert_eq!(Expression::Nil, remaining_tail);

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
        let mut acc = 0;
        let ten = 10;

        while let Some(&c) = chars.peek() {
            if is_digit_char(&c) {
                if acc != 0 {
                    acc *= ten;
                }
                let digit_char = chars.next().unwrap();
                let digit = digit_char.to_digit(10).unwrap();
                let n: u64 = digit.into();
                acc += n;
            } else {
                break;
            }
        }
        Some(Expression::Num(acc))
    }

    fn read_symbol<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Expression> {
        let mut name = String::new();
        let mut is_initial = true;
        while let Some(&c) = chars.peek() {
            if is_symbol_char(&c, is_initial) {
                let c = chars.next().unwrap();
                name.push(c);
            } else {
                break;
            }
            is_initial = false;
        }
        let sym = self.intern(&name);

        match sym {
            Expression::Sym(s) if s == "NIL" => Some(Expression::Nil),
            _ => Some(sym),
        }
    }

    // For now, this is only used for REPL/CLI commands.
    pub fn read_string<T: Iterator<Item = char>>(
        &mut self,
        chars: &mut Peekable<T>,
    ) -> Option<Expression> {
        let mut result = String::new();

        if let Some('"') = skip_whitespace_and_peek(chars) {
            chars.next();
            while let Some(&c) = chars.peek() {
                chars.next();
                // TODO: This does not handle any escaping, so strings containing " cannot be read.
                if c == '"' {
                    let str = self.intern_string(&result);
                    return Some(str);
                } else {
                    result.push(c);
                }
            }
            None
        } else {
            None
        }
    }
}

fn is_symbol_char(c: &char, initial: bool) -> bool {
    match c {
        // FIXME: suppport more than just alpha.
        'a'..='z' | 'A'..='Z' | '+' | '-' | '*' | '/' | '=' | ':' => true,
        _ => {
            if initial {
                false
            } else {
                matches!(c, '0'..='9')
            }
        }
    }
}

fn is_digit_char(c: &char) -> bool {
    matches!(c, '0'..='9')
}

#[allow(dead_code)]
fn is_reserved_char(c: &char) -> bool {
    matches!(c, '(' | ')' | '.')
}

fn is_whitespace_char(c: &char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r')
}

fn is_comment_char(c: &char) -> bool {
    matches!(c, ';')
}

fn is_line_end_char(c: &char) -> bool {
    matches!(c, '\n' | '\r')
}

// Skips whitespace and comments, returning the next character, if any.
fn skip_whitespace_and_peek<T: Iterator<Item = char>>(chars: &mut Peekable<T>) -> Option<char> {
    while let Some(&c) = chars.peek() {
        if is_whitespace_char(&c) {
            chars.next();
        } else if is_comment_char(&c) {
            skip_line_comment(chars);
        } else {
            return Some(c);
        }
    }
    None
}

// Returns true if comment ends with a line end character.
// If false, this comment is unterminated and is the end of input.
fn skip_line_comment<T: Iterator<Item = char>>(chars: &mut Peekable<T>) -> bool {
    while let Some(&c) = chars.peek() {
        if !is_line_end_char(&c) {
            chars.next();
        } else {
            return true;
        }
    }
    false

    //chars.skip_while(|c| *c != '\n' && *c != '\r');
    //     }
    // };
}

fn print_num(n: &u64, w: &mut impl Write) -> io::Result<()> {
    write!(w, "Fr(0x{:x})", n)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_print_num() {
        let n = 5;
        let mut res = Vec::new();
        print_num(&n, &mut res).unwrap();
        assert_eq!(&res[..], &b"Fr(0x5)"[..]);
    }

    #[test]
    fn tag_vals() {
        assert_eq!(0, Tag::Nil as u64);
        assert_eq!(1, Tag::Cons as u64);
        assert_eq!(2, Tag::Sym as u64);
        assert_eq!(3, Tag::Fun as u64);
        assert_eq!(4, Tag::Num as u64);
        assert_eq!(5, Tag::Thunk as u64);
        assert_eq!(6, Tag::Str as u64);
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
        assert_eq!(14, Unop.cont_tag_val());
        assert_eq!(15, Unop.thunk_tag_val());
        assert_eq!(16, Binop.cont_tag_val());
        assert_eq!(17, Binop.thunk_tag_val());
        assert_eq!(18, Binop2.cont_tag_val());
        assert_eq!(19, Binop2.thunk_tag_val());
        assert_eq!(20, Relop.cont_tag_val());
        assert_eq!(21, Relop.thunk_tag_val());
        assert_eq!(22, Relop2.cont_tag_val());
        assert_eq!(23, Relop2.thunk_tag_val());
        assert_eq!(24, If.cont_tag_val());
        assert_eq!(25, If.thunk_tag_val());
        assert_eq!(26, LetStar.cont_tag_val());
        assert_eq!(27, LetStar.thunk_tag_val());
        assert_eq!(28, LetRecStar.cont_tag_val());
        assert_eq!(29, LetRecStar.thunk_tag_val());
        assert_eq!(30, Dummy.cont_tag_val());
        assert_eq!(31, Dummy.thunk_tag_val());
        assert_eq!(32, Terminal.cont_tag_val());
        assert_eq!(33, Terminal.thunk_tag_val());
    }

    #[test]
    fn sym_tagged_ptr() {
        let s = Expression::read_sym("bubba");
        let t = s.tagged_ptr();
        assert_eq!(Sym("BUBBA".to_string()), s);
        assert_eq!(Tag::Sym, t.tag());
        // assert_eq!(
        //     fr_from_u64s([
        //         0x1c3939f30194d3b9,
        //         0x8e7208d4f2e73ed6,
        //         0x455900037c586565,
        //         0x638cabd52a433562
        //     ]),
        //     s.get_hash()
        // );
    }

    #[test]
    fn nil_tagged_ptr() {
        let nil = Expression::Nil;
        let t = nil.tagged_ptr();
        assert_eq!(Tag::Nil, t.tag());
        assert_eq!(TaggedPtr::hash_string(&"NIL"), nil.tagged_hash());
        // assert_eq!(
        //     fr_from_u64s([
        //         0xaece3618ecf6d992,
        //         0xfccb6c0141aff847,
        //         0xc19882347797fbab,
        //         0x33e4e3e92bc14968
        //     ]),
        //     nil.get_hash()
        // );
    }

    #[test]
    fn cons_tagged_ptr() {
        let nil = Expression::Nil;
        let apple = Expression::read_sym("apple");
        let cons = Expression::Cons(apple.tagged_ptr().clone(), nil.tagged_ptr().clone());
        assert_eq!(cons, Expression::cons(&apple, &nil));
        let t = cons.tagged_ptr();
        assert_eq!(Tag::Cons, t.tag());
        // assert_eq!(
        //     fr_from_u64s([
        //         0x3c0321b1e4d826b4,
        //         0x478de3220a74033e,
        //         0xcb314ea6d44ae65f,
        //         0x05c60d24e14cf749
        //     ]),
        //     cons.get_hash(),
        // );
    }

    #[test]
    fn num_tagged_ptr() {
        let num = Expression::num(123);
        let t = num.tagged_ptr();
        assert_eq!(Expression::Num(123), num);
        assert_eq!(Tag::Num, t.tag());
        // assert_eq!(
        //     fr_from_u64s([
        //         0x000000000000007b,
        //         0x0000000000000000,
        //         0x0000000000000000,
        //         0x0000000000000000
        //     ]),
        //     num.get_hash()
        // );
    }

    #[test]
    fn store() {
        let mut store = Store::default();

        let num = Expression::num(123);
        let num_t = num.tagged_ptr();
        store.store(&num);
        let num_again = store.fetch(&num_t).unwrap();

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

        let pair = store.cons(&Expression::num(1), &Expression::num(2));
        let expected7 = store.list(&mut [pair, Expression::num(3)]);
        test(&mut store, "((1 . 2) 3)", &expected7);
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
    #[test]
    fn read_print_expr() {
        let mut store = Store::default();
        let test = |store: &mut Store, input| {
            let expr = store.read(input).unwrap();
            let output = store.write_expr_str(&expr);
            assert_eq!(input, output);
        };

        test(&mut store, "A");
        test(&mut store, "(A . B)");
        test(&mut store, "(A B C)");
        test(&mut store, "(A (B) C)");
        test(&mut store, "(A (B . C) (D E (F)) G)");
        // test(&mut store, "'A");
        // test(&mut store, "'(A B)");
    }

    #[test]
    fn read_maybe_meta() {
        let mut store = Store::default();
        let test =
            |store: &mut Store, input: &str, expected_expr: Expression, expected_meta: bool| {
                let mut chars = input.chars().peekable();

                match store.read_maybe_meta(&mut chars).unwrap() {
                    (expr, meta) => {
                        assert_eq!(expected_expr, expr);
                        assert_eq!(expected_meta, meta);
                    }
                };
            };

        test(&mut store, "123", Expression::num(123), false);

        {
            let l = store.list(&mut [Expression::num(123), Expression::num(321)]);
            test(&mut store, " (123 321)", l, false);
        }
        {
            let l = store.list(&mut [Expression::num(123), Expression::num(321)]);
            test(&mut store, " !(123 321)", l, true);
        }
        {
            let l = store.list(&mut [Expression::num(123), Expression::num(321)]);
            test(&mut store, " ! (123 321)", l, true);
        }
        {
            let s = store.intern(&"asdf");
            test(&mut store, "!asdf", s, true);
        }
        {
            let s = store.intern(":assert");
            let l = store.list(&mut [s]);
            test(&mut store, "!(:assert)", l, true);
        }
        {
            let s = store.intern(&"asdf");
            test(
                &mut store,
                ";; comment
!asdf",
                s,
                true,
            );
        }
    }
    #[test]
    fn is_keyword() {
        assert!(Expression::Sym(":UIOP".to_string()).is_keyword_sym());
        assert!(!Expression::Sym("UIOP".to_string()).is_keyword_sym());
    }
    #[test]
    fn read_string() {
        let mut store = Store::default();
        let test = |store: &mut Store, input: &str, expected: Option<Expression>| {
            let maybe_string = store.read_string(&mut input.chars().peekable());
            assert_eq!(expected, maybe_string);
        };

        test(
            &mut store,
            "\"asdf\"",
            Some(Expression::Str("asdf".to_string())),
        );
        test(&mut store, "\"asdf", None);
        test(&mut store, "asdf", None);
    }
    #[test]
    fn read_with_comments() {
        let mut store = Store::default();
        let test = |store: &mut Store, input: &str, expected: Option<Expression>| {
            let res = store.read(input);
            assert_eq!(expected, res);
        };

        test(
            &mut store,
            ";123
321",
            Some(Expression::num(321)),
        );
    }
}
