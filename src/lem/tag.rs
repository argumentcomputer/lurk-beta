use std::fmt::Display;

use crate::field::LurkField;

#[derive(Clone, Copy, PartialEq, Debug, PartialOrd, Ord, Eq, Hash)]
pub enum Tag {
    // expression tags
    Nil,
    Num,
    U64,
    Char,
    Str,
    Comm,
    Fun,
    Cons,
    Sym,
    Key,
    Thunk,
    // continuation tags
    Outermost,
    Dummy,
    Terminal,
    Error,
    Tail,
    Lookup,
    Let,
    LetRec,
    Binop,
    Binop2,
    Unop,
    If,
    Call0,
    Call,
    Call2,
    Emit,
    // control tags. Note that this is a hack because we can't add arbitrary
    // constants yet.
    Return,
    MakeThunk,
    ApplyContinuation,
    // unop tags
    Car,
    Cdr,
    Atom,
    // Emit,
    Open,
    Secret,
    Commit,
    // Num,
    // Comm,
    // Char,
    Eval,
    // U64,
    // binop tags
    Sum,
    Diff,
    Product,
    Quotient,
    Equal,
    NumEqual,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    // Cons,
    StrCons,
    Begin,
    Hide,
    Modulo,
    // Eval,
}

impl Tag {
    #[inline]
    pub fn to_field<F: LurkField>(self) -> F {
        // TODO: match values from current approach
        F::from_u64(self as u64)
    }
}

impl Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // expressions
            Tag::Nil => write!(f, "Nil"),
            Tag::Num => write!(f, "Num"),
            Tag::U64 => write!(f, "U64"),
            Tag::Char => write!(f, "Char"),
            Tag::Str => write!(f, "Str"),
            Tag::Comm => write!(f, "Comm"),
            Tag::Fun => write!(f, "Fun"),
            Tag::Cons => write!(f, "Cons"),
            Tag::Sym => write!(f, "Sym"),
            Tag::Key => write!(f, "Key"),
            Tag::Thunk => write!(f, "Thunk"),
            // continuations
            Tag::Outermost => write!(f, "Outermost"),
            Tag::Dummy => write!(f, "Dummy"),
            Tag::Terminal => write!(f, "Terminal"),
            Tag::Error => write!(f, "Error"),
            Tag::Tail => write!(f, "Tail"),
            Tag::Lookup => write!(f, "Lookup"),
            Tag::Let => write!(f, "Let"),
            Tag::LetRec => write!(f, "LetRec"),
            Tag::Binop => write!(f, "Binop"),
            Tag::Binop2 => write!(f, "Binop2"),
            Tag::Unop => write!(f, "Unop"),
            Tag::If => write!(f, "If"),
            Tag::Call0 => write!(f, "Call0"),
            Tag::Call => write!(f, "Call"),
            Tag::Call2 => write!(f, "Call2"),
            Tag::Emit => write!(f, "Emit"),
            // control
            Tag::Return => write!(f, "Return"),
            Tag::ApplyContinuation => write!(f, "ApplyContinuation"),
            Tag::MakeThunk => write!(f, "MakeThunk"),
            // unop
            Tag::Car => write!(f, "Car"),
            Tag::Cdr => write!(f, "Cdr"),
            Tag::Atom => write!(f, "Atom"),
            // Tag::Emit => write!(f, "Emit"),
            Tag::Open => write!(f, "Open"),
            Tag::Secret => write!(f, "Secret"),
            Tag::Commit => write!(f, "Commit"),
            // Tag::Num  => write!(f, "Num"),
            // Tag::Comm => write!(f, "Comm"),
            // Tag::Char => write!(f, "Char"),
            Tag::Eval => write!(f, "Eval"),
            // Tag::U64  => write!(f, "U64"),
            // binop
            Tag::Sum => write!(f, "Sum"),
            Tag::Diff => write!(f, "Diff"),
            Tag::Product => write!(f, "Product"),
            Tag::Quotient => write!(f, "Quotient"),
            Tag::Equal => write!(f, "Equal"),
            Tag::NumEqual => write!(f, "NumEqual"),
            Tag::Less => write!(f, "Less"),
            Tag::Greater => write!(f, "Greater"),
            Tag::LessEqual => write!(f, "LessEqual"),
            Tag::GreaterEqual => write!(f, "GreaterEq"),
            // Tag::Cons => write!(f, "Cons")
            Tag::StrCons => write!(f, "StrCons"),
            Tag::Begin => write!(f, "Begin"),
            Tag::Hide => write!(f, "Hide"),
            Tag::Modulo => write!(f, "Modulo"),
            // Tag::Eval => write!(f, "Eval"),
        }
    }
}
