use crate::field::{FWrap, LurkField};
use crate::store::Ptr;
use crate::store::Store;
use crate::writer::Write;
use crate::{Num, UInt};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Gth,
    Gte,
    Lth,
    Lte,
    Eql,
}

impl ArithOp {
    pub fn sym(&self) -> String {
        match self {
            Self::Add => "+".to_string(),
            Self::Sub => "-".to_string(),
            Self::Mul => "*".to_string(),
            Self::Div => "/".to_string(),
            Self::Mod => "%".to_string(),
            Self::Gth => ">".to_string(),
            Self::Gte => ">=".to_string(),
            Self::Lth => "<".to_string(),
            Self::Lte => "<=".to_string(),
            Self::Eql => "=".to_string(),
        }
    }
}

impl fmt::Display for ArithOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.sym())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuiltIn {
    T,
    Nil,
    If,
    Lambda,
    Let,
    LetRec,
    Quote,
    Atom,
    FunctionP,
    Cons,
    StrCons,
    Car,
    Cdr,
    Num,
    U64,
    Char,
    Eq,
    Emit,
    Begin,
    CurrentEnv,
    Eval,
    Comm,
    Commit,
    Hide,
    Open,
}

impl BuiltIn {
    pub fn sym(&self) -> String {
        match self {
            Self::T => "T".to_string(),
            Self::Nil => "NIL".to_string(),
            Self::If => "IF".to_string(),
            Self::Lambda => "LAMBDA".to_string(),
            Self::Let => "LET".to_string(),
            Self::LetRec => "LETREC".to_string(),
            Self::Quote => "QUOTE".to_string(),
            Self::Atom => "ATOM".to_string(),
            Self::FunctionP => "FUNCTIONP".to_string(),
            Self::Cons => "CONS".to_string(),
            Self::StrCons => "STRCONS".to_string(),
            Self::Car => "CAR".to_string(),
            Self::Cdr => "CDR".to_string(),
            Self::Num => "NUM".to_string(),
            Self::U64 => "U64".to_string(),
            Self::Char => "CHAR".to_string(),
            Self::Eq => "EQ".to_string(),
            Self::Emit => "EMIT".to_string(),
            Self::Begin => "BEGIN".to_string(),
            Self::CurrentEnv => "CURRENT-ENV".to_string(),
            Self::Eval => "EVAL".to_string(),
            Self::Comm => "COMM".to_string(),
            Self::Commit => "COMMIT".to_string(),
            Self::Hide => "HIDE".to_string(),
            Self::Open => "OPEN".to_string(),
        }
    }
}

impl fmt::Display for BuiltIn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.sym())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Syn<F: LurkField> {
    Num(F),
    UInt(u64),
    ArithOp(ArithOp),
    BuiltIn(BuiltIn),
    Symbol(String),
    String(String),
    Char(char),
    List(Vec<Syn<F>>),
    Improper(Vec<Syn<F>>, Box<Syn<F>>),
}

impl<F: LurkField> fmt::Display for Syn<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Num(x) => write!(f, "{}", Num::Scalar(*x)),
            Self::UInt(x) => write!(f, "{}u64", x),
            Self::ArithOp(x) => write!(f, "{}", x),
            Self::BuiltIn(x) => write!(f, "{}", x),
            Self::Symbol(x) => write!(f, "{}", x),
            Self::String(x) => write!(f, "\"{}\"", x),
            Self::Char(x) => write!(f, "#\\{}", x),
            Self::List(xs) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    if let None = iter.peek() {
                        write!(f, "{}", x)?;
                    } else {
                        write!(f, "{} ", x)?;
                    }
                }
                write!(f, ")")
            }
            Self::Improper(xs, end) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    if let None = iter.peek() {
                        write!(f, "{}", x)?;
                    } else {
                        write!(f, "{} ", x)?;
                    }
                }
                write!(f, " . {})", end)
            }
        }
    }
}

impl<F: LurkField> Syn<F> {
    pub fn reserved_symbols() -> Vec<String> {
        vec![
            "nil".to_string(),
            "t".to_string(),
            "quote".to_string(),
            "lambda".to_string(),
            "_".to_string(),
            "let".to_string(),
            "letrec".to_string(),
            "begin".to_string(),
            "hide".to_string(),
            "cons".to_string(),
            "strcons".to_string(),
            "car".to_string(),
            "cdr".to_string(),
            "commit".to_string(),
            "num".to_string(),
            "comm".to_string(),
            "char".to_string(),
            "open".to_string(),
            "secret".to_string(),
            "atom".to_string(),
            "emit".to_string(),
            "+".to_string(),
            "-".to_string(),
            "*".to_string(),
            "/".to_string(),
            "=".to_string(),
            "<".to_string(),
            ">".to_string(),
            "<=".to_string(),
            ">=".to_string(),
            "eq".to_string(),
            "current-env".to_string(),
            "if".to_string(),
            "terminal".to_string(),
            "dummy".to_string(),
            "outermost".to_string(),
            "error".to_string(),
        ]
    }
}

impl<F: LurkField> Store<F> {
    pub fn intern_syn(&mut self, input: Syn<F>) -> Ptr<F> {
        match input {
            Syn::BuiltIn(x) => self.intern_sym(x.sym()),
            Syn::ArithOp(x) => self.intern_sym(x.sym()),
            Syn::String(x) => self.intern_str(x),
            Syn::Symbol(x) => self.intern_sym(x),
            Syn::Num(x) => self.intern_num(Num::Scalar(x)),
            Syn::Char(x) => x.into(),
            Syn::UInt(x) => self.uint64(x),
            Syn::List(xs) => {
                let nil = self.intern_nil();
                xs.into_iter().rev().fold(nil, |acc, x| {
                    let x = self.intern_syn(x);
                    self.intern_cons(x, acc)
                })
            }
            Syn::Improper(xs, end) => {
                let nil = self.intern_syn(*end);
                xs.into_iter().rev().fold(nil, |acc, x| {
                    let x = self.intern_syn(x);
                    self.intern_cons(x, acc)
                })
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::field::FWrap;
    use blstrs::Scalar as Fr;

    use quickcheck::{Arbitrary, Gen};

    use crate::test::frequency;
    use im::Vector;

    impl Syn<Fr> {}
    impl Arbitrary for ArithOp {
        fn arbitrary(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> ArithOp>)> = vec![
                (100, Box::new(|_| Self::Add)),
                (100, Box::new(|_| Self::Sub)),
                (100, Box::new(|_| Self::Mul)),
                (100, Box::new(|_| Self::Div)),
                (100, Box::new(|_| Self::Mod)),
                (100, Box::new(|_| Self::Gth)),
                (100, Box::new(|_| Self::Gte)),
                (100, Box::new(|_| Self::Lth)),
                (100, Box::new(|_| Self::Lte)),
                (100, Box::new(|_| Self::Eql)),
            ];
            frequency(g, input)
        }
    }
    impl Arbitrary for BuiltIn {
        fn arbitrary(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> BuiltIn>)> = vec![
                (100, Box::new(|_| Self::T)),
                (100, Box::new(|_| Self::Nil)),
                (100, Box::new(|_| Self::If)),
                (100, Box::new(|_| Self::Lambda)),
                (100, Box::new(|_| Self::Let)),
                (100, Box::new(|_| Self::LetRec)),
                (100, Box::new(|_| Self::Quote)),
                (100, Box::new(|_| Self::Atom)),
                (100, Box::new(|_| Self::FunctionP)),
                (100, Box::new(|_| Self::Cons)),
                (100, Box::new(|_| Self::StrCons)),
                (100, Box::new(|_| Self::Car)),
                (100, Box::new(|_| Self::Cdr)),
                (100, Box::new(|_| Self::Num)),
                (100, Box::new(|_| Self::U64)),
                (100, Box::new(|_| Self::Char)),
                (100, Box::new(|_| Self::Eq)),
                (100, Box::new(|_| Self::Emit)),
                (100, Box::new(|_| Self::Begin)),
                (100, Box::new(|_| Self::CurrentEnv)),
                (100, Box::new(|_| Self::Eval)),
                (100, Box::new(|_| Self::Comm)),
                (100, Box::new(|_| Self::Commit)),
                (100, Box::new(|_| Self::Hide)),
                (100, Box::new(|_| Self::Open)),
            ];
            frequency(g, input)
        }
    }
    impl Syn<Fr> {
        fn arbitrary_syn(g: &mut Gen, ctx: Vector<String>) -> Self {
            let len: i64 = ctx.len() as i64;
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Syn<Fr>>)> = vec![
                (100, Box::new(|g| Self::Num(FWrap::arbitrary(g).0))),
                (100, Box::new(|g| Self::UInt(u64::arbitrary(g)))),
                (100, Box::new(|g| Self::Char(char::arbitrary(g)))),
                (100, Box::new(|_| Self::String("foobar".to_string()))),
                (100, Box::new(|g| Self::ArithOp(ArithOp::arbitrary(g)))),
                (100, Box::new(|g| Self::arbitrary_list(g, ctx.clone()))),
                (100, Box::new(|g| Self::arbitrary_lam(g, ctx.clone()))),
                (100 * len, Box::new(|g| Self::arbitrary_sym(g, ctx.clone()))),
            ];
            frequency(g, input)
        }

        fn arbitrary_var(g: &mut Gen) -> String {
            let varn: u8 = Arbitrary::arbitrary(g);
            let vari: u8 = Arbitrary::arbitrary(g);
            format!("{}{}", ((varn % 26) + 65) as char, vari % 10)
        }

        fn arbitrary_lam(g: &mut Gen, ctx: Vector<String>) -> Self {
            let num_vars: usize = Arbitrary::arbitrary(g);
            let num_vars = num_vars % 3;
            let mut vars = Vec::new();
            let mut ctx2 = ctx.clone();
            for _ in 0..num_vars {
                let var = Syn::arbitrary_var(g);
                vars.push(Syn::Symbol(var.clone()));
                ctx2.push_front(var);
            }
            let arg = Syn::arbitrary_syn(g, ctx2);
            Syn::List(vec![Syn::BuiltIn(BuiltIn::Lambda), Syn::List(vars), arg])
        }

        fn arbitrary_list(g: &mut Gen, ctx: Vector<String>) -> Self {
            let num_exprs: usize = Arbitrary::arbitrary(g);
            let num_exprs = num_exprs % 3;
            let mut exprs = Vec::new();
            for _ in 0..num_exprs {
                let expr = Syn::arbitrary_syn(g, ctx.clone());
                exprs.push(expr);
            }
            let improper: bool = Arbitrary::arbitrary(g);
            if improper && num_exprs != 0 {
                let end = Syn::arbitrary_syn(g, ctx.clone());
                Syn::Improper(exprs, Box::new(end))
            } else {
                Syn::List(exprs)
            }
        }

        fn arbitrary_sym(g: &mut Gen, ctx: Vector<String>) -> Self {
            if ctx.len() == 0 {
                return Syn::Symbol(Syn::arbitrary_var(g));
            } else {
                let var: usize = Arbitrary::arbitrary(g);
                let var = &ctx[var % ctx.len()];
                Syn::Symbol(var.clone())
            }
        }
    }

    impl Arbitrary for Syn<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            Syn::arbitrary_syn(g, vec![].into())
        }
    }
    //#[test]
    //fn unit_syn_generates() {
    //    let test = |src, syn| {
    //        let mut store1 = Store::<Fr>::default();
    //        let mut store2 = Store::<Fr>::default();
    //    }
    //
    //    println!(
    //        "{}",
    //        Syn::<Fr>::Improper(
    //            vec![Syn::Symbol("X".to_string()), Syn::Symbol("Y".to_string())],
    //            Box::new(Syn::Symbol("Z".to_string()))
    //        )
    //    );
    //    println!(
    //        "{}",
    //        Syn::<Fr>::List(vec![
    //            Syn::Symbol("X".to_string()),
    //            Syn::Symbol("Y".to_string()),
    //            Syn::Symbol("Z".to_string()),
    //        ])
    //    );
    //    println!("{}", Syn::<Fr>::List(vec![]));
    //    println!("{}", BuiltIn::Nil);
    //    println!("{}", Syn::<Fr>::List(vec![Syn::BuiltIn(BuiltIn::Nil)]));
    //    println!(
    //        "{}",
    //        Syn::<Fr>::Improper(vec![], Box::new(Syn::Symbol("Z".to_string())))
    //    );
    //}

    #[quickcheck]
    fn prop_syn_generates(syn: Syn<Fr>) -> bool {
        println!("-------------");
        let mut store1 = Store::<Fr>::default();
        let ptr1 = store1.intern_syn(syn.clone());
        let mut store2 = Store::<Fr>::default();
        println!("{}", &syn.to_string());
        let ptr2 = store2.read(&syn.to_string());
        if ptr2.is_err() {
            println!("{:?}", ptr2);
            return false;
        }
        let x = ptr1.fmt_to_string(&store1);
        let y = ptr2.unwrap().fmt_to_string(&store2);
        println!("{}", x);
        println!("{}", y);
        x == y
    }
}
