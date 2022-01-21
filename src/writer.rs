use std::io;

use crate::pool::{ContPtr, Continuation, Expression, Pool, Ptr};

pub trait Write {
    fn fmt<W: io::Write>(&self, pool: &Pool, w: &mut W) -> io::Result<()>;
    fn fmt_to_string(&self, pool: &Pool) -> String {
        let mut out = Vec::new();
        self.fmt(pool, &mut out).expect("preallocated");
        String::from_utf8(out).expect("I know it")
    }
}

impl Write for Ptr {
    fn fmt<W: io::Write>(&self, pool: &Pool, w: &mut W) -> io::Result<()> {
        if let Some(expr) = pool.fetch(self) {
            expr.fmt(pool, w)
        } else {
            Ok(())
        }
    }
}

impl Write for ContPtr {
    fn fmt<W: io::Write>(&self, pool: &Pool, w: &mut W) -> io::Result<()> {
        if let Some(expr) = pool.fetch_cont(self) {
            expr.fmt(pool, w)
        } else {
            Ok(())
        }
    }
}

impl Write for Expression {
    fn fmt<W: io::Write>(&self, pool: &Pool, w: &mut W) -> io::Result<()> {
        use Expression::*;

        match self {
            Nil => write!(w, "NIL"),
            Sym(s) => write!(w, "{}", s),
            Str(s) => write!(w, "\"{}\"", s),
            Fun(arg, body, _closed_env) => {
                let arg = pool.fetch(arg).unwrap();
                let body = pool.fetch(body).unwrap();
                write!(w, "<FUNCTION (")?;
                arg.fmt(pool, w)?;
                write!(w, ") . ")?;
                body.fmt(pool, w)?;
                write!(w, ">")
            }
            Num(n) => write!(w, "Fr(0x{:x})", n),
            Thunk(f) => {
                write!(w, "Thunk for cont ")?;
                f.continuation.fmt(pool, w)?;
                write!(w, " with value: ")?;
                f.value.fmt(pool, w)
            }
            Cons(_, _) => {
                write!(w, "(")?;
                self.print_tail(pool, w)
            }
        }
    }
}

impl Expression {
    fn print_tail<W: io::Write>(&self, pool: &Pool, w: &mut W) -> io::Result<()> {
        match self {
            Expression::Nil => write!(w, ")"),
            Expression::Cons(car, cdr) => {
                let car = pool.fetch(car).unwrap();
                let cdr = pool.fetch(cdr).unwrap();
                match cdr {
                    Expression::Nil => {
                        car.fmt(pool, w)?;
                        write!(w, ")")
                    }
                    Expression::Cons(_, _) => {
                        car.fmt(pool, w)?;
                        write!(w, " ")?;
                        cdr.print_tail(pool, w)
                    }
                    _ => {
                        car.fmt(pool, w)?;
                        write!(w, " . ")?;
                        cdr.fmt(pool, w)?;
                        write!(w, ")")
                    }
                }
            }
            _ => unreachable!(),
        }
    }
}

impl Write for Continuation {
    fn fmt<W: io::Write>(&self, pool: &Pool, w: &mut W) -> io::Result<()> {
        match self {
            Continuation::Outermost => write!(w, "Outermost"),
            Continuation::Simple(cont) => {
                write!(w, "Simple(")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Call(expr1, expr2, cont) => {
                write!(w, "Call(")?;
                expr1.fmt(pool, w)?;
                write!(w, ", ")?;
                expr2.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Call2(expr1, expr2, cont) => {
                write!(w, "Call2(")?;
                expr1.fmt(pool, w)?;
                write!(w, ", ")?;
                expr2.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Tail(expr, cont) => {
                write!(w, "Tail(")?;
                expr.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Error => write!(w, "Error"),
            Continuation::Lookup(expr, cont) => {
                write!(w, "Lookup(")?;
                expr.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Unop(op1, cont) => {
                write!(w, "Unop({}, ", op1)?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Binop(op2, expr1, expr2, cont) => {
                write!(w, "Binop(")?;
                write!(w, "{}", op2)?;
                write!(w, ", ")?;
                expr1.fmt(pool, w)?;
                write!(w, ", ")?;
                expr2.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Binop2(op2, expr, cont) => {
                write!(w, "Binop2({}, ", op2)?;
                expr.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Relop(rel2, expr1, expr2, cont) => {
                write!(w, "Relop({}, ", rel2)?;
                expr1.fmt(pool, w)?;
                write!(w, ", ")?;
                expr2.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Relop2(rel2, expr, cont) => {
                write!(w, "Relop2({}, ", rel2)?;
                expr.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::If(expr, cont) => {
                write!(w, "If(")?;
                expr.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::LetStar(expr1, expr2, expr3, cont) => {
                write!(w, "LetStar(")?;
                expr1.fmt(pool, w)?;
                write!(w, ", ")?;
                expr2.fmt(pool, w)?;
                write!(w, ", ")?;
                expr3.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::LetRecStar(expr1, expr2, expr3, cont) => {
                write!(w, "LetRecStar(")?;
                expr1.fmt(pool, w)?;
                write!(w, ", ")?;
                expr2.fmt(pool, w)?;
                write!(w, ", ")?;
                expr3.fmt(pool, w)?;
                write!(w, ", ")?;
                cont.fmt(pool, w)?;
                write!(w, ")")
            }
            Continuation::Dummy => write!(w, "Dummy"),
            Continuation::Terminal => write!(w, "Terminal"),
        }
    }
}
