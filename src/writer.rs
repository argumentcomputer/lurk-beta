use std::io;

use ff::PrimeField;

use crate::store::{ContPtr, Continuation, Expression, Ptr, Store};

pub trait Write<F: PrimeField> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, w: &mut W) -> io::Result<()>;
    fn fmt_to_string(&self, store: &Store<F>) -> String {
        let mut out = Vec::new();
        self.fmt(store, &mut out).expect("preallocated");
        String::from_utf8(out).expect("I know it")
    }
}

impl<F: PrimeField> Write<F> for Ptr<F> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, w: &mut W) -> io::Result<()> {
        if let Some(expr) = store.fetch(self) {
            expr.fmt(store, w)
        } else {
            Ok(())
        }
    }
}

impl<F: PrimeField> Write<F> for ContPtr<F> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, w: &mut W) -> io::Result<()> {
        if let Some(cont) = store.fetch_cont(self) {
            cont.fmt(store, w)
        } else {
            Ok(())
        }
    }
}

impl<F: PrimeField> Write<F> for Expression<'_, F> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, w: &mut W) -> io::Result<()> {
        use Expression::*;

        match self {
            Nil => write!(w, "NIL"),
            Sym(s) => write!(w, "{}", s),
            Str(s) => write!(w, "\"{}\"", s),
            Fun(arg, body, _closed_env) => {
                let arg = store.fetch(arg).unwrap();
                let body = store.fetch(body).unwrap();
                write!(w, "<FUNCTION (")?;
                arg.fmt(store, w)?;
                write!(w, ") . ")?;
                body.fmt(store, w)?;
                write!(w, ">")
            }
            Num(n) => write!(w, "{}", n),
            Thunk(f) => {
                write!(w, "Thunk for cont ")?;
                f.continuation.fmt(store, w)?;
                write!(w, " with value: ")?;
                f.value.fmt(store, w)
            }
            Cons(_, _) => {
                write!(w, "(")?;
                self.print_tail(store, w)
            }
        }
    }
}

impl<F: PrimeField> Expression<'_, F> {
    fn print_tail<W: io::Write>(&self, store: &Store<F>, w: &mut W) -> io::Result<()> {
        match self {
            Expression::Nil => write!(w, ")"),
            Expression::Cons(car, cdr) => {
                let car = store.fetch(car).unwrap();
                let cdr = store.fetch(cdr).unwrap();
                match cdr {
                    Expression::Nil => {
                        car.fmt(store, w)?;
                        write!(w, ")")
                    }
                    Expression::Cons(_, _) => {
                        car.fmt(store, w)?;
                        write!(w, " ")?;
                        cdr.print_tail(store, w)
                    }
                    _ => {
                        car.fmt(store, w)?;
                        write!(w, " . ")?;
                        cdr.fmt(store, w)?;
                        write!(w, ")")
                    }
                }
            }
            _ => unreachable!(),
        }
    }
}

impl<F: PrimeField> Write<F> for Continuation<F> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, w: &mut W) -> io::Result<()> {
        match self {
            Continuation::Outermost => write!(w, "Outermost"),
            Continuation::Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => {
                write!(w, "Call{{ unevaled_arg: ")?;
                unevaled_arg.fmt(store, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Call2 {
                function,
                saved_env,
                continuation,
            } => {
                write!(w, "Call2{{ function: ")?;
                function.fmt(store, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Tail {
                saved_env,
                continuation,
            } => {
                write!(w, "Tail{{ saved_env: ")?;
                saved_env.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Error => write!(w, "Error"),
            Continuation::Lookup {
                saved_env,
                continuation,
            } => {
                write!(w, "Lookup{{ saved_env: ")?;
                saved_env.fmt(store, w)?;
                write!(w, ", ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Unop {
                operator,
                continuation,
            } => {
                write!(w, "Unop{{ operator: {}, continuation: ", operator)?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => {
                write!(w, "Binop{{ operator: ")?;
                write!(w, "{}, saved_env: ", operator)?;
                saved_env.fmt(store, w)?;
                write!(w, ", unevaled_args: ")?;
                unevaled_args.fmt(store, w)?;
                write!(w, ", continuation")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => {
                write!(w, "Binop2{{ operator: {}, evaled_arg: ", operator)?;
                evaled_arg.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Relop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => {
                write!(w, "Relop{{ operator: {}, saved_env: ", operator)?;
                saved_env.fmt(store, w)?;
                write!(w, ", unevaled_args: ")?;
                unevaled_args.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, ")")
            }
            Continuation::Relop2 {
                operator,
                evaled_arg,
                continuation,
            } => {
                write!(w, "Relop2{{ operator: {}, evaled_ag: ", operator)?;
                evaled_arg.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::If {
                unevaled_args,
                continuation,
            } => {
                write!(w, "If{{ unevaled_args: ")?;
                unevaled_args.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Let {
                var,
                body,
                saved_env,
                continuation,
            } => {
                write!(w, "Let{{ var: ")?;
                var.fmt(store, w)?;
                write!(w, ", body: ")?;
                body.fmt(store, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::LetRec {
                var,
                saved_env,
                body,
                continuation,
            } => {
                write!(w, "LetRec{{var: ")?;
                var.fmt(store, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, w)?;
                write!(w, ", body: ")?;
                body.fmt(store, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, w)?;
                write!(w, " }}")
            }
            Continuation::Dummy => write!(w, "Dummy"),
            Continuation::Terminal => write!(w, "Terminal"),
        }
    }
}
