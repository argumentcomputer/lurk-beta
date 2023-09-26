use crate::cont::Continuation;
use crate::expr::Expression;
use crate::field::LurkField;
use crate::lurk_sym_ptr;
use crate::package::SymbolRef;
use crate::ptr::{ContPtr, Ptr};
use crate::state::State;
use crate::store::Store;
use crate::symbol::Symbol;
use crate::z_expr::ZExpr;
use std::io;

pub trait Write<F: LurkField> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, state: &State, w: &mut W) -> io::Result<()>;
    fn fmt_to_string(&self, store: &Store<F>, state: &State) -> String {
        let mut out = Vec::new();
        self.fmt(store, state, &mut out).expect("preallocated");
        String::from_utf8(out).expect("I know it")
    }
}

impl<F: LurkField> Write<F> for Ptr<F> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, state: &State, w: &mut W) -> io::Result<()> {
        if self.is_opaque() {
            // This should never fail.
            write!(w, "<Opaque ")?;
            write!(w, "{:?}", self.tag)?;

            if let Some(x) = store.hash_expr(self) {
                write!(w, " ")?;
                crate::expr::Expression::Num(crate::num::Num::Scalar(*x.value()))
                    .fmt(store, state, w)?;
            }
            write!(w, ">")
        } else if let Some(expr) = store.fetch(self) {
            expr.fmt(store, state, w)
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                "Cannot find expression pointer",
            ))
        }
    }
}

impl<F: LurkField> Write<F> for ContPtr<F> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, state: &State, w: &mut W) -> io::Result<()> {
        if let Some(cont) = store.fetch_cont(self) {
            cont.fmt(store, state, w)
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                "Cannot find continuation pointer",
            ))
        }
    }
}

fn write_symbol<W: io::Write>(w: &mut W, sym: Symbol, state: &State) -> io::Result<()> {
    write!(w, "{}", state.fmt_to_string(&SymbolRef::new(sym)))
}

impl<F: LurkField> Write<F> for Expression<F> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, state: &State, w: &mut W) -> io::Result<()> {
        use Expression::{
            Char, Comm, Cons, EmptyStr, Fun, Key, Nil, Num, RootKey, RootSym, Str, Sym, Thunk, UInt,
        };

        match self {
            Nil => write!(w, "nil"),
            RootSym => write_symbol(w, Symbol::root_sym(), state),
            RootKey => write_symbol(w, Symbol::root_key(), state),
            Sym(car, cdr) => {
                let head = store.fetch_string(car).expect("missing symbol head");
                let tail = store.fetch_sym(cdr).expect("missing symbol tail");
                write_symbol(w, tail.extend(&[head]), state)
            }
            Key(car, cdr) => {
                let head = store.fetch_string(car).expect("missing keyword head");
                let mut tail = store.fetch_sym(cdr).expect("missing keyword tail");
                tail.set_as_keyword();
                write_symbol(w, tail.extend(&[head]), state)
            }
            EmptyStr => write!(w, "\"\""),
            Str(car, cdr) => {
                let head = store.fetch_char(car).expect("missing string head");
                let tail = store.fetch_string(cdr).expect("missing string tail");
                write!(w, "\"{head}{tail}\"")
            }
            Fun(arg, body, _closed_env) => {
                let is_zero_arg = *arg == lurk_sym_ptr!(store, dummy);
                let arg = store.fetch(arg).unwrap();
                write!(w, "<FUNCTION (")?;
                if !is_zero_arg {
                    arg.fmt(store, state, w)?;
                }
                write!(w, ") ")?;

                //Assume body is a single-element cons, ignore the cdr
                match store.fetch(body).unwrap() {
                    Expression::Cons(expr, _) => {
                        let expr = store.fetch(&expr).unwrap();
                        expr.fmt(store, state, w)?;
                    }
                    Expression::Nil => {
                        lurk_sym_ptr!(store, nil).fmt(store, state, w)?;
                    }
                    _ => {
                        panic!("Function body was neither a Cons nor Nil");
                    }
                }
                write!(w, ">")
            }
            Num(n) => write!(w, "{n}"),
            Thunk(f) => {
                write!(w, "Thunk{{ value: ")?;
                f.value.fmt(store, state, w)?;
                write!(w, " => cont: ")?;
                f.continuation.fmt(store, state, w)?;
                write!(w, "}}")
            }
            Cons(_, _) => {
                write!(w, "(")?;
                self.print_tail(store, state, w)
            }
            Comm(secret, payload) => {
                // This requires a run-time coercion.
                // Consider implementing the equivalent of CL's #. reader macro to let this happen at read-time.
                write!(w, "(comm ")?;
                let c = ZExpr::Comm(*secret, store.hash_expr(payload).unwrap())
                    .z_ptr(&store.poseidon_cache);
                Num(crate::num::Num::Scalar(c.1)).fmt(store, state, w)?;
                write!(w, ")")
            }
            Char(c) => {
                write!(w, "'{c}'")
            }
            UInt(n) => write!(w, "{n}u64"),
        }
    }
}

impl<F: LurkField> Expression<F> {
    fn print_tail<W: io::Write>(
        &self,
        store: &Store<F>,
        state: &State,
        w: &mut W,
    ) -> io::Result<()> {
        match self {
            Expression::Nil => write!(w, ")"),
            Expression::Cons(car, cdr) => {
                let car = store.fetch(car);
                let cdr = store.fetch(cdr);
                let fmt_car = |store, w: &mut W| {
                    if let Some(car) = car {
                        car.fmt(store, state, w)
                    } else {
                        write!(w, "<Opaque>")
                    }
                };
                let fmt_cdr = |store, w: &mut W| {
                    if let Some(cdr) = &cdr {
                        cdr.fmt(store, state, w)
                    } else {
                        write!(w, "<Opaque>")
                    }
                };

                match cdr {
                    Some(Expression::Nil) => {
                        fmt_car(store, w)?;
                        write!(w, ")")
                    }
                    Some(Expression::Cons(_, _)) => {
                        fmt_car(store, w)?;
                        write!(w, " ")?;
                        if let Some(cdr) = cdr {
                            cdr.print_tail(store, state, w)
                        } else {
                            write!(w, "<Opaque Tail>")
                        }
                    }
                    Some(_) => {
                        fmt_car(store, w)?;
                        write!(w, " . ")?;
                        fmt_cdr(store, w)?;
                        write!(w, ")")
                    }
                    None => write!(w, "<Opaque>"),
                }
            }
            expr => expr.fmt(store, state, w),
        }
    }
}

impl<F: LurkField> Write<F> for Continuation<F> {
    fn fmt<W: io::Write>(&self, store: &Store<F>, state: &State, w: &mut W) -> io::Result<()> {
        match self {
            Continuation::Outermost => write!(w, "Outermost"),
            Continuation::Call0 {
                saved_env,
                continuation,
            } => {
                write!(w, "Call0{{ saved_env: ")?;
                saved_env.fmt(store, state, w)?;
                write!(w, ", ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => {
                write!(w, "Call{{ unevaled_arg: ")?;
                unevaled_arg.fmt(store, state, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, state, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Call2 {
                function,
                saved_env,
                continuation,
            } => {
                write!(w, "Call2{{ function: ")?;
                function.fmt(store, state, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, state, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Tail {
                saved_env,
                continuation,
            } => {
                write!(w, "Tail{{ saved_env: ")?;
                saved_env.fmt(store, state, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Error => write!(w, "Error"),
            Continuation::Lookup {
                saved_env,
                continuation,
            } => {
                write!(w, "Lookup{{ saved_env: ")?;
                saved_env.fmt(store, state, w)?;
                write!(w, ", ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Unop {
                operator,
                continuation,
            } => {
                write!(w, "Unop{{ operator: {operator}, continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => {
                write!(w, "Binop{{ operator: ")?;
                write!(w, "{operator}, unevaled_args: ")?;
                unevaled_args.fmt(store, state, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, state, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => {
                write!(w, "Binop2{{ operator: {operator}, evaled_arg: ")?;
                evaled_arg.fmt(store, state, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::If {
                unevaled_args,
                continuation,
            } => {
                write!(w, "If{{ unevaled_args: ")?;
                unevaled_args.fmt(store, state, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Let {
                var,
                body,
                saved_env,
                continuation,
            } => {
                write!(w, "Let{{ var: ")?;
                var.fmt(store, state, w)?;
                write!(w, ", body: ")?;
                body.fmt(store, state, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, state, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::LetRec {
                var,
                saved_env,
                body,
                continuation,
            } => {
                write!(w, "LetRec{{var: ")?;
                var.fmt(store, state, w)?;
                write!(w, ", saved_env: ")?;
                saved_env.fmt(store, state, w)?;
                write!(w, ", body: ")?;
                body.fmt(store, state, w)?;
                write!(w, ", continuation: ")?;
                continuation.fmt(store, state, w)?;
                write!(w, " }}")
            }
            Continuation::Dummy => write!(w, "Dummy"),
            Continuation::Terminal => write!(w, "Terminal"),
            Continuation::Emit {
                continuation: _continuation,
            } => {
                write!(w, "Emit")?;
                write!(w, "<CONTINUATION>") // Omit continuation for clarity when logging and using output.
                                            // write!(w, " {{ continuation: ")?;
                                            // continuation.fmt(store, state, w)?;
                                            // write!(w, " }}")
            }
        }
    }
}

#[cfg(test)]
pub mod test {
    use crate::state::initial_lurk_state;

    use super::*;
    use pasta_curves::pallas::Scalar as Fr;

    #[test]
    fn print_expr() {
        let mut s = Store::<Fr>::default();
        let state = &mut State::init_lurk_state();
        let nil = lurk_sym_ptr!(s, nil);
        let x = s.user_sym("x");
        state.intern("x");
        let lambda = lurk_sym_ptr!(&s, lambda);
        let val = s.num(123);
        let lambda_args = s.cons(x, nil);
        let body = s.cons(x, nil);
        let rest = s.cons(lambda_args, body);
        let whole_lambda = s.cons(lambda, rest);
        let lambda_arguments = s.cons(val, nil);
        let expr = s.cons(whole_lambda, lambda_arguments);
        let output = expr.fmt_to_string(&s, state);

        assert_eq!("((lambda (x) x) 123)".to_string(), output);
    }

    #[test]
    fn test_print_num() {
        let mut store = Store::<Fr>::default();
        let num = store.num(5);
        let res = num.fmt_to_string(&store, initial_lurk_state());
        assert_eq!(&res, &"5");
    }

    #[test]
    fn test_print_char() {
        let store = Store::<Fr>::default();
        let char = store.intern_char('a');
        let res = char.fmt_to_string(&store, initial_lurk_state());
        assert_eq!(&res, &"'a'");
    }

    #[test]
    fn test_print_keyword() {
        let mut store = Store::<Fr>::default();
        let foo_key_ptr = store.intern_symbol(&Symbol::key_from_vec(vec!["foo".into()]));
        let foo_key_str = foo_key_ptr.fmt_to_string(&store, initial_lurk_state());
        assert_eq!(":foo", foo_key_str);
    }
}
