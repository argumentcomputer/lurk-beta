use super::{empty_sym_env, Witness};
use crate::error::ReductionError;
use crate::field::LurkField;
use crate::hash_witness::{ConsName, ConsWitness, ContName, ContWitness};
use crate::num::Num;
use crate::store;
use crate::store::{
    ContPtr, Continuation, Expression, NamedConstants, Pointer, Ptr, Store, Thunk, TypePredicates,
};
use crate::tag::{ContTag, ExprTag, Op1, Op2};
use crate::writer::Write;

pub fn reduce<F: LurkField>(
    expr: Ptr<F>,
    env: Ptr<F>,
    cont: ContPtr<F>,
    store: &mut Store<F>,
) -> Result<(Ptr<F>, Ptr<F>, ContPtr<F>, Witness<F>), ReductionError> {
    let c = *store.get_constants();
    let (ctrl, witness) = reduce_with_witness(expr, env, cont, store, &c)?;
    let (new_expr, new_env, new_cont) = ctrl.into_results(store);

    Ok((new_expr, new_env, new_cont, witness))
}

#[derive(Debug, Clone)]
pub enum Control<F: LurkField> {
    Return(Ptr<F>, Ptr<F>, ContPtr<F>),
    MakeThunk(Ptr<F>, Ptr<F>, ContPtr<F>),
    ApplyContinuation(Ptr<F>, Ptr<F>, ContPtr<F>),
    Error(Ptr<F>, Ptr<F>),
}

impl<F: LurkField> Control<F> {
    pub fn into_results(self, store: &mut Store<F>) -> (Ptr<F>, Ptr<F>, ContPtr<F>) {
        match self {
            Self::Return(expr, env, cont) => (expr, env, cont),
            Self::MakeThunk(expr, env, cont) => (expr, env, cont),
            Self::ApplyContinuation(expr, env, cont) => (expr, env, cont),
            Self::Error(expr, env) => (expr, env, store.intern_cont_error()),
        }
    }
    pub fn is_return(&self) -> bool {
        matches!(self, Self::Return(_, _, _))
    }
    pub fn is_make_thunk(&self) -> bool {
        matches!(self, Self::MakeThunk(_, _, _))
    }
    pub fn is_apply_continuation(&self) -> bool {
        matches!(self, Self::ApplyContinuation(_, _, _))
    }
}

fn reduce_with_witness_inner<F: LurkField>(
    expr: Ptr<F>,
    env: Ptr<F>,
    cont: ContPtr<F>,
    store: &mut Store<F>,
    cons_witness: &mut ConsWitness<F>,
    cont_witness: &mut ContWitness<F>,
    c: &NamedConstants<F>,
) -> Result<(Control<F>, Option<Ptr<F>>), ReductionError> {
    let mut closure_to_extend = None;

    Ok((
        if matches!(cont.tag(), ContTag::Terminal | ContTag::Error) {
            Control::Return(expr, env, cont)
        } else {
            match expr.tag() {
                // Self-evaluating
                ExprTag::Nil
                | ExprTag::Fun
                | ExprTag::Num
                | ExprTag::Str
                | ExprTag::Char
                | ExprTag::Comm
                | ExprTag::U64
                | ExprTag::Key => {
                    debug_assert!(expr.tag().is_self_evaluating());
                    Control::ApplyContinuation(expr, env, cont)
                }

                ExprTag::Thunk => match store
                    .fetch(&expr)
                    .ok_or_else(|| store::Error("Fetch failed".into()))?
                {
                    Expression::Thunk(thunk) => {
                        Control::ApplyContinuation(thunk.value, env, thunk.continuation)
                    }
                    _ => unreachable!(),
                },

                ExprTag::Sym => {
                    if expr == c.nil.ptr() || (expr == store.t()) {
                        // NIL and T are self-evaluating symbols, pass them to the continuation in a thunk.
                        // NOTE: For now, NIL is its own type, but this will change soon, so leave the check here.

                        // CIRCUIT: sym_is_self_evaluating
                        Control::ApplyContinuation(expr, env, cont)
                    } else {
                        // Otherwise, look for a matching binding in env.

                        // CIRCUIT: sym_otherwise
                        if env.is_nil() {
                            // CIRCUIT: needed_env_missing
                            Control::Error(expr, env)
                        } else {
                            // CIRCUIT: main
                            let (binding, smaller_env) =
                                cons_witness.car_cdr_named(ConsName::Env, store, &env)?;
                            if binding.is_nil() {
                                // If binding is NIL, it's empty. There is no match. Return an error due to unbound variable.

                                // CIRCUIT: needed_binding_missing
                                Control::Error(expr, env)
                            } else {
                                // Binding is not NIL, so it is either a normal binding or a recursive environment.

                                // CIRCUIT: with_binding
                                let (var_or_rec_binding, val_or_more_rec_env) = cons_witness
                                    .car_cdr_named(ConsName::EnvCar, store, &binding)?;

                                match var_or_rec_binding.tag() {
                                    ExprTag::Sym => {
                                        // We are in a simple env (not a recursive env),
                                        // looking at a binding's variable.

                                        // CIRCUIT: with_sym_binding

                                        let v = var_or_rec_binding;
                                        let val = val_or_more_rec_env;

                                        if v == expr {
                                            // expr matches the binding's var.

                                            // CIRCUIT: with_sym_binding_matched

                                            // Pass the binding's value to the continuation in a thunk.
                                            Control::ApplyContinuation(val, env, cont)
                                        } else {
                                            // expr does not match the binding's var.

                                            // CIRCUIT: with_sym_binding_unmatched
                                            match cont.tag() {
                                                ContTag::Lookup => {
                                                    // If performing a lookup, continue with remaining env.

                                                    // CIRCUIT: with_sym_binding_unmatched_old_lookup
                                                    Control::Return(expr, smaller_env, cont)
                                                }
                                                _ =>
                                                // Otherwise, create a lookup continuation, packaging current env
                                                // to be restored later.

                                                // CIRCUIT: with_sym_binding_unmatched_new_lookup
                                                {
                                                    Control::Return(
                                                        expr,
                                                        smaller_env,
                                                        cont_witness.intern_named_cont(
                                                            ContName::Lookup,
                                                            store,
                                                            Continuation::Lookup {
                                                                saved_env: env,
                                                                continuation: cont,
                                                            },
                                                        ),
                                                    )
                                                }
                                            }
                                        }
                                    }
                                    // Start of a recursive_env.
                                    ExprTag::Cons => {
                                        // CIRCUIT: with_cons_binding

                                        let rec_env = binding;
                                        let smaller_rec_env = val_or_more_rec_env;

                                        let (v2, val2) = cons_witness.car_cdr_named(
                                            ConsName::EnvCaar,
                                            store,
                                            &var_or_rec_binding,
                                        )?;

                                        if v2 == expr {
                                            // CIRCUIT: with_cons_binding_matched

                                            let val_to_use = {
                                                // CIRCUIT: val_to_use
                                                match val2.tag() {
                                                    ExprTag::Fun => {
                                                        closure_to_extend = Some(val2);
                                                        // CIRCUIT: val2_is_fun

                                                        // We just found a closure in a recursive env.
                                                        // We need to extend its environment to include that recursive env.

                                                        // CIRCUIT: extended_fun
                                                        extend_closure(
                                                            &val2,
                                                            &rec_env,
                                                            store,
                                                            cons_witness,
                                                        )?
                                                    }
                                                    _ => {
                                                        closure_to_extend = None;
                                                        val2
                                                    }
                                                }
                                            };
                                            Control::ApplyContinuation(val_to_use, env, cont)
                                        } else {
                                            // CIRCUIT: with_cons_binding_unmatched
                                            let env_to_use = if smaller_rec_env.is_nil() {
                                                // CIRCUIT: smaller_rec_env_is_nil
                                                smaller_env
                                            } else {
                                                // CIRCUIT: rec_extended_env
                                                cons_witness.cons_named(
                                                    ConsName::EnvToUse,
                                                    store,
                                                    smaller_rec_env,
                                                    smaller_env,
                                                )
                                            };
                                            match cont.tag() {
                                                ContTag::Lookup => {
                                                    // CIRCUIT: with_cons_binding_unmatched_old_lookup
                                                    Control::Return(expr, env_to_use, cont)
                                                }
                                                _ => Control::Return(
                                                    // CIRCUIT: with_cons_binding_unmatched_new_lookup
                                                    expr,
                                                    env_to_use,
                                                    cont_witness.intern_named_cont(
                                                        ContName::Lookup,
                                                        store,
                                                        Continuation::Lookup {
                                                            saved_env: env,
                                                            continuation: cont,
                                                        },
                                                    ),
                                                ),
                                            }
                                        }
                                    }
                                    _ => Control::Error(expr, env), // CIRCUIT: with_other_binding
                                }
                            }
                        }
                    }
                }
                ExprTag::Cons => {
                    // This should not fail, since expr is a Cons.
                    let (head, rest) = cons_witness.car_cdr_named(ConsName::Expr, store, &expr)?;

                    let lambda = c.lambda.ptr();
                    let quote = c.quote.ptr();
                    let dummy_arg = c.dummy.ptr();

                    macro_rules! car_cdr_named {
                        ($cons_name:expr, $cons:expr) => {{
                            let pair = cons_witness.car_cdr_named($cons_name, store, $cons);

                            if matches!(pair, Err(ReductionError::CarCdrType(_))) {
                                return Ok((Control::Error(expr, env), None));
                            } else {
                                pair
                            }
                        }};
                    }

                    if head == lambda {
                        let (args, body) = car_cdr_named!(ConsName::ExprCdr, &rest)?;
                        let (arg, _rest) = if args.is_nil() {
                            // (LAMBDA () STUFF)
                            // becomes (LAMBDA (DUMMY) STUFF)
                            (dummy_arg, store.nil())
                        } else {
                            cons_witness.car_cdr_named(ConsName::ExprCadr, store, &args)?
                        };
                        if arg.tag() != ExprTag::Sym {
                            Control::Error(expr, env)
                        } else {
                            let (_, cdr_args) =
                                cons_witness.car_cdr_named(ConsName::ExprCadr, store, &args)?;
                            let inner_body = if cdr_args.is_nil() {
                                body
                            } else {
                                // (LAMBDA (A B) STUFF)
                                // becomes (LAMBDA (A) (LAMBDA (B) STUFF))
                                let inner = cons_witness.cons_named(
                                    ConsName::InnerLambda,
                                    store,
                                    cdr_args,
                                    body,
                                );
                                let l =
                                    cons_witness.cons_named(ConsName::Lambda, store, lambda, inner);
                                let nil = store.nil();
                                cons_witness.cons_named(ConsName::InnerBody, store, l, nil)
                            };
                            let function = store.intern_fun(arg, inner_body, env);

                            Control::ApplyContinuation(function, env, cont)
                        }
                    } else if head == quote {
                        let (quoted, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::ApplyContinuation(quoted, env, cont)
                        }
                    } else if head == c.let_.ptr() || head == c.letrec.ptr() {
                        let (bindings, body) = car_cdr_named!(ConsName::ExprCdr, &rest)?;
                        let (body1, rest_body) =
                            cons_witness.car_cdr_named(ConsName::ExprCddr, store, &body)?;
                        // Only a single body form allowed for now.
                        if !rest_body.is_nil() || body.is_nil() {
                            Control::Error(expr, env)
                        } else if bindings.is_nil() {
                            Control::Return(body1, env, cont)
                        } else {
                            let (binding1, rest_bindings) =
                                cons_witness.car_cdr_named(ConsName::ExprCadr, store, &bindings)?;
                            let (var, vals) = cons_witness.car_cdr_named(
                                ConsName::ExprCaadr,
                                store,
                                &binding1,
                            )?;
                            if var.tag() != ExprTag::Sym {
                                Control::Error(expr, env)
                            } else {
                                let (val, end) = cons_witness.car_cdr_named(
                                    ConsName::ExprCaaadr,
                                    store,
                                    &vals,
                                )?;

                                if !end.is_nil() {
                                    Control::Error(expr, env)
                                } else {
                                    let head_ptr = c.let_.ptr();
                                    let expanded = if rest_bindings.is_nil() {
                                        body1
                                    } else {
                                        // We know body is a proper list equivalent to (body1), if this branch was taken, since end is nil.
                                        let expanded0 = cons_witness.cons_named(
                                            ConsName::ExpandedInner,
                                            store,
                                            rest_bindings,
                                            body,
                                        );
                                        cons_witness.cons_named(
                                            ConsName::Expanded,
                                            store,
                                            head,
                                            expanded0,
                                        )
                                    };
                                    let cont = if head == head_ptr {
                                        cont_witness.intern_named_cont(
                                            ContName::NewerCont,
                                            store,
                                            Continuation::Let {
                                                var,
                                                saved_env: env,
                                                body: expanded,
                                                continuation: cont,
                                            },
                                        )
                                    } else {
                                        cont_witness.intern_named_cont(
                                            ContName::NewerCont,
                                            store,
                                            Continuation::LetRec {
                                                var,
                                                saved_env: env,
                                                body: expanded,
                                                continuation: cont,
                                            },
                                        )
                                    };
                                    Control::Return(val, env, cont)
                                }
                            }
                        }
                    } else if head == c.cons.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Cons,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.strcons.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::StrCons,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.hide.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Hide,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.begin.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if more.is_nil() {
                            Control::Return(arg1, env, cont)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Begin,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.car.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Car,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.cdr.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Cdr,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.commit.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Commit,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.num.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Num,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.u64.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::U64,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.comm.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Comm,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.char.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Char,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.eval.ptr() {
                        if rest.is_nil() {
                            return Ok((Control::Error(expr, env), None));
                        }
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() {
                            Control::Error(expr, env)
                        } else if more.is_nil() {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Eval,
                                        continuation: cont,
                                    },
                                ),
                            )
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Eval,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.open.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Open,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.secret.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Secret,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.atom.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Atom,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.emit.ptr() {
                        let (arg1, end) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || !end.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Unop {
                                        operator: Op1::Emit,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.sum.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Sum,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.diff.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Diff,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.product.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Product,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.quotient.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Quotient,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.modulo.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Modulo,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.num_equal.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::NumEqual,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.equal.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Equal,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.less.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Less,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.greater.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::Greater,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.less_equal.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::LessEqual,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.greater_equal.ptr() {
                        let (arg1, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if rest.is_nil() || more.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::Return(
                                arg1,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Binop {
                                        operator: Op2::GreaterEqual,
                                        saved_env: env,
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.if_.ptr() {
                        let (condition, more) = car_cdr_named!(ConsName::ExprCdr, &rest)?;

                        if more.is_nil() {
                            Control::Error(condition, env)
                        } else {
                            Control::Return(
                                condition,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::If {
                                        unevaled_args: more,
                                        continuation: cont,
                                    },
                                ),
                            )
                        }
                    } else if head == c.current_env.ptr() {
                        if !rest.is_nil() {
                            Control::Error(expr, env)
                        } else {
                            Control::ApplyContinuation(env, env, cont)
                        }
                    } else {
                        // (fn . args)
                        let fun_form = head;
                        let args = rest;

                        // `fun_form` must be a function or potentially evaluate to one.
                        if !fun_form.is_potentially(ExprTag::Fun) {
                            Control::Error(expr, env)
                        } else if args.is_nil() {
                            Control::Return(
                                fun_form,
                                env,
                                cont_witness.intern_named_cont(
                                    ContName::NewerCont,
                                    store,
                                    Continuation::Call0 {
                                        saved_env: env,
                                        continuation: cont,
                                    },
                                ),
                            )
                        } else {
                            let (arg, more_args) = car_cdr_named!(ConsName::ExprCdr, &args)?;
                            match more_args.tag() {
                                // (fn arg)
                                // Interpreting as call.
                                ExprTag::Nil => Control::Return(
                                    fun_form,
                                    env,
                                    cont_witness.intern_named_cont(
                                        ContName::NewerCont,
                                        store,
                                        Continuation::Call {
                                            unevaled_arg: arg,
                                            saved_env: env,
                                            continuation: cont,
                                        },
                                    ),
                                ),
                                _ => {
                                    // Interpreting as multi-arg call.
                                    // (fn arg . more_args) => ((fn arg) . more_args)
                                    let nil = store.nil();
                                    let expanded_inner0 = cons_witness.cons_named(
                                        ConsName::ExpandedInner0,
                                        store,
                                        arg,
                                        nil,
                                    );
                                    let expanded_inner = cons_witness.cons_named(
                                        ConsName::ExpandedInner,
                                        store,
                                        fun_form,
                                        expanded_inner0,
                                    );
                                    let expanded = cons_witness.cons_named(
                                        ConsName::FunExpanded,
                                        store,
                                        expanded_inner,
                                        more_args,
                                    );
                                    Control::Return(expanded, env, cont)
                                }
                            }
                        }
                    }
                }
            }
        },
        closure_to_extend,
    ))
}

pub fn reduce_with_witness<F: LurkField>(
    expr: Ptr<F>,
    env: Ptr<F>,
    cont: ContPtr<F>,
    store: &mut Store<F>,
    c: &NamedConstants<F>,
) -> Result<(Control<F>, Witness<F>), ReductionError> {
    let cons_witness = &mut ConsWitness::<F>::new_dummy();
    let cont_witness = &mut ContWitness::<F>::new_dummy();

    let (control, closure_to_extend) =
        reduce_with_witness_inner(expr, env, cont, store, cons_witness, cont_witness, c)?;

    let (new_expr, new_env, new_cont) = control.clone().into_results(store);

    let mut witness = Witness {
        prethunk_output_expr: new_expr,
        prethunk_output_env: new_env,
        prethunk_output_cont: new_cont,

        closure_to_extend,
        apply_continuation_cont: None,
        conses: *cons_witness,
        conts: *cont_witness,
    };

    let control = apply_continuation(control, store, &mut witness, c)?;

    let ctrl = make_thunk(control, store, &mut witness)?;

    witness.conses.assert_invariants(store);
    witness.conts.assert_invariants(store);

    Ok((ctrl, witness))
}

fn apply_continuation<F: LurkField>(
    control: Control<F>,
    store: &mut Store<F>,
    witness: &mut Witness<F>,
    c: &NamedConstants<F>,
) -> Result<Control<F>, ReductionError> {
    if !control.is_apply_continuation() {
        return Ok(control);
    }

    let (result, env, cont) = control.into_results(store);

    witness.apply_continuation_cont = Some(cont);
    let cons_witness = &mut witness.conses;
    let cont_witness = &mut witness.conts;

    let control = match cont.tag() {
        ContTag::Terminal | ContTag::Error => Control::Return(result, env, cont),
        ContTag::Dummy => unreachable!("Dummy Continuation should never be applied."),
        ContTag::Outermost => Control::Return(result, env, store.intern_cont_terminal()),
        ContTag::Emit => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            // Although Emit has no effect within the computation, it has an externally-visible side effect of
            // manifesting an explicit Thunk in the expr register of the execution trace.
            Continuation::Emit { continuation } => Control::MakeThunk(result, env, continuation),
            _ => unreachable!(),
        },
        ContTag::Call0 => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Call0 {
                saved_env,
                continuation,
            } => match result.tag() {
                ExprTag::Fun => match store
                    .fetch(&result)
                    .ok_or_else(|| store::Error("Fetch failed".into()))?
                {
                    Expression::Fun(arg, body, closed_env) => {
                        if arg == c.dummy.ptr() {
                            if body.is_nil() {
                                Control::Error(result, env)
                            } else {
                                let (body_form, end) =
                                    cons_witness.car_cdr_named(ConsName::FunBody, store, &body)?;
                                if !end.is_nil() {
                                    Control::Error(result, env)
                                } else {
                                    let cont = make_tail_continuation(
                                        saved_env,
                                        continuation,
                                        store,
                                        cont_witness,
                                    );

                                    Control::Return(body_form, closed_env, cont)
                                }
                            }
                        } else {
                            // // Applying zero args to a non-zero arg function leaves it unchanged.
                            // // This is arguably consistent with auto-currying.
                            Control::Return(result, env, continuation)
                        }
                    }
                    _ => unreachable!(),
                }, // Bad function
                _ => Control::Error(result, env),
            },
            _ => unreachable!(),
        },
        ContTag::Call => match result.tag() {
            ExprTag::Fun => match cont_witness
                .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
                .ok_or_else(|| store::Error("Fetch failed".into()))?
            {
                Continuation::Call {
                    unevaled_arg,
                    saved_env,
                    continuation,
                } => {
                    let function = result;
                    let next_expr = unevaled_arg;

                    let newer_cont = cont_witness.intern_named_cont(
                        ContName::NewerCont2,
                        store,
                        Continuation::Call2 {
                            function,
                            saved_env,
                            continuation,
                        },
                    );
                    Control::Return(next_expr, env, newer_cont)
                }
                _ => unreachable!(),
            },
            _ => {
                // Bad function
                Control::Error(result, env)
            }
        },
        ContTag::Call2 => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Call2 {
                function,
                saved_env,
                continuation,
            } => match function.tag() {
                ExprTag::Fun => match store
                    .fetch(&function)
                    .ok_or_else(|| store::Error("Fetch failed".into()))?
                {
                    Expression::Fun(arg, body, closed_env) => {
                        if arg == c.dummy.ptr() {
                            return Ok(Control::Error(result, env));
                        }
                        if body.is_nil() {
                            Control::Error(result, env)
                        } else {
                            let (body_form, end) =
                                cons_witness.car_cdr_named(ConsName::FunBody, store, &body)?;

                            if !end.is_nil() {
                                Control::Error(result, env)
                            } else {
                                let newer_env = cons_witness.extend_named(
                                    ConsName::ClosedEnv,
                                    closed_env,
                                    arg,
                                    result,
                                    store,
                                );
                                let cont = make_tail_continuation(
                                    saved_env,
                                    continuation,
                                    store,
                                    cont_witness,
                                );
                                Control::Return(body_form, newer_env, cont)
                            }
                        }
                    }
                    _ => unreachable!(),
                },
                _ => {
                    // Call2 continuation contains a non-function
                    return Ok(Control::Error(result, env));
                }
            },
            _ => unreachable!(),
        },
        ContTag::Let => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Let {
                var,
                body,
                saved_env,
                continuation,
            } => {
                let extended_env =
                    cons_witness.extend_named(ConsName::Env, env, var, result, store);
                let c = make_tail_continuation(saved_env, continuation, store, cont_witness);

                Control::Return(body, extended_env, c)
            }
            _ => unreachable!(),
        },
        ContTag::LetRec => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::LetRec {
                var,
                body,
                saved_env,
                continuation,
            } => {
                let extended_env = extend_rec(env, var, result, store, cons_witness);

                let c = make_tail_continuation(saved_env, continuation, store, cont_witness);

                Control::Return(body, extended_env?, c)
            }
            _ => unreachable!(),
        },
        ContTag::Unop => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Unop {
                operator,
                continuation,
            } => {
                let val = match operator {
                    Op1::Car => {
                        match cons_witness.car_cdr_mut_named(ConsName::UnopConsLike, store, &result)
                        {
                            Ok((car, _)) => car,
                            Err(_) => return Ok(Control::Error(result, env)),
                        }
                    }
                    Op1::Cdr => {
                        match cons_witness.car_cdr_mut_named(ConsName::UnopConsLike, store, &result)
                        {
                            Ok((_, cdr)) => cdr,
                            Err(_) => return Ok(Control::Error(result, env)),
                        }
                    }
                    Op1::Atom => match result.tag() {
                        ExprTag::Cons => store.nil(),
                        _ => store.t(),
                    },
                    Op1::Emit => {
                        println!("{}", result.fmt_to_string(store));
                        return Ok(Control::MakeThunk(
                            result,
                            env,
                            cont_witness.intern_named_cont(
                                ContName::NewerCont2,
                                store,
                                Continuation::Emit { continuation },
                            ),
                        ));
                    }
                    Op1::Open => match result.tag() {
                        ExprTag::Num | ExprTag::Comm => store.open_mut(result)?.1,
                        _ => return Ok(Control::Error(result, env)),
                    },
                    Op1::Secret => match result.tag() {
                        ExprTag::Num | ExprTag::Comm => store.secret_mut(result)?,
                        _ => return Ok(Control::Error(result, env)),
                    },
                    Op1::Commit => store.hide(F::zero(), result),
                    Op1::Num => match result.tag() {
                        ExprTag::Num | ExprTag::Comm | ExprTag::Char | ExprTag::U64 => {
                            let scalar_ptr = store
                                .get_expr_hash(&result)
                                .ok_or_else(|| store::Error("expr hash missing".into()))?;
                            store.intern_num(crate::Num::Scalar::<F>(*scalar_ptr.value()))
                        }
                        _ => return Ok(Control::Error(result, env)),
                    },
                    Op1::U64 => match result.tag() {
                        ExprTag::Num => {
                            let scalar_ptr = store
                                .get_expr_hash(&result)
                                .ok_or_else(|| store::Error("expr hash missing".into()))?;

                            store.get_u64(scalar_ptr.value().to_u64_unchecked())
                        }
                        ExprTag::U64 => result,
                        _ => return Ok(Control::Error(result, env)),
                    },
                    Op1::Comm => match result.tag() {
                        ExprTag::Num | ExprTag::Comm => {
                            let scalar_ptr = store
                                .get_expr_hash(&result)
                                .ok_or_else(|| store::Error("expr hash missing".into()))?;
                            store.intern_maybe_opaque_comm(*scalar_ptr.value())
                        }
                        _ => return Ok(Control::Error(result, env)),
                    },
                    Op1::Char => match result.tag() {
                        ExprTag::Num | ExprTag::Char => {
                            let scalar_ptr = store
                                .get_expr_hash(&result)
                                .ok_or_else(|| store::Error("expr hash missing".into()))?;
                            store.get_char_from_u32(scalar_ptr.value().to_u32_unchecked())
                        }
                        _ => return Ok(Control::Error(result, env)),
                    },
                    Op1::Eval => {
                        return Ok(Control::Return(result, empty_sym_env(store), continuation));
                    }
                };
                Control::MakeThunk(val, env, continuation)
            }
            _ => unreachable!(),
        },
        ContTag::Binop => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => {
                let (arg2, rest) =
                    cons_witness.car_cdr_named(ConsName::UnevaledArgs, store, &unevaled_args)?;
                if operator == Op2::Begin {
                    if rest.is_nil() {
                        Control::Return(arg2, saved_env, continuation)
                    } else {
                        let begin = c.begin.ptr();
                        let begin_again =
                            cons_witness.cons_named(ConsName::Begin, store, begin, unevaled_args);
                        Control::Return(begin_again, saved_env, continuation)
                    }
                } else if !rest.is_nil() {
                    return Ok(Control::Error(result, env));
                } else {
                    Control::Return(
                        arg2,
                        saved_env,
                        cont_witness.intern_named_cont(
                            ContName::NewerCont2,
                            store,
                            Continuation::Binop2 {
                                operator,
                                evaled_arg: result,
                                continuation,
                            },
                        ),
                    )
                }
            }
            _ => unreachable!(),
        },
        ContTag::Binop2 => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => {
                let arg2 = result;

                let num_num = |store: &mut Store<F>,
                               operator,
                               a: Num<F>,
                               b: Num<F>|
                 -> Result<Ptr<F>, Control<F>> {
                    match operator {
                        Op2::Sum => {
                            let mut tmp = a;
                            tmp += b;
                            Ok(store.intern_num(tmp))
                        }
                        Op2::Diff => {
                            let mut tmp = a;
                            tmp -= b;
                            Ok(store.intern_num(tmp))
                        }
                        Op2::Product => {
                            let mut tmp = a;
                            tmp *= b;
                            Ok(store.intern_num(tmp))
                        }
                        Op2::Quotient => {
                            let mut tmp = a;
                            let b_is_zero: bool = b.is_zero();
                            if b_is_zero {
                                Err(Control::Error(result, env))
                            } else {
                                tmp /= b;
                                Ok(store.intern_num(tmp))
                            }
                        }
                        Op2::Modulo => {
                            // Modulo requires both args be UInt.
                            Err(Control::Error(result, env))
                        }
                        Op2::Equal | Op2::NumEqual => Ok(store.as_lurk_boolean(a == b)),
                        Op2::Less => Ok(store.as_lurk_boolean(a < b)),
                        Op2::Greater => Ok(store.as_lurk_boolean(a > b)),
                        Op2::LessEqual => Ok(store.as_lurk_boolean(a <= b)),
                        Op2::GreaterEqual => Ok(store.as_lurk_boolean(a >= b)),
                        _ => unreachable!(),
                    }
                };

                let result = match (
                    store
                        .fetch(&evaled_arg)
                        .ok_or_else(|| store::Error("Fetch failed".into()))?,
                    store
                        .fetch(&arg2)
                        .ok_or_else(|| store::Error("Fetch failed".into()))?,
                ) {
                    (Expression::Num(a), Expression::Num(b)) if operator.is_numeric() => {
                        match num_num(store, operator, a, b) {
                            Ok(x) => x,
                            Err(control) => return Ok(control),
                        }
                    }
                    (Expression::Num(a), _) if operator == Op2::Hide => {
                        store.hide(a.into_scalar(), arg2)
                    }
                    (Expression::UInt(a), Expression::UInt(b)) if operator.is_numeric() => {
                        match operator {
                            Op2::Sum => store.get_u64((a + b).into()),
                            Op2::Diff => store.get_u64((a - b).into()),
                            Op2::Product => store.get_u64((a * b).into()),
                            Op2::Quotient => {
                                if b.is_zero() {
                                    return Ok(Control::Return(
                                        result,
                                        env,
                                        store.intern_cont_error(),
                                    ));
                                } else {
                                    store.get_u64((a / b).into())
                                }
                            }
                            Op2::Modulo => {
                                if b.is_zero() {
                                    return Ok(Control::Return(
                                        result,
                                        env,
                                        store.intern_cont_error(),
                                    ));
                                } else {
                                    store.get_u64((a % b).into())
                                }
                            }
                            Op2::Equal | Op2::NumEqual => store.as_lurk_boolean(a == b),
                            Op2::Less => store.as_lurk_boolean(a < b),
                            Op2::Greater => store.as_lurk_boolean(a > b),
                            Op2::LessEqual => store.as_lurk_boolean(a <= b),
                            Op2::GreaterEqual => store.as_lurk_boolean(a >= b),
                            _ => unreachable!(),
                        }
                    }
                    (Expression::Num(a), Expression::UInt(b)) if operator.is_numeric() => {
                        match num_num(store, operator, a, b.into()) {
                            Ok(x) => x,
                            Err(control) => return Ok(control),
                        }
                    }
                    (Expression::UInt(a), Expression::Num(b)) if operator.is_numeric() => {
                        match num_num(store, operator, a.into(), b) {
                            Ok(x) => x,
                            Err(control) => return Ok(control),
                        }
                    }
                    (Expression::Char(_), Expression::Str(_))
                        if matches!(operator, Op2::StrCons) =>
                    {
                        cons_witness.strcons_named(ConsName::TheCons, store, evaled_arg, arg2)
                    }
                    _ => match operator {
                        Op2::Equal => store.as_lurk_boolean(store.ptr_eq(&evaled_arg, &arg2)?),
                        Op2::Cons => {
                            cons_witness.cons_named(ConsName::TheCons, store, evaled_arg, arg2)
                        }
                        Op2::Eval => {
                            return Ok(Control::Return(evaled_arg, arg2, continuation));
                        }
                        _ => {
                            return Ok(Control::Return(result, env, store.intern_cont_error()));
                        }
                    },
                };
                Control::MakeThunk(result, env, continuation)
            }
            _ => unreachable!(),
        },
        ContTag::If => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::If {
                unevaled_args,
                continuation,
            } => {
                let condition = result;
                let (arg1, more) =
                    cons_witness.car_cdr_named(ConsName::UnevaledArgs, store, &unevaled_args)?;

                // NOTE: as formulated here, IF operates on any condition. Every
                // value but NIL is considered true.
                //
                // We can implement this in constraints:
                // X * (1-X) = 0
                // C * X = 0
                // (X + C) * Q = 1
                //
                // where X is a constrained boolean which is true (1) iff C == 0. Q
                // is a value non-deterministically supplied by the prover to
                // demonstrate that both X and C are not 0. If both were 0, the
                // constraint C * X = 0 would hold. But in that case, X should be 1
                // since C = 0.
                //
                // Now X can be used as the known-boolean conditional in a
                // conditional selection: (B - A) * X = B - C
                //
                // where C is the result, A is the 'true' result, and B is the
                // false/else result. i.e. if X then A else B.
                //
                // All of the above is just 'how to implement an exact equality
                // check' in the case that the value checked against is zero. We
                // will need this throughout, when branching on symbols (effectively
                // a CASE expression). Since symbols are field elements with
                // equality, this is relatively efficient. When doing this, the
                // value being checked against is not zero, so that value should
                // first be subtracted from the value being checked.

                let (arg2, end) =
                    cons_witness.car_cdr_named(ConsName::UnevaledArgsCdr, store, &more)?;
                if !end.is_nil() {
                    Control::Return(arg1, env, store.intern_cont_error())
                } else if condition.is_nil() {
                    Control::Return(arg2, env, continuation)
                } else {
                    Control::Return(arg1, env, continuation)
                }
            }
            _ => unreachable!(),
        },
        ContTag::Lookup => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Lookup {
                saved_env,
                continuation,
            } => Control::MakeThunk(result, saved_env, continuation),
            _ => unreachable!(),
        },
        ContTag::Tail => match cont_witness
            .fetch_named_cont(ContName::ApplyContinuation, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Tail {
                saved_env,
                continuation,
            } => Control::MakeThunk(result, saved_env, continuation),
            _ => {
                unreachable!();
            }
        },
    };

    if control.is_apply_continuation() {
        unreachable!();
    }

    Ok(control)
}

// Returns (Expression::Thunk, Expression::Env, Continuation)
fn make_thunk<F: LurkField>(
    control: Control<F>,
    store: &mut Store<F>,
    witness: &mut Witness<F>,
) -> Result<Control<F>, ReductionError> {
    if !control.is_make_thunk() {
        return Ok(control);
    }

    let (result, env, cont) = control.into_results(store);

    if let ExprTag::Thunk = result.tag() {
        unreachable!("make_thunk should never be called with a thunk");
    };

    let cont_witness = &mut witness.conts;

    match cont.tag() {
        ContTag::Tail => match cont_witness
            .fetch_named_cont(ContName::MakeThunk, store, &cont)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Continuation::Tail {
                saved_env,
                continuation,
            } => {
                let thunk = store.intern_thunk(Thunk {
                    value: result,
                    continuation,
                });
                Ok(Control::Return(thunk, saved_env, store.intern_cont_dummy()))
            }
            _ => unreachable!(),
        },
        // If continuation is outermost, we don't actually make a thunk. Instead, we signal
        // that this is the terminal result by returning a Terminal continuation.
        ContTag::Outermost => Ok(Control::Return(result, env, store.intern_cont_terminal())),
        _ => {
            let thunk = store.intern_thunk(Thunk {
                value: result,
                continuation: cont,
            });
            Ok(Control::Return(thunk, env, store.intern_cont_dummy()))
        }
    }
}

fn make_tail_continuation<F: LurkField>(
    env: Ptr<F>,
    continuation: ContPtr<F>,
    store: &mut Store<F>,
    cont_witness: &mut ContWitness<F>,
) -> ContPtr<F> {
    // Result must be either a Tail or Outermost continuation.
    match continuation.tag() {
        // If continuation is already tail, just return it.
        //ContTag::Tail => continuation,
        ContTag::Tail => continuation,
        // Otherwise, package it along with supplied env as a new Tail continuation.
        _ => cont_witness.intern_named_cont(
            ContName::NewerCont2,
            store,
            Continuation::Tail {
                saved_env: env,
                continuation,
            },
        ),
    }
    // Since this is the only place Tail continuation are created, this ensures Tail continuations never
    // point to one another: they can only be nested one deep.
}

// Only used in tests. Real evalution should use extend_name.
#[allow(dead_code)]
pub(crate) fn extend<F: LurkField>(
    env: Ptr<F>,
    var: Ptr<F>,
    val: Ptr<F>,
    store: &mut Store<F>,
) -> Ptr<F> {
    let cons = store.cons(var, val);
    store.cons(cons, env)
}

fn extend_rec<F: LurkField>(
    env: Ptr<F>,
    var: Ptr<F>,
    val: Ptr<F>,
    store: &mut Store<F>,
    cons_witness: &mut ConsWitness<F>,
) -> Result<Ptr<F>, ReductionError> {
    let (binding_or_env, rest) = cons_witness.car_cdr_named(ConsName::Env, store, &env)?;
    let (var_or_binding, _val_or_more_bindings) =
        cons_witness.car_cdr_named(ConsName::EnvCar, store, &binding_or_env)?;
    match var_or_binding.tag() {
        // It's a var, so we are extending a simple env with a recursive env.
        ExprTag::Sym | ExprTag::Nil => {
            let cons = cons_witness.cons_named(ConsName::NewRecCadr, store, var, val);
            let nil = store.nil();
            let list = cons_witness.cons_named(ConsName::NewRec, store, cons, nil);
            let res = cons_witness.cons_named(ConsName::ExtendedRec, store, list, env);

            Ok(res)
        }
        // It's a binding, so we are extending a recursive env.
        ExprTag::Cons => {
            let cons = cons_witness.cons_named(ConsName::NewRecCadr, store, var, val);
            let cons2 = cons_witness.cons_named(ConsName::NewRec, store, cons, binding_or_env);
            let res = cons_witness.cons_named(ConsName::ExtendedRec, store, cons2, rest);

            Ok(res)
        }
        _ => Err(store::Error("Bad input form.".into()).into()),
    }
}

fn extend_closure<F: LurkField>(
    fun: &Ptr<F>,
    rec_env: &Ptr<F>,
    store: &mut Store<F>,
    cons_witness: &mut ConsWitness<F>,
) -> Result<Ptr<F>, ReductionError> {
    match fun.tag() {
        ExprTag::Fun => match store
            .fetch(fun)
            .ok_or_else(|| store::Error("Fetch failed".into()))?
        {
            Expression::Fun(arg, body, closed_env) => {
                let extended = cons_witness.cons_named(
                    ConsName::ExtendedClosureEnv,
                    store,
                    *rec_env,
                    closed_env,
                );
                Ok(store.intern_fun(arg, body, extended))
            }
            _ => unreachable!(),
        },
        _ => unreachable!(
            "fun.tag() stopped being ExprTag::Fun after already having been checked in caller."
        ),
    }
}

impl<F: LurkField> Store<F> {
    fn as_lurk_boolean(&mut self, x: bool) -> Ptr<F> {
        if x {
            self.t()
        } else {
            self.nil()
        }
    }
}

#[allow(dead_code)]
// This clarifies the lookup logic and is used in tests.
pub(crate) fn lookup<F: LurkField>(
    env: &Ptr<F>,
    var: &Ptr<F>,
    store: &Store<F>,
) -> Result<Ptr<F>, store::Error> {
    assert!(matches!(var.tag(), ExprTag::Sym));
    match env.tag() {
        ExprTag::Nil => Ok(store.get_nil()),
        ExprTag::Cons => {
            let (binding, smaller_env) = store.car_cdr(env)?;
            let (v, val) = store.car_cdr(&binding)?;
            if v == *var {
                Ok(val)
            } else {
                lookup(&smaller_env, var, store)
            }
        }
        _ => Err(store::Error("Env must be a list.".into())),
    }
}
