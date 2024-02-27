use super::toplevel::ToplevelQuery;

use crate::coroutine::memoset::{LogMemo, Query, Scope};
use crate::field::LurkField;
use crate::lem::pointers::{Ptr, RawPtr};
use crate::lem::slot::Val;
use crate::lem::store::{fetch_ptrs, intern_ptrs};
use crate::lem::tag::Tag;
use crate::lem::var_map::VarMap;
use crate::lem::{Block, Ctrl, Func, Op};
use crate::num::Num as BaseNum;
use crate::tag::ExprTag::{Comm, Num, Sym};

use anyhow::{bail, Context, Result};

pub(crate) fn call<F: LurkField>(
    query: &ToplevelQuery<F>,
    func: &Func,
    args: &[Ptr],
    scope: &mut Scope<ToplevelQuery<F>, LogMemo<F>, F>,
) -> Result<Vec<Ptr>> {
    let mut bindings = VarMap::new();
    for (i, param) in func.input_params.iter().enumerate() {
        bindings.insert_ptr(param.clone(), args[i]);
    }
    run(query, &func.body, scope, bindings)
}

fn run<F: LurkField>(
    query: &ToplevelQuery<F>,
    body: &Block,
    scope: &mut Scope<ToplevelQuery<F>, LogMemo<F>, F>,
    mut bindings: VarMap<Val>,
) -> Result<Vec<Ptr>> {
    for op in &body.ops {
        match op {
            Op::Crout(out, name, inp) => {
                let args = bindings.get_many_ptr(inp)?;
                let sub_query = ToplevelQuery::new(name.clone(), args, &scope.content)?;
                let out_ptr = query.recursive_eval(scope, sub_query);
                bindings.insert_ptr(out.clone(), out_ptr);
            }
            Op::Cproc(..) => unimplemented!(),
            Op::Call(out, func, inp) => {
                let inp_ptrs = bindings.get_many_ptr(inp)?;
                let output = call(query, func, &inp_ptrs, scope)?;
                for (var, ptr) in out.iter().zip(output.into_iter()) {
                    bindings.insert_ptr(var.clone(), ptr);
                }
            }
            Op::Copy(tgt, src) => {
                bindings.insert(tgt.clone(), bindings.get_cloned(src)?);
            }
            Op::Zero(tgt, tag) => {
                bindings.insert_ptr(tgt.clone(), scope.store.zero(*tag));
            }
            Op::Hash3Zeros(tgt, tag) => {
                bindings.insert_ptr(tgt.clone(), Ptr::atom(*tag, scope.store.hash3zeros_idx));
            }
            Op::Hash4Zeros(tgt, tag) => {
                bindings.insert_ptr(tgt.clone(), Ptr::atom(*tag, scope.store.hash4zeros_idx));
            }
            Op::Hash6Zeros(tgt, tag) => {
                bindings.insert_ptr(tgt.clone(), Ptr::atom(*tag, scope.store.hash6zeros_idx));
            }
            Op::Hash8Zeros(tgt, tag) => {
                bindings.insert_ptr(tgt.clone(), Ptr::atom(*tag, scope.store.hash8zeros_idx));
            }
            Op::Lit(tgt, lit) => {
                bindings.insert_ptr(tgt.clone(), lit.to_ptr(&scope.store));
            }
            Op::Cast(tgt, tag, src) => {
                let src_ptr = bindings.get_ptr(src)?;
                let tgt_ptr = src_ptr.cast(*tag);
                bindings.insert_ptr(tgt.clone(), tgt_ptr);
            }
            Op::EqTag(tgt, a, b) => {
                let a = bindings.get_ptr(a)?;
                let b = bindings.get_ptr(b)?;
                let c = a.tag() == b.tag();
                bindings.insert_bool(tgt.clone(), c);
            }
            Op::EqVal(tgt, a, b) => {
                let a = bindings.get_ptr(a)?;
                let b = bindings.get_ptr(b)?;
                // In order to compare Ptrs, we *must* resolve the hashes. Otherwise, we risk failing to recognize equality of
                // compound data with opaque data in either element's transitive closure.
                let c = scope.store.hash_ptr(&a).value() == scope.store.hash_ptr(&b).value();
                bindings.insert_bool(tgt.clone(), c);
            }
            Op::Not(tgt, a) => {
                let a = bindings.get_bool(a)?;
                bindings.insert_bool(tgt.clone(), !a);
            }
            Op::And(tgt, a, b) => {
                let a = bindings.get_bool(a)?;
                let b = bindings.get_bool(b)?;
                bindings.insert_bool(tgt.clone(), a && b);
            }
            Op::Or(tgt, a, b) => {
                let a = bindings.get_bool(a)?;
                let b = bindings.get_bool(b)?;
                bindings.insert_bool(tgt.clone(), a || b);
            }
            Op::Add(tgt, a, b) => {
                let a = *bindings.get_ptr(a)?.raw();
                let b = *bindings.get_ptr(b)?.raw();
                let c = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                    let (f, g) = (scope.store.expect_f(f), scope.store.expect_f(g));
                    scope.store.intern_atom(Tag::Expr(Num), *f + *g)
                } else {
                    bail!("`Add` only works on atoms")
                };
                bindings.insert_ptr(tgt.clone(), c);
            }
            Op::Sub(tgt, a, b) => {
                let a = *bindings.get_ptr(a)?.raw();
                let b = *bindings.get_ptr(b)?.raw();
                let c = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                    let (f, g) = (scope.store.expect_f(f), scope.store.expect_f(g));
                    scope.store.intern_atom(Tag::Expr(Num), *f - *g)
                } else {
                    bail!("`Sub` only works on atoms")
                };
                bindings.insert_ptr(tgt.clone(), c);
            }
            Op::Mul(tgt, a, b) => {
                let a = *bindings.get_ptr(a)?.raw();
                let b = *bindings.get_ptr(b)?.raw();
                let c = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                    let (f, g) = (scope.store.expect_f(f), scope.store.expect_f(g));
                    scope.store.intern_atom(Tag::Expr(Num), *f * *g)
                } else {
                    bail!("`Mul` only works on atoms")
                };
                bindings.insert_ptr(tgt.clone(), c);
            }
            Op::Div(tgt, a, b) => {
                let a = *bindings.get_ptr(a)?.raw();
                let b = *bindings.get_ptr(b)?.raw();
                let c = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                    let (f, g) = (scope.store.expect_f(f), scope.store.expect_f(g));
                    if g == &F::ZERO {
                        bail!("Can't divide by zero")
                    }
                    scope
                        .store
                        .intern_atom(Tag::Expr(Num), *f * g.invert().expect("not zero"))
                } else {
                    bail!("`Div` only works on numbers")
                };
                bindings.insert_ptr(tgt.clone(), c);
            }
            Op::Lt(tgt, a, b) => {
                let a = *bindings.get_ptr(a)?.raw();
                let b = *bindings.get_ptr(b)?.raw();
                let c = if let (RawPtr::Atom(f_idx), RawPtr::Atom(g_idx)) = (a, b) {
                    let f = *scope.store.expect_f(f_idx);
                    let g = *scope.store.expect_f(g_idx);
                    let f = BaseNum::Scalar(f);
                    let g = BaseNum::Scalar(g);
                    f < g
                } else {
                    bail!("`Lt` only works on atoms")
                };
                bindings.insert_bool(tgt.clone(), c);
            }
            Op::Trunc(tgt, a, n) => {
                assert!(*n <= 64);
                let a = *bindings.get_ptr(a)?.raw();
                let c = if let RawPtr::Atom(f_idx) = a {
                    let f = *scope.store.expect_f(f_idx);
                    let b = if *n < 64 { (1 << *n) - 1 } else { u64::MAX };
                    scope
                        .store
                        .intern_atom(Tag::Expr(Num), F::from_u64(f.to_u64_unchecked() & b))
                } else {
                    bail!("`Trunc` only works on atoms")
                };
                bindings.insert_ptr(tgt.clone(), c);
            }
            Op::DivRem64(tgt, a, b) => {
                let a = *bindings.get_ptr(a)?.raw();
                let b = *bindings.get_ptr(b)?.raw();
                let (c1, c2) = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                    let f = *scope.store.expect_f(f);
                    let g = *scope.store.expect_f(g);
                    if g == F::ZERO {
                        bail!("Can't divide by zero")
                    }
                    let f = f.to_u64_unchecked();
                    let g = g.to_u64_unchecked();
                    let c1 = scope.store.intern_atom(Tag::Expr(Num), F::from_u64(f / g));
                    let c2 = scope.store.intern_atom(Tag::Expr(Num), F::from_u64(f % g));
                    (c1, c2)
                } else {
                    bail!("`DivRem64` only works on atoms")
                };
                bindings.insert_ptr(tgt[0].clone(), c1);
                bindings.insert_ptr(tgt[1].clone(), c2);
            }
            Op::Emit(a) => {
                let a = bindings.get_ptr(a)?;
                println!("{}", a.fmt_to_string_simple(&scope.store));
            }
            Op::Cons2(img, tag, preimg) => {
                let preimg_ptrs = bindings.get_many_ptr(preimg)?;
                let tgt_ptr = intern_ptrs!(scope.store, *tag, preimg_ptrs[0], preimg_ptrs[1]);
                bindings.insert_ptr(img.clone(), tgt_ptr);
            }
            Op::Cons3(img, tag, preimg) => {
                let preimg_ptrs = bindings.get_many_ptr(preimg)?;
                let tgt_ptr = intern_ptrs!(
                    scope.store,
                    *tag,
                    preimg_ptrs[0],
                    preimg_ptrs[1],
                    preimg_ptrs[2]
                );
                bindings.insert_ptr(img.clone(), tgt_ptr);
            }
            Op::Cons4(img, tag, preimg) => {
                let preimg_ptrs = bindings.get_many_ptr(preimg)?;
                let tgt_ptr = intern_ptrs!(
                    scope.store,
                    *tag,
                    preimg_ptrs[0],
                    preimg_ptrs[1],
                    preimg_ptrs[2],
                    preimg_ptrs[3]
                );
                bindings.insert_ptr(img.clone(), tgt_ptr);
            }
            Op::Decons2(preimg, img) => {
                let img_ptr = bindings.get_ptr(img)?;
                let Some(idx) = img_ptr.get_index2() else {
                    bail!("{img} isn't a Tree2 pointer");
                };
                let Some(preimg_ptrs) = fetch_ptrs!(scope.store, 2, idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                    bindings.insert_ptr(var.clone(), *ptr);
                }
            }
            Op::Decons3(preimg, img) => {
                let img_ptr = bindings.get_ptr(img)?;
                let Some(idx) = img_ptr.get_index3() else {
                    bail!("{img} isn't a Tree3 pointer");
                };
                let Some(preimg_ptrs) = fetch_ptrs!(scope.store, 3, idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                    bindings.insert_ptr(var.clone(), *ptr);
                }
            }
            Op::Decons4(preimg, img) => {
                let img_ptr = bindings.get_ptr(img)?;
                let Some(idx) = img_ptr.get_index4() else {
                    bail!("{img} isn't a Tree4 pointer");
                };
                let Some(preimg_ptrs) = fetch_ptrs!(scope.store, 4, idx) else {
                    bail!("Couldn't fetch {img}'s children")
                };
                for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                    bindings.insert_ptr(var.clone(), *ptr);
                }
            }
            Op::PushBinding(img, preimg) => {
                let preimg_ptrs = bindings.get_many_ptr(preimg)?;
                let tgt_ptr =
                    scope
                        .store
                        .push_binding(preimg_ptrs[0], preimg_ptrs[1], preimg_ptrs[2]);
                bindings.insert_ptr(img.clone(), tgt_ptr);
            }
            Op::PopBinding(preimg, img) => {
                let img_ptr = bindings.get_ptr(img)?;
                let preimg_ptrs = scope
                    .store
                    .pop_binding(img_ptr)
                    .context("cannot extract {img}'s binding")?;
                for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                    bindings.insert_ptr(var.clone(), *ptr);
                }
            }
            Op::Hide(tgt, sec, src) => {
                let src_ptr = bindings.get_ptr(src)?;
                let sec_ptr = bindings.get_ptr(sec)?;
                let (Tag::Expr(Num), RawPtr::Atom(secret_idx)) = sec_ptr.parts() else {
                    bail!("{sec} is not a numeric pointer")
                };
                let secret = *scope.store.expect_f(*secret_idx);
                let tgt_ptr = scope.store.hide(secret, src_ptr);
                bindings.insert_ptr(tgt.clone(), tgt_ptr);
            }
            Op::Open(tgt_secret, tgt_ptr, comm) => {
                let comm_ptr = bindings.get_ptr(comm)?;
                let (Tag::Expr(Comm), RawPtr::Atom(hash)) = comm_ptr.parts() else {
                    bail!("{comm} is not a comm pointer")
                };
                let hash = *scope.store.expect_f(*hash);
                let Some((secret, ptr)) = scope.store.open(hash) else {
                    bail!("No committed data for hash {}", &hash.hex_digits())
                };
                bindings.insert_ptr(tgt_ptr.clone(), *ptr);
                bindings.insert_ptr(
                    tgt_secret.clone(),
                    scope.store.intern_atom(Tag::Expr(Num), *secret),
                );
            }
            Op::Unit(f) => f(),
        }
    }
    match &body.ctrl {
        Ctrl::MatchTag(match_var, cases, def) => {
            let ptr = bindings.get_ptr(match_var)?;
            let tag = ptr.tag();
            if let Some(block) = cases.get(tag) {
                run(query, block, scope, bindings)
            } else {
                let Some(def) = def else {
                    bail!("No match for tag {}", tag)
                };
                run(query, def, scope, bindings)
            }
        }
        Ctrl::MatchSymbol(match_var, cases, def) => {
            let ptr = bindings.get_ptr(match_var)?;
            if ptr.tag() != &Tag::Expr(Sym) {
                bail!("{match_var} is not a symbol");
            }
            let Some(sym) = scope.store.fetch_symbol(&ptr) else {
                bail!("Symbol bound to {match_var} wasn't interned");
            };
            if let Some(block) = cases.get(&sym) {
                run(query, block, scope, bindings)
            } else {
                let Some(def) = def else {
                    bail!("No match for symbol {sym}")
                };
                run(query, def, scope, bindings)
            }
        }
        Ctrl::If(b, true_block, false_block) => {
            let b = bindings.get_bool(b)?;
            if b {
                run(query, true_block, scope, bindings)
            } else {
                run(query, false_block, scope, bindings)
            }
        }
        Ctrl::Return(output_vars) => {
            let mut output = Vec::with_capacity(output_vars.len());
            for var in output_vars.iter() {
                output.push(bindings.get_ptr(var)?)
            }
            Ok(output)
        }
    }
}
