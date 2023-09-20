use anyhow::{bail, Result};
use std::collections::VecDeque;

use super::{path::Path, pointers::Ptr, store::Store, var_map::VarMap, Block, Ctrl, Func, Op, Tag};

use crate::{
    field::LurkField,
    num::Num as BaseNum,
    state::initial_lurk_state,
    tag::ExprTag::{Comm, Nil, Num, Sym},
};

#[derive(Clone, Debug)]
pub enum PreimageData<F: LurkField> {
    PtrVec(Vec<Ptr<F>>),
    FPtr(F, Ptr<F>),
    FPair(F, F),
}

#[derive(Clone, Debug, Default)]
/// `Preimages` hold the non-deterministic advices for hashes and `Func` calls.
/// The hash preimages must have the same shape as the allocated slots for the
/// `Func`, and the `None` values are used to fill the unused slots, which are
/// later filled by dummy values.
pub struct Preimages<F: LurkField> {
    pub hash4: Vec<Option<PreimageData<F>>>,
    pub hash6: Vec<Option<PreimageData<F>>>,
    pub hash8: Vec<Option<PreimageData<F>>>,
    pub commitment: Vec<Option<PreimageData<F>>>,
    pub less_than: Vec<Option<PreimageData<F>>>,
    pub call_outputs: VecDeque<Vec<Ptr<F>>>,
}

impl<F: LurkField> Preimages<F> {
    pub fn new_from_func(func: &Func) -> Preimages<F> {
        let slot = func.slot;
        let hash4 = Vec::with_capacity(slot.hash4);
        let hash6 = Vec::with_capacity(slot.hash6);
        let hash8 = Vec::with_capacity(slot.hash8);
        let commitment = Vec::with_capacity(slot.commitment);
        let less_than = Vec::with_capacity(slot.less_than);
        let call_outputs = VecDeque::new();
        Preimages {
            hash4,
            hash6,
            hash8,
            commitment,
            less_than,
            call_outputs,
        }
    }

    pub fn blank(func: &Func) -> Preimages<F> {
        let slot = func.slot;
        let hash4 = vec![None; slot.hash4];
        let hash6 = vec![None; slot.hash6];
        let hash8 = vec![None; slot.hash8];
        let commitment = vec![None; slot.commitment];
        let less_than = vec![None; slot.less_than];
        let call_outputs = VecDeque::new();
        Preimages {
            hash4,
            hash6,
            hash8,
            commitment,
            less_than,
            call_outputs,
        }
    }
}

/// A `Frame` carries the data that results from interpreting a LEM. That is,
/// it contains the input, the output and all the assignments resulting from
/// running one iteration as a HashMap of variables to pointers.
///
/// This information is used to generate the witness.
#[derive(Clone, Debug, Default)]
pub struct Frame<F: LurkField> {
    pub input: Vec<Ptr<F>>,
    pub output: Vec<Ptr<F>>,
    pub preimages: Preimages<F>,
    pub blank: bool,
}

impl<F: LurkField> Frame<F> {
    pub fn blank(func: &Func) -> Frame<F> {
        let input = vec![Ptr::null(Tag::Expr(Nil)); func.input_params.len()];
        let output = vec![Ptr::null(Tag::Expr(Nil)); func.output_size];
        let preimages = Preimages::blank(func);
        Frame {
            input,
            output,
            preimages,
            blank: true,
        }
    }
}

impl Block {
    /// Interprets a LEM while i) modifying a `Store`, ii) binding `Var`s to
    /// `Ptr`s and iii) collecting the preimages from visited slots (more on this
    /// in `circuit.rs`)
    fn run<F: LurkField>(
        &self,
        input: &[Ptr<F>],
        store: &mut Store<F>,
        mut bindings: VarMap<Ptr<F>>,
        mut preimages: Preimages<F>,
        mut path: Path,
        emitted: &mut Vec<Ptr<F>>,
    ) -> Result<(Frame<F>, Path)> {
        for op in &self.ops {
            match op {
                Op::Call(out, func, inp) => {
                    // Get the argument values
                    let inp_ptrs = bindings.get_many_cloned(inp)?;

                    // To save lexical order of `call_outputs` we need to push the output
                    // of the call *before* the inner calls of the `func`. To do this, we
                    // save all the inner call outputs, push the output of the call in front
                    // of it, then extend `call_outputs`
                    let mut inner_call_outputs = VecDeque::new();
                    std::mem::swap(&mut inner_call_outputs, &mut preimages.call_outputs);
                    let (mut frame, func_path) = func.call(&inp_ptrs, store, preimages, emitted)?;
                    std::mem::swap(&mut inner_call_outputs, &mut frame.preimages.call_outputs);

                    // Extend the path and bind the output variables to the output values
                    path.extend_from_path(&func_path);
                    for (var, ptr) in out.iter().zip(frame.output.iter()) {
                        bindings.insert(var.clone(), *ptr);
                    }

                    // Update `preimages` correctly
                    inner_call_outputs.push_front(frame.output);
                    preimages = frame.preimages;
                    preimages.call_outputs.extend(inner_call_outputs);
                }
                Op::Null(tgt, tag) => {
                    bindings.insert(tgt.clone(), Ptr::null(*tag));
                }
                Op::Lit(tgt, lit) => {
                    bindings.insert(tgt.clone(), lit.to_ptr(store));
                }
                Op::Cast(tgt, tag, src) => {
                    let src_ptr = bindings.get(src)?;
                    let tgt_ptr = src_ptr.cast(*tag);
                    bindings.insert(tgt.clone(), tgt_ptr);
                }
                Op::EqTag(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = if a.tag() == b.tag() {
                        Ptr::Atom(Tag::Expr(Num), F::ONE)
                    } else {
                        Ptr::Atom(Tag::Expr(Num), F::ZERO)
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::EqVal(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    // In order to compare Ptrs, we *must* resolve the hashes. Otherwise, we risk failing to recognize equality of
                    // compound data with opaque data in either element's transitive closure.
                    let c = if store.hash_ptr(a)?.value() == store.hash_ptr(b)?.value() {
                        Ptr::Atom(Tag::Expr(Num), F::ONE)
                    } else {
                        Ptr::Atom(Tag::Expr(Num), F::ZERO)
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Add(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = if let (Ptr::Atom(_, f), Ptr::Atom(_, g)) = (a, b) {
                        Ptr::Atom(Tag::Expr(Num), *f + *g)
                    } else {
                        bail!("`Add` only works on atoms")
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Sub(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = if let (Ptr::Atom(_, f), Ptr::Atom(_, g)) = (a, b) {
                        Ptr::Atom(Tag::Expr(Num), *f - *g)
                    } else {
                        bail!("`Sub` only works on atoms")
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Mul(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = if let (Ptr::Atom(_, f), Ptr::Atom(_, g)) = (a, b) {
                        Ptr::Atom(Tag::Expr(Num), *f * *g)
                    } else {
                        bail!("`Mul` only works on atoms")
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Div(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = if let (Ptr::Atom(_, f), Ptr::Atom(_, g)) = (a, b) {
                        if g == &F::ZERO {
                            bail!("Can't divide by zero")
                        }
                        Ptr::Atom(Tag::Expr(Num), *f * g.invert().expect("not zero"))
                    } else {
                        bail!("`Div` only works on numbers")
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Lt(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = if let (Ptr::Atom(_, f), Ptr::Atom(_, g)) = (a, b) {
                        preimages.less_than.push(Some(PreimageData::FPair(*f, *g)));
                        let f = BaseNum::Scalar(*f);
                        let g = BaseNum::Scalar(*g);
                        let b = if f < g { F::ONE } else { F::ZERO };
                        Ptr::Atom(Tag::Expr(Num), b)
                    } else {
                        bail!("`Lt` only works on atoms")
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Trunc(tgt, a, n) => {
                    assert!(*n <= 64);
                    let a = bindings.get(a)?;
                    let c = if let Ptr::Atom(_, f) = a {
                        let b = if *n < 64 { (1 << *n) - 1 } else { u64::MAX };
                        Ptr::Atom(Tag::Expr(Num), F::from_u64(f.to_u64_unchecked() & b))
                    } else {
                        bail!("`Trunc` only works a leaf")
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::DivRem64(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let (c1, c2) = if let (Ptr::Atom(_, f), Ptr::Atom(_, g)) = (a, b) {
                        if g == &F::ZERO {
                            bail!("Can't divide by zero")
                        }
                        let f = f.to_u64_unchecked();
                        let g = g.to_u64_unchecked();
                        let c1 = Ptr::Atom(Tag::Expr(Num), F::from_u64(f / g));
                        let c2 = Ptr::Atom(Tag::Expr(Num), F::from_u64(f % g));
                        (c1, c2)
                    } else {
                        bail!("`DivRem64` only works on atoms")
                    };
                    bindings.insert(tgt[0].clone(), c1);
                    bindings.insert(tgt[1].clone(), c2);
                }
                Op::Emit(a) => {
                    let a = bindings.get(a)?;
                    println!("{}", a.fmt_to_string(store, initial_lurk_state()));
                    emitted.push(*a);
                }
                Op::Cons2(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr = store.intern_2_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1]);
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages
                        .hash4
                        .push(Some(PreimageData::PtrVec(preimg_ptrs)));
                }
                Op::Cons3(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr =
                        store.intern_3_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1], preimg_ptrs[2]);
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages
                        .hash6
                        .push(Some(PreimageData::PtrVec(preimg_ptrs)));
                }
                Op::Cons4(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr = store.intern_4_ptrs(
                        *tag,
                        preimg_ptrs[0],
                        preimg_ptrs[1],
                        preimg_ptrs[2],
                        preimg_ptrs[3],
                    );
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages
                        .hash8
                        .push(Some(PreimageData::PtrVec(preimg_ptrs)));
                }
                Op::Decons2(preimg, img) => {
                    let img_ptr = bindings.get(img)?;
                    let Some(idx) = img_ptr.get_index2() else {
                        bail!("{img} isn't a Tree2 pointer");
                    };
                    let Some((a, b)) = store.fetch_2_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    let preimg_ptrs = [*a, *b];
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert(var.clone(), *ptr);
                    }
                    preimages
                        .hash4
                        .push(Some(PreimageData::PtrVec(preimg_ptrs.to_vec())));
                }
                Op::Decons3(preimg, img) => {
                    let img_ptr = bindings.get(img)?;
                    let Some(idx) = img_ptr.get_index3() else {
                        bail!("{img} isn't a Tree3 pointer");
                    };
                    let Some((a, b, c)) = store.fetch_3_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    let preimg_ptrs = [*a, *b, *c];
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert(var.clone(), *ptr);
                    }
                    preimages
                        .hash6
                        .push(Some(PreimageData::PtrVec(preimg_ptrs.to_vec())));
                }
                Op::Decons4(preimg, img) => {
                    let img_ptr = bindings.get(img)?;
                    let Some(idx) = img_ptr.get_index4() else {
                        bail!("{img} isn't a Tree4 pointer");
                    };
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    let preimg_ptrs = [*a, *b, *c, *d];
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert(var.clone(), *ptr);
                    }
                    preimages
                        .hash8
                        .push(Some(PreimageData::PtrVec(preimg_ptrs.to_vec())));
                }
                Op::Hide(tgt, sec, src) => {
                    let src_ptr = bindings.get(src)?;
                    let Ptr::Atom(Tag::Expr(Num), secret) = bindings.get(sec)? else {
                        bail!("{sec} is not a numeric pointer")
                    };
                    let tgt_ptr = store.hide(*secret, *src_ptr)?;
                    preimages
                        .commitment
                        .push(Some(PreimageData::FPtr(*secret, *src_ptr)));
                    bindings.insert(tgt.clone(), tgt_ptr);
                }
                Op::Open(tgt_secret, tgt_ptr, comm) => {
                    let Ptr::Atom(Tag::Expr(Comm), hash) = bindings.get(comm)? else {
                        bail!("{comm} is not a comm pointer")
                    };
                    let Some((secret, ptr)) = store.open(*hash) else {
                        bail!("No committed data for hash {}", &hash.hex_digits())
                    };
                    bindings.insert(tgt_ptr.clone(), *ptr);
                    bindings.insert(tgt_secret.clone(), Ptr::Atom(Tag::Expr(Num), *secret));
                    preimages
                        .commitment
                        .push(Some(PreimageData::FPtr(*secret, *ptr)))
                }
            }
        }
        match &self.ctrl {
            Ctrl::MatchTag(match_var, cases, def) => {
                let ptr = bindings.get(match_var)?;
                let tag = ptr.tag();
                if let Some(block) = cases.get(tag) {
                    path.push_tag_inplace(*tag);
                    block.run(input, store, bindings, preimages, path, emitted)
                } else {
                    path.push_default_inplace();
                    let Some(def) = def else {
                        bail!("No match for tag {}", tag)
                    };
                    def.run(input, store, bindings, preimages, path, emitted)
                }
            }
            Ctrl::MatchSymbol(match_var, cases, def) => {
                let ptr = bindings.get(match_var)?;
                if ptr.tag() != &Tag::Expr(Sym) {
                    bail!("{match_var} is not a symbol");
                }
                let Some(sym) = store.fetch_symbol(ptr) else {
                    bail!("Symbol bound to {match_var} wasn't interned");
                };
                if let Some(block) = cases.get(&sym) {
                    path.push_symbol_inplace(sym);
                    block.run(input, store, bindings, preimages, path, emitted)
                } else {
                    path.push_default_inplace();
                    let Some(def) = def else {
                        bail!("No match for symbol {sym}")
                    };
                    def.run(input, store, bindings, preimages, path, emitted)
                }
            }
            Ctrl::IfEq(x, y, eq_block, else_block) => {
                let x = bindings.get(x)?;
                let y = bindings.get(y)?;
                let b = x == y;
                path.push_bool_inplace(b);
                if b {
                    eq_block.run(input, store, bindings, preimages, path, emitted)
                } else {
                    else_block.run(input, store, bindings, preimages, path, emitted)
                }
            }
            Ctrl::Return(output_vars) => {
                let mut output = Vec::with_capacity(output_vars.len());
                for var in output_vars.iter() {
                    output.push(*bindings.get(var)?)
                }
                let input = input.to_vec();
                Ok((
                    Frame {
                        input,
                        output,
                        preimages,
                        blank: false,
                    },
                    path,
                ))
            }
        }
    }
}

impl Func {
    pub fn call<F: LurkField>(
        &self,
        args: &[Ptr<F>],
        store: &mut Store<F>,
        preimages: Preimages<F>,
        emitted: &mut Vec<Ptr<F>>,
    ) -> Result<(Frame<F>, Path)> {
        let mut bindings = VarMap::new();
        for (i, param) in self.input_params.iter().enumerate() {
            bindings.insert(param.clone(), args[i]);
        }

        // We must fill any unused slots with `None` values so we save
        // the initial size of preimages, which might not be zero
        let hash4_init = preimages.hash4.len();
        let hash6_init = preimages.hash6.len();
        let hash8_init = preimages.hash8.len();
        let commitment_init = preimages.commitment.len();
        let less_than_init = preimages.less_than.len();

        let mut res = self
            .body
            .run(args, store, bindings, preimages, Path::default(), emitted)?;
        let preimages = &mut res.0.preimages;

        let hash4_used = preimages.hash4.len() - hash4_init;
        let hash6_used = preimages.hash6.len() - hash6_init;
        let hash8_used = preimages.hash8.len() - hash8_init;
        let commitment_used = preimages.commitment.len() - commitment_init;
        let less_than_used = preimages.less_than.len() - less_than_init;

        for _ in hash4_used..self.slot.hash4 {
            preimages.hash4.push(None);
        }
        for _ in hash6_used..self.slot.hash6 {
            preimages.hash6.push(None);
        }
        for _ in hash8_used..self.slot.hash8 {
            preimages.hash8.push(None);
        }
        for _ in commitment_used..self.slot.commitment {
            preimages.commitment.push(None);
        }
        for _ in less_than_used..self.slot.less_than {
            preimages.less_than.push(None);
        }

        Ok(res)
    }

    /// Calls a `Func` on an input until the stop contidion is satisfied, using the output of one
    /// iteration as the input of the next one.
    pub fn call_until<
        F: LurkField,
        StopCond: Fn(&[Ptr<F>]) -> bool,
        // iteration -> input -> emitted -> store -> string
        LogFmt: Fn(usize, &[Ptr<F>], &[Ptr<F>], &Store<F>) -> String,
    >(
        &self,
        args: &[Ptr<F>],
        store: &mut Store<F>,
        stop_cond: StopCond,
        limit: usize,
        // TODO: make this argument optional
        log_fmt: LogFmt,
    ) -> Result<(Vec<Frame<F>>, usize, Vec<Path>)> {
        assert_eq!(self.input_params.len(), self.output_size);
        assert_eq!(self.input_params.len(), args.len());

        // Initial input, path vector and frames
        let mut input = args.to_vec();
        let mut frames = vec![];
        let mut paths = vec![];

        let mut iterations = 0;

        tracing::info!("{}", &log_fmt(iterations, &input, &[], store));

        for _ in 0..limit {
            let preimages = Preimages::new_from_func(self);
            let mut emitted = vec![];
            let (frame, path) = self.call(&input, store, preimages, &mut emitted)?;
            input = frame.output.clone();
            iterations += 1;
            tracing::info!("{}", &log_fmt(iterations, &input, &emitted, store));
            if stop_cond(&frame.output) {
                frames.push(frame);
                paths.push(path);
                break;
            }
            frames.push(frame);
            paths.push(path);
        }
        if iterations < limit {
            // pushing a frame that can be padded
            let preimages = Preimages::new_from_func(self);
            let (frame, path) = self.call(&input, store, preimages, &mut vec![])?;
            frames.push(frame);
            paths.push(path);
        }
        Ok((frames, iterations, paths))
    }

    pub fn call_until_simple<F: LurkField, StopCond: Fn(&[Ptr<F>]) -> bool>(
        &self,
        args: Vec<Ptr<F>>,
        store: &mut Store<F>,
        stop_cond: StopCond,
        limit: usize,
    ) -> Result<(Vec<Ptr<F>>, usize, Vec<Ptr<F>>)> {
        assert_eq!(self.input_params.len(), self.output_size);
        assert_eq!(self.input_params.len(), args.len());

        let mut input = args;
        let mut emitted = vec![];

        let mut iterations = 0;

        for _ in 0..limit {
            let (frame, _) = self.call(&input, store, Preimages::default(), &mut emitted)?;
            input = frame.output.clone();
            iterations += 1;
            if stop_cond(&frame.output) {
                break;
            }
        }
        Ok((input, iterations, emitted))
    }
}
