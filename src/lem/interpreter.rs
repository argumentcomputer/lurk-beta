use anyhow::{anyhow, bail, Result};

use super::{
    path::Path,
    pointers::{Ptr, RawPtr},
    slot::{SlotData, Val},
    store::Store,
    var_map::VarMap,
    Block, Ctrl, Func, Op, Tag, Var,
};

use crate::{
    coprocessor::Coprocessor,
    eval::lang::Lang,
    field::LurkField,
    num::Num as BaseNum,
    state::initial_lurk_state,
    tag::ExprTag::{Comm, Num, Sym},
};

impl VarMap<Val> {
    pub fn get_many_ptr(&self, args: &[Var]) -> Result<Vec<Ptr>> {
        args.iter().map(|arg| self.get_ptr(arg)).collect()
    }

    fn get_ptr(&self, var: &Var) -> Result<Ptr> {
        if let Val::Pointer(ptr) = self.get(var)? {
            return Ok(*ptr);
        }
        bail!("Expected {var} to be a pointer")
    }

    fn insert_ptr(&mut self, var: Var, ptr: Ptr) -> Option<Val> {
        self.insert(var, Val::Pointer(ptr))
    }

    fn get_bool(&self, var: &Var) -> Result<bool> {
        if let Val::Boolean(b) = self.get(var)? {
            return Ok(*b);
        }
        bail!("Expected {var} to be a boolean")
    }

    fn insert_bool(&mut self, var: Var, b: bool) -> Option<Val> {
        self.insert(var, Val::Boolean(b))
    }
}

#[derive(Clone, Debug, Default)]
/// `Hints` hold the non-deterministic hints for hashes and `Func` calls.
/// The hash preimages must have the same shape as the allocated slots for the
/// `Func`, and the `None` values are used to fill the unused slots, which are
/// later filled by dummy values.
pub struct Hints {
    pub hash4: Vec<Option<SlotData>>,
    pub hash6: Vec<Option<SlotData>>,
    pub hash8: Vec<Option<SlotData>>,
    pub commitment: Vec<Option<SlotData>>,
    pub bit_decomp: Vec<Option<SlotData>>,
    pub bindings: VarMap<Val>,
}

impl Hints {
    pub fn new_from_func(func: &Func) -> Hints {
        let slot = func.slots_count;
        let hash4 = Vec::with_capacity(slot.hash4);
        let hash6 = Vec::with_capacity(slot.hash6);
        let hash8 = Vec::with_capacity(slot.hash8);
        let commitment = Vec::with_capacity(slot.commitment);
        let bit_decomp = Vec::with_capacity(slot.bit_decomp);
        let bindings = VarMap::new();
        Hints {
            hash4,
            hash6,
            hash8,
            commitment,
            bit_decomp,
            bindings,
        }
    }

    pub fn blank(func: &Func) -> Hints {
        let slot = func.slots_count;
        let hash4 = vec![None; slot.hash4];
        let hash6 = vec![None; slot.hash6];
        let hash8 = vec![None; slot.hash8];
        let commitment = vec![None; slot.commitment];
        let bit_decomp = vec![None; slot.bit_decomp];
        let bindings = VarMap::new();
        Hints {
            hash4,
            hash6,
            hash8,
            commitment,
            bit_decomp,
            bindings,
        }
    }
}

/// A `Frame` carries the data that results from interpreting a LEM. That is,
/// it contains the input, the output and all the assignments resulting from
/// running one iteration as a HashMap of variables to pointers.
///
/// This information is used to generate the witness.
#[derive(Clone, Debug, Default)]
pub struct Frame {
    pub input: Vec<Ptr>,
    pub output: Vec<Ptr>,
    pub emitted: Vec<Ptr>,
    pub hints: Hints,
    pub blank: bool,
    pub pc: usize,
}

impl Frame {
    pub fn blank<F: LurkField>(func: &Func, pc: usize, store: &Store<F>) -> Frame {
        let input = vec![store.dummy(); func.input_params.len()];
        let output = vec![store.dummy(); func.output_size];
        let hints = Hints::blank(func);
        Frame {
            input,
            output,
            emitted: Vec::default(),
            hints,
            blank: true,
            pc,
        }
    }
}

impl Block {
    /// Interprets a LEM while i) modifying a `Store`, ii) binding `Var`s to
    /// `Ptr`s and iii) collecting the preimages from visited slots (more on this
    /// in `circuit.rs`)
    fn run<F: LurkField, C: Coprocessor<F>>(
        &self,
        input: &[Ptr],
        store: &Store<F>,
        mut bindings: VarMap<Val>,
        mut hints: Hints,
        mut path: Path,
        emitted: &mut Vec<Ptr>,
        lang: &Lang<F, C>,
        pc: usize,
    ) -> Result<(Frame, Path)> {
        for op in &self.ops {
            match op {
                Op::Cproc(out, sym, inp) => {
                    let inp_ptrs = bindings.get_many_ptr(inp)?;
                    let cproc = lang
                        .lookup_by_sym(sym)
                        .ok_or_else(|| anyhow!("Coprocessor for {sym} not found"))?;
                    let out_ptrs = cproc.evaluate_internal(store, &inp_ptrs);
                    if out.len() != out_ptrs.len() {
                        bail!("Incompatible output length for coprocessor {sym}")
                    }
                    for (var, ptr) in out.iter().zip(out_ptrs.into_iter()) {
                        bindings.insert(var.clone(), Val::Pointer(ptr));
                        hints.bindings.insert(var.clone(), Val::Pointer(ptr));
                    }
                }
                Op::Call(out, func, inp) => {
                    // Get the argument values
                    let inp_ptrs = bindings.get_many_ptr(inp)?;
                    let (frame, func_path) =
                        func.call(&inp_ptrs, store, hints, emitted, lang, pc)?;
                    // Extend the path
                    path.extend_from_path(&func_path);
                    // Bind the output variables to the output values
                    hints = frame.hints;
                    for (var, ptr) in out.iter().zip(frame.output.into_iter()) {
                        bindings.insert_ptr(var.clone(), ptr);
                        hints.bindings.insert_ptr(var.clone(), ptr);
                    }
                }
                Op::Copy(tgt, src) => {
                    bindings.insert(tgt.clone(), bindings.get_cloned(src)?);
                }
                Op::Zero(tgt, tag) => {
                    bindings.insert_ptr(tgt.clone(), store.zero(*tag));
                }
                Op::Hash3Zeros(tgt, tag) => {
                    bindings.insert_ptr(tgt.clone(), Ptr::atom(*tag, store.hash3zeros_idx));
                }
                Op::Hash4Zeros(tgt, tag) => {
                    bindings.insert_ptr(tgt.clone(), Ptr::atom(*tag, store.hash4zeros_idx));
                }
                Op::Hash6Zeros(tgt, tag) => {
                    bindings.insert_ptr(tgt.clone(), Ptr::atom(*tag, store.hash6zeros_idx));
                }
                Op::Hash8Zeros(tgt, tag) => {
                    bindings.insert_ptr(tgt.clone(), Ptr::atom(*tag, store.hash8zeros_idx));
                }
                Op::Lit(tgt, lit) => {
                    bindings.insert_ptr(tgt.clone(), lit.to_ptr(store));
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
                    let c = store.hash_ptr(&a).value() == store.hash_ptr(&b).value();
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
                    let a = *bindings.get_ptr(a)?.pay();
                    let b = *bindings.get_ptr(b)?.pay();
                    let c = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                        let (f, g) = (store.expect_f(f), store.expect_f(g));
                        store.intern_atom(Tag::Expr(Num), *f + *g)
                    } else {
                        bail!("`Add` only works on atoms")
                    };
                    bindings.insert_ptr(tgt.clone(), c);
                }
                Op::Sub(tgt, a, b) => {
                    let a = *bindings.get_ptr(a)?.pay();
                    let b = *bindings.get_ptr(b)?.pay();
                    let c = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                        let (f, g) = (store.expect_f(f), store.expect_f(g));
                        store.intern_atom(Tag::Expr(Num), *f - *g)
                    } else {
                        bail!("`Sub` only works on atoms")
                    };
                    bindings.insert_ptr(tgt.clone(), c);
                }
                Op::Mul(tgt, a, b) => {
                    let a = *bindings.get_ptr(a)?.pay();
                    let b = *bindings.get_ptr(b)?.pay();
                    let c = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                        let (f, g) = (store.expect_f(f), store.expect_f(g));
                        store.intern_atom(Tag::Expr(Num), *f * *g)
                    } else {
                        bail!("`Mul` only works on atoms")
                    };
                    bindings.insert_ptr(tgt.clone(), c);
                }
                Op::Div(tgt, a, b) => {
                    let a = *bindings.get_ptr(a)?.pay();
                    let b = *bindings.get_ptr(b)?.pay();
                    let c = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                        let (f, g) = (store.expect_f(f), store.expect_f(g));
                        if g == &F::ZERO {
                            bail!("Can't divide by zero")
                        }
                        store.intern_atom(Tag::Expr(Num), *f * g.invert().expect("not zero"))
                    } else {
                        bail!("`Div` only works on numbers")
                    };
                    bindings.insert_ptr(tgt.clone(), c);
                }
                Op::Lt(tgt, a, b) => {
                    let a = *bindings.get_ptr(a)?.pay();
                    let b = *bindings.get_ptr(b)?.pay();
                    let c = if let (RawPtr::Atom(f_idx), RawPtr::Atom(g_idx)) = (a, b) {
                        let f = *store.expect_f(f_idx);
                        let g = *store.expect_f(g_idx);
                        let diff = f - g;
                        hints.bit_decomp.push(Some(SlotData {
                            vals: vec![Val::Num(store.intern_f(f + f).0)],
                        }));
                        hints.bit_decomp.push(Some(SlotData {
                            vals: vec![Val::Num(store.intern_f(g + g).0)],
                        }));
                        hints.bit_decomp.push(Some(SlotData {
                            vals: vec![Val::Num(store.intern_f(diff + diff).0)],
                        }));
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
                    let a = *bindings.get_ptr(a)?.pay();
                    let c = if let RawPtr::Atom(f_idx) = a {
                        let f = *store.expect_f(f_idx);
                        hints.bit_decomp.push(Some(SlotData {
                            vals: vec![Val::Num(f_idx)],
                        }));
                        let b = if *n < 64 { (1 << *n) - 1 } else { u64::MAX };
                        store.intern_atom(Tag::Expr(Num), F::from_u64(f.to_u64_unchecked() & b))
                    } else {
                        bail!("`Trunc` only works on atoms")
                    };
                    bindings.insert_ptr(tgt.clone(), c);
                }
                Op::DivRem64(tgt, a, b) => {
                    let a = *bindings.get_ptr(a)?.pay();
                    let b = *bindings.get_ptr(b)?.pay();
                    let (c1, c2) = if let (RawPtr::Atom(f), RawPtr::Atom(g)) = (a, b) {
                        let f = *store.expect_f(f);
                        let g = *store.expect_f(g);
                        if g == F::ZERO {
                            bail!("Can't divide by zero")
                        }
                        let f = f.to_u64_unchecked();
                        let g = g.to_u64_unchecked();
                        let c1 = store.intern_atom(Tag::Expr(Num), F::from_u64(f / g));
                        let c2 = store.intern_atom(Tag::Expr(Num), F::from_u64(f % g));
                        (c1, c2)
                    } else {
                        bail!("`DivRem64` only works on atoms")
                    };
                    bindings.insert_ptr(tgt[0].clone(), c1);
                    bindings.insert_ptr(tgt[1].clone(), c2);
                }
                Op::Emit(a) => {
                    let a = bindings.get_ptr(a)?;
                    println!("{}", a.fmt_to_string(store, initial_lurk_state()));
                    emitted.push(a);
                }
                Op::Cons2(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_ptr(preimg)?;
                    let tgt_ptr = store.intern_2_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1]);
                    bindings.insert_ptr(img.clone(), tgt_ptr);
                    let vals = preimg_ptrs.into_iter().map(Val::Pointer).collect();
                    hints.hash4.push(Some(SlotData { vals }));
                }
                Op::Cons3(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_ptr(preimg)?;
                    let tgt_ptr =
                        store.intern_3_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1], preimg_ptrs[2]);
                    bindings.insert_ptr(img.clone(), tgt_ptr);
                    let vals = preimg_ptrs.into_iter().map(Val::Pointer).collect();
                    hints.hash6.push(Some(SlotData { vals }));
                }
                Op::Cons4(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_ptr(preimg)?;
                    let tgt_ptr = store.intern_4_ptrs(
                        *tag,
                        preimg_ptrs[0],
                        preimg_ptrs[1],
                        preimg_ptrs[2],
                        preimg_ptrs[3],
                    );
                    bindings.insert_ptr(img.clone(), tgt_ptr);
                    let vals = preimg_ptrs.into_iter().map(Val::Pointer).collect();
                    hints.hash8.push(Some(SlotData { vals }));
                }
                Op::Decons2(preimg, img) => {
                    let img_ptr = bindings.get_ptr(img)?;
                    let Some(idx) = img_ptr.get_index2() else {
                        bail!("{img} isn't a Tree2 pointer");
                    };
                    let Some(preimg_ptrs) = store.fetch_2_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert_ptr(var.clone(), *ptr);
                    }
                    let vals = preimg_ptrs.into_iter().map(Val::Pointer).collect();
                    hints.hash4.push(Some(SlotData { vals }));
                }
                Op::Decons3(preimg, img) => {
                    let img_ptr = bindings.get_ptr(img)?;
                    let Some(idx) = img_ptr.get_index3() else {
                        bail!("{img} isn't a Tree3 pointer");
                    };
                    let Some(preimg_ptrs) = store.fetch_3_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert_ptr(var.clone(), *ptr);
                    }
                    let vals = preimg_ptrs.into_iter().map(Val::Pointer).collect();
                    hints.hash6.push(Some(SlotData { vals }));
                }
                Op::Decons4(preimg, img) => {
                    let img_ptr = bindings.get_ptr(img)?;
                    let Some(idx) = img_ptr.get_index4() else {
                        bail!("{img} isn't a Tree4 pointer");
                    };
                    let Some(preimg_ptrs) = store.fetch_4_ptrs(idx) else {
                        bail!("Couldn't fetch {img}'s children")
                    };
                    for (var, ptr) in preimg.iter().zip(preimg_ptrs.iter()) {
                        bindings.insert_ptr(var.clone(), *ptr);
                    }
                    let vals = preimg_ptrs.into_iter().map(Val::Pointer).collect();
                    hints.hash8.push(Some(SlotData { vals }));
                }
                Op::Hide(tgt, sec, src) => {
                    let src_ptr = bindings.get_ptr(src)?;
                    let sec_ptr = bindings.get_ptr(sec)?;
                    let (Tag::Expr(Num), RawPtr::Atom(secret_idx)) = sec_ptr.parts() else {
                        bail!("{sec} is not a numeric pointer")
                    };
                    let secret = *store.expect_f(*secret_idx);
                    let tgt_ptr = store.hide(secret, src_ptr);
                    let vals = vec![Val::Num(*secret_idx), Val::Pointer(src_ptr)];
                    hints.commitment.push(Some(SlotData { vals }));
                    bindings.insert_ptr(tgt.clone(), tgt_ptr);
                }
                Op::Open(tgt_secret, tgt_ptr, comm) => {
                    let comm_ptr = bindings.get_ptr(comm)?;
                    let (Tag::Expr(Comm), RawPtr::Atom(hash)) = comm_ptr.parts() else {
                        bail!("{comm} is not a comm pointer")
                    };
                    let hash = *store.expect_f(*hash);
                    let Some((secret, ptr)) = store.open(hash).cloned() else {
                        bail!("No committed data for hash {}", &hash.hex_digits())
                    };
                    bindings.insert_ptr(tgt_ptr.clone(), ptr);
                    bindings.insert_ptr(
                        tgt_secret.clone(),
                        store.intern_atom(Tag::Expr(Num), secret),
                    );
                    let secret_idx = store.intern_f(secret).0;
                    let vals = vec![Val::Num(secret_idx), Val::Pointer(ptr)];
                    hints.commitment.push(Some(SlotData { vals }));
                }
                Op::Unit(f) => f(),
            }
        }
        match &self.ctrl {
            Ctrl::MatchTag(match_var, cases, def) => {
                let ptr = bindings.get_ptr(match_var)?;
                let tag = ptr.tag();
                if let Some(block) = cases.get(tag) {
                    path.push_tag_inplace(*tag);
                    block.run(input, store, bindings, hints, path, emitted, lang, pc)
                } else {
                    path.push_default_inplace();
                    let Some(def) = def else {
                        bail!("No match for tag {}", tag)
                    };
                    def.run(input, store, bindings, hints, path, emitted, lang, pc)
                }
            }
            Ctrl::MatchSymbol(match_var, cases, def) => {
                let ptr = bindings.get_ptr(match_var)?;
                if ptr.tag() != &Tag::Expr(Sym) {
                    bail!("{match_var} is not a symbol");
                }
                let Some(sym) = store.fetch_symbol(&ptr) else {
                    bail!("Symbol bound to {match_var} wasn't interned");
                };
                if let Some(block) = cases.get(&sym) {
                    path.push_symbol_inplace(sym);
                    block.run(input, store, bindings, hints, path, emitted, lang, pc)
                } else {
                    path.push_default_inplace();
                    let Some(def) = def else {
                        bail!("No match for symbol {sym}")
                    };
                    def.run(input, store, bindings, hints, path, emitted, lang, pc)
                }
            }
            Ctrl::If(b, true_block, false_block) => {
                let b = bindings.get_bool(b)?;
                path.push_bool_inplace(b);
                if b {
                    true_block.run(input, store, bindings, hints, path, emitted, lang, pc)
                } else {
                    false_block.run(input, store, bindings, hints, path, emitted, lang, pc)
                }
            }
            Ctrl::Return(output_vars) => {
                let mut output = Vec::with_capacity(output_vars.len());
                for var in output_vars.iter() {
                    output.push(bindings.get_ptr(var)?)
                }
                let input = input.to_vec();
                Ok((
                    Frame {
                        input,
                        output,
                        emitted: emitted.clone(),
                        hints,
                        blank: false,
                        pc,
                    },
                    path,
                ))
            }
        }
    }
}

impl Func {
    pub fn call<F: LurkField, C: Coprocessor<F>>(
        &self,
        args: &[Ptr],
        store: &Store<F>,
        hints: Hints,
        emitted: &mut Vec<Ptr>,
        lang: &Lang<F, C>,
        pc: usize,
    ) -> Result<(Frame, Path)> {
        let mut bindings = VarMap::new();
        for (i, param) in self.input_params.iter().enumerate() {
            bindings.insert_ptr(param.clone(), args[i]);
        }

        // We must fill any unused slots with `None` values so we save
        // the initial size of hints, which might not be zero
        let hash4_init = hints.hash4.len();
        let hash6_init = hints.hash6.len();
        let hash8_init = hints.hash8.len();
        let commitment_init = hints.commitment.len();
        let bit_decomp_init = hints.bit_decomp.len();

        let mut res = self.body.run(
            args,
            store,
            bindings,
            hints,
            Path::default(),
            emitted,
            lang,
            pc,
        )?;
        let hints = &mut res.0.hints;

        let hash4_used = hints.hash4.len() - hash4_init;
        let hash6_used = hints.hash6.len() - hash6_init;
        let hash8_used = hints.hash8.len() - hash8_init;
        let commitment_used = hints.commitment.len() - commitment_init;
        let bit_decomp_used = hints.bit_decomp.len() - bit_decomp_init;

        for _ in hash4_used..self.slots_count.hash4 {
            hints.hash4.push(None);
        }
        for _ in hash6_used..self.slots_count.hash6 {
            hints.hash6.push(None);
        }
        for _ in hash8_used..self.slots_count.hash8 {
            hints.hash8.push(None);
        }
        for _ in commitment_used..self.slots_count.commitment {
            hints.commitment.push(None);
        }
        for _ in bit_decomp_used..self.slots_count.bit_decomp {
            hints.bit_decomp.push(None);
        }

        Ok(res)
    }

    #[inline]
    pub fn call_simple<F: LurkField, C: Coprocessor<F>>(
        &self,
        args: &[Ptr],
        store: &Store<F>,
        lang: &Lang<F, C>,
        pc: usize,
    ) -> Result<Frame> {
        Ok(self
            .call(
                args,
                store,
                Hints::new_from_func(self),
                &mut vec![],
                lang,
                pc,
            )?
            .0)
    }
}
