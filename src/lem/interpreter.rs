use crate::{
    field::{FWrap, LurkField},
    state::initial_lurk_state,
};
use anyhow::{bail, Result};
use std::collections::VecDeque;

use super::{
    path::Path, pointers::Ptr, store::Store, var_map::VarMap, Block, Ctrl, Func, Lit, Op, Tag,
};

use crate::tag::ExprTag::*;

#[derive(Clone, Default)]
/// `Preimages` hold the non-deterministic advices for hashes and `Func` calls.
/// The hash preimages must have the same shape as the allocated slots for the
/// `Func`, and the `None` values are used to fill the unused slots, which are
/// later filled by dummy values.
pub struct Preimages<F: LurkField> {
    pub hash2_ptrs: Vec<Option<Vec<Ptr<F>>>>,
    pub hash3_ptrs: Vec<Option<Vec<Ptr<F>>>>,
    pub hash4_ptrs: Vec<Option<Vec<Ptr<F>>>>,
    pub call_outputs: VecDeque<Vec<Ptr<F>>>,
}

impl<F: LurkField> Preimages<F> {
    pub fn new_from_func(func: &Func) -> Preimages<F> {
        let slot = func.slot;
        let hash2_ptrs = Vec::with_capacity(slot.hash2);
        let hash3_ptrs = Vec::with_capacity(slot.hash3);
        let hash4_ptrs = Vec::with_capacity(slot.hash4);
        let call_outputs = VecDeque::new();
        Preimages {
            hash2_ptrs,
            hash3_ptrs,
            hash4_ptrs,
            call_outputs,
        }
    }
}

/// A `Frame` carries the data that results from interpreting a LEM. That is,
/// it contains the input, the output and all the assignments resulting from
/// running one iteration as a HashMap of variables to pointers.
///
/// This information is used to generate the witness.
#[derive(Clone)]
pub struct Frame<F: LurkField> {
    pub input: Vec<Ptr<F>>,
    pub output: Vec<Ptr<F>>,
    pub preimages: Preimages<F>,
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
                Op::Add(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = match (a, b) {
                        (Ptr::Leaf(Tag::Expr(Num), f), Ptr::Leaf(Tag::Expr(Num), g)) => {
                            Ptr::Leaf(Tag::Expr(Num), *f + *g)
                        }
                        _ => bail!("Addition only works on numbers"),
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Sub(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = match (a, b) {
                        (Ptr::Leaf(Tag::Expr(Num), f), Ptr::Leaf(Tag::Expr(Num), g)) => {
                            Ptr::Leaf(Tag::Expr(Num), *f - *g)
                        }
                        _ => bail!("Addition only works on numbers"),
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Mul(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = match (a, b) {
                        (Ptr::Leaf(Tag::Expr(Num), f), Ptr::Leaf(Tag::Expr(Num), g)) => {
                            Ptr::Leaf(Tag::Expr(Num), *f * *g)
                        }
                        _ => bail!("Addition only works on numbers"),
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Div(tgt, a, b) => {
                    let a = bindings.get(a)?;
                    let b = bindings.get(b)?;
                    let c = match (a, b) {
                        (Ptr::Leaf(Tag::Expr(Num), f), Ptr::Leaf(Tag::Expr(Num), g)) => {
                            Ptr::Leaf(Tag::Expr(Num), *f * g.invert().unwrap())
                        }
                        _ => bail!("Division only works on numbers"),
                    };
                    bindings.insert(tgt.clone(), c);
                }
                Op::Emit(a) => {
                    let a = bindings.get(a)?;
                    println!("{}", a.fmt_to_string(store, initial_lurk_state()));
                    emitted.push(a.clone());
                }
                Op::Hash2(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr = store.intern_2_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1]);
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages.hash2_ptrs.push(Some(preimg_ptrs));
                }
                Op::Hash3(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr =
                        store.intern_3_ptrs(*tag, preimg_ptrs[0], preimg_ptrs[1], preimg_ptrs[2]);
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages.hash3_ptrs.push(Some(preimg_ptrs));
                }
                Op::Hash4(img, tag, preimg) => {
                    let preimg_ptrs = bindings.get_many_cloned(preimg)?;
                    let tgt_ptr = store.intern_4_ptrs(
                        *tag,
                        preimg_ptrs[0],
                        preimg_ptrs[1],
                        preimg_ptrs[2],
                        preimg_ptrs[3],
                    );
                    bindings.insert(img.clone(), tgt_ptr);
                    preimages.hash4_ptrs.push(Some(preimg_ptrs));
                }
                Op::Unhash2(preimg, img) => {
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
                    preimages.hash2_ptrs.push(Some(preimg_ptrs.to_vec()));
                }
                Op::Unhash3(preimg, img) => {
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
                    preimages.hash3_ptrs.push(Some(preimg_ptrs.to_vec()));
                }
                Op::Unhash4(preimg, img) => {
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
                    preimages.hash4_ptrs.push(Some(preimg_ptrs.to_vec()));
                }
                Op::Hide(tgt, sec, src) => {
                    let src_ptr = bindings.get(src)?;
                    let Ptr::Leaf(Tag::Expr(Num), secret) = bindings.get(sec)? else {
                        bail!("{sec} is not a numeric pointer")
                    };
                    let z_ptr = store.hash_ptr(src_ptr)?;
                    let hash =
                        store
                            .poseidon_cache
                            .hash3(&[*secret, z_ptr.tag.to_field(), z_ptr.hash]);
                    let tgt_ptr = Ptr::comm(hash);
                    store.comms.insert(FWrap::<F>(hash), (*secret, *src_ptr));
                    bindings.insert(tgt.clone(), tgt_ptr);
                }
                Op::Open(tgt_secret, tgt_ptr, comm_or_num) => match bindings.get(comm_or_num)? {
                    Ptr::Leaf(Tag::Expr(Num), hash) | Ptr::Leaf(Tag::Expr(Comm), hash) => {
                        let Some((secret, ptr)) = store.comms.get(&FWrap::<F>(*hash)) else {
                            bail!("No committed data for hash {}", &hash.hex_digits())
                        };
                        bindings.insert(tgt_ptr.clone(), *ptr);
                        bindings.insert(tgt_secret.clone(), Ptr::Leaf(Tag::Expr(Num), *secret));
                    }
                    _ => {
                        bail!("{comm_or_num} is not a num/comm pointer")
                    }
                },
            }
        }
        match &self.ctrl {
            Ctrl::MatchTag(match_var, cases, def) => {
                let ptr = bindings.get(match_var)?;
                let tag = ptr.tag();
                match cases.get(tag) {
                    Some(block) => {
                        path.push_tag_inplace(tag);
                        block.run(input, store, bindings, preimages, path, emitted)
                    }
                    None => {
                        path.push_default_inplace();
                        match def {
                            Some(def) => def.run(input, store, bindings, preimages, path, emitted),
                            None => bail!("No match for tag {}", tag),
                        }
                    }
                }
            }
            Ctrl::MatchVal(match_var, cases, def) => {
                let ptr = bindings.get(match_var)?;
                let Some(lit) = Lit::from_ptr(ptr, store) else {
                    // If we can't find it in the store, it most certaily is not equal to any
                    // of the cases, which are all interned
                    path.push_default_inplace();
                    match def {
                        Some(def) => return def.run(input, store, bindings, preimages, path, emitted),
                        None => bail!("No match for literal"),
                    }
                };
                match cases.get(&lit) {
                    Some(block) => {
                        path.push_lit_inplace(&lit);
                        block.run(input, store, bindings, preimages, path, emitted)
                    }
                    None => {
                        path.push_default_inplace();
                        match def {
                            Some(def) => def.run(input, store, bindings, preimages, path, emitted),
                            None => bail!("No match for literal {:?}", lit),
                        }
                    }
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
        let hash2_init = preimages.hash2_ptrs.len();
        let hash3_init = preimages.hash3_ptrs.len();
        let hash4_init = preimages.hash4_ptrs.len();

        let mut res = self
            .body
            .run(args, store, bindings, preimages, Path::default(), emitted)?;
        let preimages = &mut res.0.preimages;

        let hash2_used = preimages.hash2_ptrs.len() - hash2_init;
        let hash3_used = preimages.hash3_ptrs.len() - hash3_init;
        let hash4_used = preimages.hash4_ptrs.len() - hash4_init;
        for _ in hash2_used..self.slot.hash2 {
            preimages.hash2_ptrs.push(None);
        }
        for _ in hash3_used..self.slot.hash3 {
            preimages.hash3_ptrs.push(None);
        }
        for _ in hash4_used..self.slot.hash4 {
            preimages.hash4_ptrs.push(None);
        }

        Ok(res)
    }

    /// Calls a `Func` on an input until the stop contidion is satisfied, using the output of one
    /// iteration as the input of the next one.
    pub fn call_until<F: LurkField, Stop: Fn(&[Ptr<F>]) -> bool>(
        &self,
        args: &[Ptr<F>],
        store: &mut Store<F>,
        stop_cond: Stop,
        limit: usize,
    ) -> Result<(Vec<Frame<F>>, usize, Vec<Path>)> {
        assert_eq!(self.input_params.len(), self.output_size);
        assert_eq!(self.input_params.len(), args.len());

        // Initial path vector and frames
        let mut frames = vec![];
        let mut paths = vec![];

        let mut iterations = 0;

        let mut input = args.to_vec();

        for _ in 0..limit {
            let preimages = Preimages::new_from_func(self);
            let (frame, path) = self.call(&input, store, preimages, &mut vec![])?;
            iterations += 1;
            if stop_cond(&frame.output) {
                frames.push(frame);
                paths.push(path);
                break;
            }
            // Should frames take borrowed vectors instead, as to avoid cloning?
            // Using AVec is a possibility, but to create a dynamic AVec, currently,
            // requires 2 allocations since it must be created from a Vec and
            // Vec<T> -> Arc<[T]> uses `copy_from_slice`.
            input = frame.output.clone();
            frames.push(frame);
            paths.push(path);
        }
        Ok((frames, iterations, paths))
    }

    pub fn call_until_simple<F: LurkField, Stop: Fn(&[Ptr<F>]) -> bool>(
        &self,
        args: Vec<Ptr<F>>,
        store: &mut Store<F>,
        stop_cond: Stop,
        limit: usize,
    ) -> Result<(Vec<Ptr<F>>, usize, Vec<Ptr<F>>)> {
        assert_eq!(self.input_params.len(), self.output_size);
        assert_eq!(self.input_params.len(), args.len());

        let mut iterations = 0;
        let mut input = args;
        let mut emitted = vec![];

        for _ in 0..limit {
            let (frame, _) = self.call(&input, store, Preimages::default(), &mut emitted)?;
            iterations += 1;
            if stop_cond(&frame.output) {
                break;
            }
            input = frame.output.clone();
        }
        Ok((input, iterations, emitted))
    }
}
