//! ## Lurk Evaluation Model (LEM)
//!
//! LEM is a simple, first order, referentially transparent language, designed to
//! allow writing Lurk's step function and Lurk coprocessors in a convenient way.
//!
//! The motivation behind LEM is the fact that hand-writing the circuit is a
//! fragile process that hinders experimentation and safety. Thus we would like
//! to bootstrap the circuit automatically, as well as an interpretation
//! algorithm that computes all non-deterministic advices for the circuit,
//! given a higher level description of the step function.
//!
//! LEM also allows the `Store` API to be completely abstracted away from the
//! responsibilities of LEM authors. Indeed, we want the implementation details
//! of the `Store` not to be important at LEM definition time.
//!
//! ### Data semantics
//!
//! The main data type that represents LEM code is the `Func` type. A `Func` is
//! much like a function: it contains input parameters, output size, and a
//! function body. The body of a function is a `Block` which is a sequence of
//! operations `Op` followed by a control `Ctrl` statement.
//!
//! Operations are much like `let` statements in functional languages. For
//! example, a `Op::Hash2(x, t, ys)` is to be understood as `let x = hash2(ys)`.
//! If a second operation binds its result to the same variable as a previous
//! operation, we shadow the previous value. There is no mutation, thus the
//! language is referentially transparent.
//!
//! A control statement is either a `Return(xs)`, which exits a function and
//! returns the values of the specified variables, or a match statement, which
//! will do case analysis on the value of a variable and select the appropriate
//! block to continue to.
//!
//! ### Interpretation
//!
//! The interpreter runs a LEM function given input values. Interpreting a LEM
//! function will compute the values of each variable in the path of execution.
//! In particular, it will compute all the non-deterministic advices that are
//! needed to solve the circuit.
//!
//! ### Synthesizing
//!
//! Synthesizing is the process of building the circuit and solving it for a
//! particular instance (i.e. finding a witness). All valid LEM functions can be
//! synthesized if they were previously interpreted.
//!
//! ### Code transformations and static checks of correctness
//!
//! Here are some simple transformations and static checks of correctness we
//! want to perform on a LEM function before interpreting and synthesizing it
//!
//! 1. All variables must be bound, no variable can be used before being bound
//! 2. All returns within a block must be of the same size and equal to the
//!    function's output size
//! 3. Function calls must have the correct number of arguments and must bind
//!    the correct number of variables
//! 4. No match statements should have conflicting cases
//! 5. LEM should be transformed to SSA to make it simple to synthesize
//! 6. We also check for variables that are not used. If intended they should
//!    be prefixed by "_"

mod circuit;
pub mod eval;
pub mod interpreter;
mod macros;
mod path;
pub mod pointers;
mod slot;
pub mod store;
mod var_map;

use crate::field::LurkField;
use crate::symbol::Symbol;
use crate::tag::{ContTag, ExprTag, Tag as TagTrait};
use anyhow::{bail, Result};
use indexmap::IndexMap;
use std::sync::Arc;

use self::{pointers::Ptr, slot::SlotsCounter, store::Store, var_map::VarMap};

pub type AString = Arc<str>;

/// A `Func` is a LEM function. It consist of input params, output size and a
/// function body, which is a `Block`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Func {
    name: String,
    input_params: Vec<Var>,
    output_size: usize,
    body: Block,
    slot: SlotsCounter,
}

/// LEM variables
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct Var(AString);

/// LEM tags
#[derive(Copy, Debug, PartialEq, Clone, Eq, Hash)]
pub enum Tag {
    Expr(ExprTag),
    Cont(ContTag),
    Ctrl(CtrlTag),
}

#[derive(Copy, Debug, PartialEq, Clone, Eq, Hash)]
pub enum CtrlTag {
    Return,
    MakeThunk,
    ApplyContinuation,
    Error,
}

impl Tag {
    #[inline]
    pub fn to_field<F: LurkField>(self) -> F {
        use Tag::*;
        match self {
            Expr(tag) => tag.to_field(),
            Cont(tag) => tag.to_field(),
            Ctrl(tag) => tag.to_field(),
        }
    }
}

impl CtrlTag {
    #[inline]
    fn to_field<F: LurkField>(self) -> F {
        F::from(self as u64)
    }
}

impl std::fmt::Display for CtrlTag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Return => write!(f, "return#"),
            Self::ApplyContinuation => write!(f, "apply-cont#"),
            Self::MakeThunk => write!(f, "make-thunk#"),
            Self::Error => write!(f, "error#"),
        }
    }
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Tag::*;
        match self {
            Expr(tag) => write!(f, "expr.{}", tag),
            Cont(tag) => write!(f, "cont.{}", tag),
            Ctrl(tag) => write!(f, "ctrl.{}", tag),
        }
    }
}

/// LEM literals
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum Lit {
    // TODO maybe it should be a LurkField instead of u64
    Num(u64),
    String(String),
    Symbol(Symbol),
}

impl Lit {
    pub fn to_ptr_cache<F: LurkField>(&self, store: &Store<F>) -> Ptr<F> {
        match self {
            Self::Symbol(s) => store
                .symbol_ptr_cache
                .get(s)
                .expect("Symbols should have been cached")
                .clone(),
            Self::String(s) => store
                .string_ptr_cache
                .get(s)
                .expect("String should have been cached")
                .clone(),
            Self::Num(num) => Ptr::num((*num).into()),
        }
    }

    pub fn to_ptr<F: LurkField>(&self, store: &mut Store<F>) -> Ptr<F> {
        match self {
            Self::Symbol(s) => store.intern_symbol(s),
            Self::String(s) => store.intern_string(s),
            Self::Num(num) => Ptr::num((*num).into()),
        }
    }

    pub fn from_ptr<F: LurkField>(ptr: &Ptr<F>, store: &Store<F>) -> Option<Self> {
        use ExprTag::*;
        use Tag::*;
        match ptr.tag() {
            Expr(Num) => match ptr {
                Ptr::Leaf(_, f) => {
                    let num = LurkField::to_u64_unchecked(f);
                    Some(Self::Num(num))
                }
                _ => unreachable!(),
            },
            Expr(Str) => store.fetch_string(ptr).cloned().map(Lit::String),
            Expr(Sym) => store.fetch_symbol(ptr).cloned().map(Lit::Symbol),
            _ => None,
        }
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Var {
    #[inline]
    pub fn name(&self) -> &AString {
        &self.0
    }
}

/// A block is a sequence of operations followed by a control. Each block
/// delimits their variables' scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    ops: Vec<Op>,
    ctrl: Ctrl,
}

/// The basic control nodes for LEM logical paths.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ctrl {
    /// `MatchTag(x, cases)` performs a match on the tag of `x`, choosing the
    /// appropriate `Block` among the ones provided in `cases`
    MatchTag(Var, IndexMap<Tag, Block>, Option<Box<Block>>),
    /// `MatchSymbol(x, cases, def)` checks whether `x` matches some symbol among
    /// the ones provided in `cases`. If so, run the corresponding `Block`. Run
    /// `def` otherwise
    MatchVal(Var, IndexMap<Lit, Block>, Option<Box<Block>>),
    /// `IfEq(x, y, eq_block, else_block)` runs `eq_block` if `x == y`, and
    /// otherwise runs `else_block`
    IfEq(Var, Var, Box<Block>, Box<Block>),
    /// `Return(rets)` sets the output to `rets`
    Return(Vec<Var>),
}

/// The atomic operations of LEMs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    /// `Call(ys, f, xs)` binds `ys` to the results of `f` applied to `xs`
    Call(Vec<Var>, Box<Func>, Vec<Var>),
    /// `Null(x, t)` binds `x` to a `Ptr::Leaf(t, F::zero())`
    Null(Var, Tag),
    /// `Lit(x, l)` binds `x` to the pointer representing that `Lit`
    Lit(Var, Lit),
    /// `Cast(y, t, x)` binds `y` to a pointer with tag `t` and the hash of `x`
    Cast(Var, Tag, Var),
    /// `Add(y, a, b)` binds `y` to the sum of `a` and `b`
    Add(Var, Var, Var),
    /// `Sub(y, a, b)` binds `y` to the sum of `a` and `b`
    Sub(Var, Var, Var),
    /// `Mul(y, a, b)` binds `y` to the sum of `a` and `b`
    Mul(Var, Var, Var),
    /// `Div(y, a, b)` binds `y` to the sum of `a` and `b`
    Div(Var, Var, Var),
    /// `Emit(v)` simply prints out the value of `v` when interpreting the code
    Emit(Var),
    /// `Hash2(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 2 children `ys`
    Hash2(Var, Tag, [Var; 2]),
    /// `Hash3(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 3 children `ys`
    Hash3(Var, Tag, [Var; 3]),
    /// `Hash4(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 4 children `ys`
    Hash4(Var, Tag, [Var; 4]),
    /// `Unhash2([a, b], x)` binds `a` and `b` to the 2 children of `x`
    Unhash2([Var; 2], Var),
    /// `Unhash3([a, b, c], x)` binds `a`, `b` and `c` to the 3 children of `x`
    Unhash3([Var; 3], Var),
    /// `Unhash4([a, b, c, d], x)` binds `a`, `b`, `c` and `d` to the 4 children of `x`
    Unhash4([Var; 4], Var),
    /// `Hide(x, s, p)` binds `x` to a (comm) `Ptr` resulting from hiding the
    /// payload `p` with (num) secret `s`
    Hide(Var, Var, Var),
    /// `Open(s, p, h)` binds `s` and `p` to the secret and payload (respectively)
    /// of the commitment that resulted on (num or comm) `h`
    Open(Var, Var, Var),
}

impl Func {
    /// Instantiates a `Func` with the appropriate transformations and checks
    pub fn new(
        name: String,
        input_params: Vec<Var>,
        output_size: usize,
        body: Block,
    ) -> Result<Func> {
        let slot = body.count_slots();
        let func = Func {
            slot,
            name,
            input_params,
            output_size,
            body,
        }
        .deconflict(&mut VarMap::new(), &mut 0)?;
        func.check()?;
        Ok(func)
    }

    /// Performs the static checks described in LEM's docstring.
    pub fn check(&self) -> Result<()> {
        // Check if variable has already been defined. Panics
        // if it is repeated (means `deconflict` is broken)
        use std::collections::{HashMap, HashSet};
        #[inline(always)]
        fn is_unique(var: &Var, map: &mut HashMap<Var, bool>) {
            if map.insert(var.clone(), false).is_some() {
                panic!("Variable {var} already defined. `deconflict` implementation broken.");
            }
        }
        // Check if variable is bound and sets it as "used"
        #[inline(always)]
        fn is_bound(var: &Var, map: &mut HashMap<Var, bool>) -> Result<()> {
            if map.insert(var.clone(), true).is_none() {
                bail!("Variable {var} is unbound.");
            }
            Ok(())
        }
        fn recurse(block: &Block, return_size: usize, map: &mut HashMap<Var, bool>) -> Result<()> {
            for op in &block.ops {
                match op {
                    Op::Call(out, func, inp) => {
                        if out.len() != func.output_size {
                            bail!(
                                "Function's return size {} different from number of variables {} bound by the call",
                                out.len(),
                                func.output_size
                            )
                        }
                        if inp.len() != func.input_params.len() {
                            bail!(
                                "The number of arguments {} differs from the function's input size {}",
                                inp.len(),
                                func.input_params.len()
                            )
                        }
                        inp.iter().try_for_each(|arg| is_bound(arg, map))?;
                        out.iter().for_each(|var| is_unique(var, map));
                        func.input_params.iter().for_each(|var| is_unique(var, map));
                        recurse(&func.body, func.output_size, map)?;
                    }
                    Op::Null(tgt, _tag) => {
                        is_unique(tgt, map);
                    }
                    Op::Lit(tgt, _lit) => {
                        is_unique(tgt, map);
                    }
                    Op::Cast(tgt, _tag, src) => {
                        is_bound(src, map)?;
                        is_unique(tgt, map);
                    }
                    Op::Add(tgt, a, b)
                    | Op::Sub(tgt, a, b)
                    | Op::Mul(tgt, a, b)
                    | Op::Div(tgt, a, b) => {
                        is_bound(a, map)?;
                        is_bound(b, map)?;
                        is_unique(tgt, map);
                    }
                    Op::Emit(a) => {
                        is_bound(a, map)?;
                    }
                    Op::Hash2(img, _tag, preimg) => {
                        preimg.iter().try_for_each(|arg| is_bound(arg, map))?;
                        is_unique(img, map);
                    }
                    Op::Hash3(img, _tag, preimg) => {
                        preimg.iter().try_for_each(|arg| is_bound(arg, map))?;
                        is_unique(img, map);
                    }
                    Op::Hash4(img, _tag, preimg) => {
                        preimg.iter().try_for_each(|arg| is_bound(arg, map))?;
                        is_unique(img, map);
                    }
                    Op::Unhash2(preimg, img) => {
                        is_bound(img, map)?;
                        preimg.iter().for_each(|var| is_unique(var, map))
                    }
                    Op::Unhash3(preimg, img) => {
                        is_bound(img, map)?;
                        preimg.iter().for_each(|var| is_unique(var, map))
                    }
                    Op::Unhash4(preimg, img) => {
                        is_bound(img, map)?;
                        preimg.iter().for_each(|var| is_unique(var, map))
                    }
                    Op::Hide(tgt, sec, src) => {
                        is_bound(sec, map)?;
                        is_bound(src, map)?;
                        is_unique(tgt, map);
                    }
                    Op::Open(tgt_secret, tgt_ptr, comm_or_num) => {
                        is_bound(comm_or_num, map)?;
                        is_unique(tgt_secret, map);
                        is_unique(tgt_ptr, map);
                    }
                }
            }
            match &block.ctrl {
                Ctrl::Return(return_vars) => {
                    return_vars.iter().try_for_each(|arg| is_bound(arg, map))?;
                    if return_vars.len() != return_size {
                        bail!(
                            "Return size {} different from expected size of return {}",
                            return_vars.len(),
                            return_size
                        )
                    }
                }
                Ctrl::MatchTag(var, cases, def) => {
                    is_bound(var, map)?;
                    let mut tags = HashSet::new();
                    let mut kind = None;
                    for (tag, block) in cases {
                        let tag_kind = match tag {
                            Tag::Expr(..) => 0,
                            Tag::Cont(..) => 1,
                            Tag::Ctrl(..) => 4,
                        };
                        if let Some(kind) = kind {
                            if kind != tag_kind {
                                bail!("Only tags of the same kind allowed.");
                            }
                        } else {
                            kind = Some(tag_kind)
                        }
                        if !tags.insert(tag) {
                            bail!("Tag {tag} already defined.");
                        }
                        recurse(block, return_size, map)?;
                    }
                    match def {
                        Some(def) => recurse(def, return_size, map)?,
                        None => (),
                    }
                }
                Ctrl::MatchVal(var, cases, def) => {
                    is_bound(var, map)?;
                    let mut lits = HashSet::new();
                    let mut kind = None;
                    for (lit, block) in cases {
                        let lit_kind = match lit {
                            Lit::Num(..) => 0,
                            Lit::String(..) => 1,
                            Lit::Symbol(..) => 2,
                        };
                        if let Some(kind) = kind {
                            if kind != lit_kind {
                                bail!("Only values of the same kind allowed.");
                            }
                        } else {
                            kind = Some(lit_kind)
                        }
                        if !lits.insert(lit) {
                            bail!("Case {:?} already defined.", lit);
                        }
                        recurse(block, return_size, map)?;
                    }
                    match def {
                        Some(def) => recurse(def, return_size, map)?,
                        None => (),
                    }
                }
                Ctrl::IfEq(x, y, eq_block, else_block) => {
                    is_bound(x, map)?;
                    is_bound(y, map)?;
                    recurse(eq_block, return_size, map)?;
                    recurse(else_block, return_size, map)?;
                }
            }
            Ok(())
        }
        let map = &mut HashMap::new();
        self.input_params.iter().for_each(|var| is_unique(var, map));
        recurse(&self.body, self.output_size, map)?;
        for (var, u) in map.iter() {
            let ch = var.0.chars().next().unwrap();
            if !u && ch != '_' {
                bail!("Variable {var} not used. If intended, please prefix it with \"_\"")
            }
        }
        Ok(())
    }

    /// Deconflict will replace conflicting names and make the function SSA. The
    /// conflict resolution is achieved by prepending conflicting variables by
    /// a unique identifier.
    ///
    /// Note: this function is not supposed to be called manually. It's used by
    /// `Func::new`, which is the API that should be used directly.
    fn deconflict(mut self, map: &mut VarMap<Var>, uniq: &mut usize) -> Result<Self> {
        self.input_params = self
            .input_params
            .into_iter()
            .map(|var| {
                let new_var = var.make_unique(uniq);
                map.insert(var, new_var.clone());
                new_var
            })
            .collect();
        self.body = self.body.deconflict(map, uniq)?;
        Ok(self)
    }

    /// Unrolls a function of equal input/output sizes `n` times
    pub fn unroll(&self, n: usize) -> Result<Self> {
        if self.output_size != self.input_params.len() {
            bail!("Cannot unroll a function with different number of inputs and outputs")
        }
        let mut ops = vec![];
        // This loop will create a sequence of n-1
        // let x1, ... xn = f(x1, ..., xn);
        for _ in 0..n - 1 {
            let inp = self.input_params.clone();
            let func = Box::new(self.clone());
            let out = self.input_params.clone();
            ops.push(Op::Call(inp, func, out))
        }
        // The last call can be inlined by just extending ops
        // and using the same control statement
        ops.extend_from_slice(&self.body.ops);
        let ctrl = self.body.ctrl.clone();
        let body = Block { ops, ctrl };
        Self::new(
            self.name.clone(),
            self.input_params.clone(),
            self.output_size,
            body,
        )
    }

    pub fn init_store<F: LurkField>(&self) -> Store<F> {
        let mut store = Store::default();
        self.body.intern_lits(&mut store);
        store
    }
}

impl Block {
    fn deconflict(self, map: &mut VarMap<Var>, uniq: &mut usize) -> Result<Self> {
        #[inline]
        fn insert_one(map: &mut VarMap<Var>, uniq: &mut usize, var: &Var) -> Var {
            let new_var = var.make_unique(uniq);
            map.insert(var.clone(), new_var.clone());
            new_var
        }

        #[inline]
        fn insert_many(map: &mut VarMap<Var>, uniq: &mut usize, vars: &[Var]) -> Vec<Var> {
            vars.iter().map(|var| insert_one(map, uniq, var)).collect()
        }

        let mut ops = Vec::with_capacity(self.ops.len());
        for op in self.ops {
            match op {
                Op::Call(out, func, inp) => {
                    let inp = map.get_many_cloned(&inp)?;
                    let out = insert_many(map, uniq, &out);
                    let func = Box::new(func.deconflict(map, uniq)?);
                    ops.push(Op::Call(out, func, inp))
                }
                Op::Null(tgt, tag) => ops.push(Op::Null(insert_one(map, uniq, &tgt), tag)),
                Op::Lit(tgt, lit) => ops.push(Op::Lit(insert_one(map, uniq, &tgt), lit)),
                Op::Cast(tgt, tag, src) => {
                    let src = map.get_cloned(&src)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Cast(tgt, tag, src))
                }
                Op::Add(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Add(tgt, a, b))
                }
                Op::Sub(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Sub(tgt, a, b))
                }
                Op::Mul(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Mul(tgt, a, b))
                }
                Op::Div(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Div(tgt, a, b))
                }
                Op::Emit(a) => {
                    let a = map.get_cloned(&a)?;
                    ops.push(Op::Emit(a))
                }
                Op::Hash2(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, uniq, &img);
                    ops.push(Op::Hash2(img, tag, preimg))
                }
                Op::Hash3(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, uniq, &img);
                    ops.push(Op::Hash3(img, tag, preimg))
                }
                Op::Hash4(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, uniq, &img);
                    ops.push(Op::Hash4(img, tag, preimg))
                }
                Op::Unhash2(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, uniq, &preimg);
                    ops.push(Op::Unhash2(preimg.try_into().unwrap(), img))
                }
                Op::Unhash3(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, uniq, &preimg);
                    ops.push(Op::Unhash3(preimg.try_into().unwrap(), img))
                }
                Op::Unhash4(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, uniq, &preimg);
                    ops.push(Op::Unhash4(preimg.try_into().unwrap(), img))
                }
                Op::Hide(tgt, sec, pay) => {
                    let sec = map.get_cloned(&sec)?;
                    let pay = map.get_cloned(&pay)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Hide(tgt, sec, pay))
                }
                Op::Open(sec, pay, comm_or_num) => {
                    let comm_or_num = map.get_cloned(&comm_or_num)?;
                    let sec = insert_one(map, uniq, &sec);
                    let pay = insert_one(map, uniq, &pay);
                    ops.push(Op::Open(sec, pay, comm_or_num))
                }
            }
        }
        let ctrl = match self.ctrl {
            Ctrl::MatchTag(var, cases, def) => {
                let var = map.get_cloned(&var)?;
                let mut new_cases = Vec::with_capacity(cases.len());
                for (tag, case) in cases {
                    let new_case = case.deconflict(&mut map.clone(), uniq)?;
                    new_cases.push((tag, new_case));
                }
                let new_def = match def {
                    Some(def) => Some(Box::new(def.deconflict(map, uniq)?)),
                    None => None,
                };
                Ctrl::MatchTag(var, IndexMap::from_iter(new_cases), new_def)
            }
            Ctrl::MatchVal(var, cases, def) => {
                let var = map.get_cloned(&var)?;
                let mut new_cases = Vec::with_capacity(cases.len());
                for (lit, case) in cases {
                    let new_case = case.deconflict(&mut map.clone(), uniq)?;
                    new_cases.push((lit.clone(), new_case));
                }
                let new_def = match def {
                    Some(def) => Some(Box::new(def.deconflict(map, uniq)?)),
                    None => None,
                };
                Ctrl::MatchVal(var, IndexMap::from_iter(new_cases), new_def)
            }
            Ctrl::IfEq(x, y, eq_block, else_block) => {
                let x = map.get_cloned(&x)?;
                let y = map.get_cloned(&y)?;
                let eq_block = Box::new(eq_block.deconflict(&mut map.clone(), uniq)?);
                let else_block = Box::new(else_block.deconflict(&mut map.clone(), uniq)?);
                Ctrl::IfEq(x, y, eq_block, else_block)
            }
            Ctrl::Return(o) => Ctrl::Return(map.get_many_cloned(&o)?),
        };
        Ok(Block { ops, ctrl })
    }

    fn intern_lits<F: LurkField>(&self, store: &mut Store<F>) {
        for op in &self.ops {
            match op {
                Op::Call(_, func, _) => func.body.intern_lits(store),
                Op::Lit(_, lit) => {
                    lit.to_ptr(store);
                }
                _ => (),
            }
        }
        match &self.ctrl {
            Ctrl::IfEq(.., a, b) => {
                a.intern_lits(store);
                b.intern_lits(store);
            }
            Ctrl::MatchTag(_, cases, def) => {
                cases.values().for_each(|block| block.intern_lits(store));
                if let Some(def) = def {
                    def.intern_lits(store);
                }
            }
            Ctrl::MatchVal(_, cases, def) => {
                for (lit, b) in cases {
                    lit.to_ptr(store);
                    b.intern_lits(store);
                }
                if let Some(def) = def {
                    def.intern_lits(store);
                }
            }
            Ctrl::Return(..) => (),
        }
    }
}

impl Var {
    fn make_unique(&self, uniq: &mut usize) -> Var {
        *uniq += 1;
        Var(format!("{}#{}", self.name(), uniq).into())
    }
}

#[cfg(test)]
mod tests {
    use super::slot::SlotsCounter;
    use super::*;
    use crate::{func, lem::pointers::Ptr};
    use bellperson::util_cs::{test_cs::TestConstraintSystem, Comparable, Delta};
    use blstrs::Scalar as Fr;

    /// Helper function for testing circuit synthesis.
    ///   - `func` is the input LEM program.
    ///   - `exprs` is a set of input expressions that can exercise different LEM paths,
    ///   therefore this parameter can be used to test circuit uniformity among all the
    ///   provided expressions.
    ///   - `expected_slots` gives the number of expected slots for each type of hash.
    fn synthesize_test_helper(func: &Func, inputs: Vec<Ptr<Fr>>, expected_num_slots: SlotsCounter) {
        use crate::tag::ContTag::*;
        let store = &mut func.init_store();
        let outermost = Ptr::null(Tag::Cont(Outermost));
        let terminal = Ptr::null(Tag::Cont(Terminal));
        let error = Ptr::null(Tag::Cont(Error));
        let nil = store.intern_nil();
        let stop_cond = |output: &[Ptr<Fr>]| output[2] == terminal || output[2] == error;

        assert_eq!(func.slot, expected_num_slots);

        let computed_num_constraints = func.num_constraints::<Fr>(store);

        let mut cs_prev = None;
        for input in inputs.into_iter() {
            let input = [input, nil, outermost];
            let (frames, ..) = func.call_until(&input, store, stop_cond, 10).unwrap();

            let mut cs;

            for frame in frames.clone() {
                cs = TestConstraintSystem::<Fr>::new();
                func.synthesize(&mut cs, store, &frame).unwrap();
                assert!(cs.is_satisfied());
                assert_eq!(computed_num_constraints, cs.num_constraints());
                if let Some(cs_prev) = cs_prev {
                    // Check for all input expresssions that all frames are uniform.
                    assert_eq!(cs.delta(&cs_prev, true), Delta::Equal);
                }
                cs_prev = Some(cs);
            }
        }
    }

    #[test]
    fn accepts_virtual_nested_match_tag() {
        let lem = func!(foo(expr_in, env_in, cont_in): 3 => {
            match expr_in.tag {
                Expr::Num => {
                    let cont_out_terminal: Cont::Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                }
                Expr::Char => {
                    match expr_in.tag {
                        // This nested match excercises the need to pass on the
                        // information that we are on a virtual branch, because a
                        // constraint will be created for `cont_out_error` and it
                        // will need to be relaxed by an implication with a false
                        // premise.
                        Expr::Num => {
                            let cont_out_error: Cont::Error;
                            return (env_in, expr_in, cont_out_error);
                        }
                    }
                }
                Expr::Sym => {
                    match expr_in.tag {
                        // This nested match exercises the need to relax `popcount`
                        // because there is no match but it's on a virtual path, so
                        // we don't want to be too restrictive and demand that at
                        // least one path must be taken.
                        Expr::Char => {
                            return (cont_in, cont_in, cont_in);
                        }
                    }
                }
            }
        });

        let inputs = vec![Ptr::num(Fr::from_u64(42))];
        synthesize_test_helper(&lem, inputs, SlotsCounter::default());
    }

    #[test]
    fn resolves_conflicts_of_clashing_names_in_parallel_branches() {
        let lem = func!(foo(expr_in, env_in, _cont_in): 3 => {
            match expr_in.tag {
                // This match is creating `cont_out_terminal` on two different
                // branches, which, in theory, would cause troubles at allocation
                // time. We solve this problem by calling `LEMOP::deconflict`,
                // which turns one into `Num.cont_out_terminal` and the other into
                // `Char.cont_out_terminal`.
                Expr::Num => {
                    let cont_out_terminal: Cont::Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                }
                Expr::Char => {
                    let cont_out_terminal: Cont::Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                }
            }
        });

        let inputs = vec![Ptr::num(Fr::from_u64(42))];
        synthesize_test_helper(&lem, inputs, SlotsCounter::default());
    }

    #[test]
    fn handles_non_ssa() {
        let func = func!(foo(expr_in, _env_in, _cont_in): 3 => {
            let x: Expr::Cons = hash2(expr_in, expr_in);
            // The next line rewrites `x` and it should move on smoothly, matching
            // the expected number of constraints accordingly
            let x: Expr::Cons = hash2(x, x);
            let cont_out_terminal: Cont::Terminal;
            return (x, x, cont_out_terminal);
        });

        let inputs = vec![Ptr::num(Fr::from_u64(42))];
        synthesize_test_helper(&func, inputs, SlotsCounter::new((2, 0, 0)));
    }

    #[test]
    fn test_simple_all_paths_delta() {
        let lem = func!(foo(expr_in, env_in, _cont_in): 3 => {
            let cont_out_terminal: Cont::Terminal;
            return (expr_in, env_in, cont_out_terminal);
        });

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::default());
    }

    #[test]
    fn test_match_all_paths_delta() {
        let lem = func!(foo(expr_in, env_in, _cont_in): 3 => {
            match expr_in.tag {
                Expr::Num => {
                    let cont_out_terminal: Cont::Terminal;
                    return (expr_in, env_in, cont_out_terminal);
                }
                Expr::Char => {
                    let cont_out_error: Cont::Error;
                    return (expr_in, env_in, cont_out_error);
                }
            }
        });

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::default());
    }

    #[test]
    fn test_hash_slots() {
        let lem = func!(foo(expr_in, env_in, cont_in): 3 => {
            let _x: Expr::Cons = hash2(expr_in, env_in);
            let _y: Expr::Cons = hash3(expr_in, env_in, cont_in);
            let _z: Expr::Cons = hash4(expr_in, env_in, cont_in, cont_in);
            let t: Cont::Terminal;
            let p: Expr::Nil;
            match expr_in.tag {
                Expr::Num => {
                    let m: Expr::Cons = hash2(env_in, expr_in);
                    let n: Expr::Cons = hash3(cont_in, env_in, expr_in);
                    let _k: Expr::Cons = hash4(expr_in, cont_in, env_in, expr_in);
                    return (m, n, t);
                }
                Expr::Char => {
                    return (p, p, t);
                }
                Expr::Cons => {
                    return (p, p, t);
                }
                Expr::Nil => {
                    return (p, p, t);
                }
            }
        });

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::new((2, 2, 2)));
    }

    #[test]
    fn test_unhash_slots() {
        let lem = func!(foo(expr_in, env_in, cont_in): 3 => {
            let _x: Expr::Cons = hash2(expr_in, env_in);
            let _y: Expr::Cons = hash3(expr_in, env_in, cont_in);
            let _z: Expr::Cons = hash4(expr_in, env_in, cont_in, cont_in);
            let t: Cont::Terminal;
            let p: Expr::Nil;
            match expr_in.tag {
                Expr::Num => {
                    let m: Expr::Cons = hash2(env_in, expr_in);
                    let n: Expr::Cons = hash3(cont_in, env_in, expr_in);
                    let k: Expr::Cons = hash4(expr_in, cont_in, env_in, expr_in);
                    let (_m1, _m2) = unhash2(m);
                    let (_n1, _n2, _n3) = unhash3(n);
                    let (_k1, _k2, _k3, _k4) = unhash4(k);
                    return (m, n, t);
                }
                Expr::Char => {
                    return (p, p, t);
                }
                Expr::Cons => {
                    return (p, p, p);
                }
                Expr::Nil => {
                    return (p, p, p);
                }
            }
        });

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::new((3, 3, 3)));
    }

    #[test]
    fn test_unhash_nested_slots() {
        let lem = func!(foo(expr_in, env_in, cont_in): 3 => {
            let _x: Expr::Cons = hash2(expr_in, env_in);
            let _y: Expr::Cons = hash3(expr_in, env_in, cont_in);
            let _z: Expr::Cons = hash4(expr_in, env_in, cont_in, cont_in);
            let t: Cont::Terminal;
            let p: Expr::Nil;
            match expr_in.tag {
                Expr::Num => {
                    let m: Expr::Cons = hash2(env_in, expr_in);
                    let n: Expr::Cons = hash3(cont_in, env_in, expr_in);
                    let k: Expr::Cons = hash4(expr_in, cont_in, env_in, expr_in);
                    let (_m1, _m2) = unhash2(m);
                    let (_n1, _n2, _n3) = unhash3(n);
                    let (_k1, _k2, _k3, _k4) = unhash4(k);
                    match cont_in.tag {
                        Cont::Outermost => {
                            let _a: Expr::Cons = hash2(env_in, expr_in);
                            let _b: Expr::Cons = hash3(cont_in, env_in, expr_in);
                            let _c: Expr::Cons = hash4(expr_in, cont_in, env_in, expr_in);
                            return (m, n, t);
                        }
                        Cont::Terminal => {
                            let _d: Expr::Cons = hash2(env_in, expr_in);
                            let _e: Expr::Cons = hash3(cont_in, env_in, expr_in);
                            let _f: Expr::Cons = hash4(expr_in, cont_in, env_in, expr_in);
                            return (m, n, t);
                        }
                    }
                }
                Expr::Char => {
                    return (p, p, t);
                }
                Expr::Cons => {
                    return (p, p, p);
                }
                Expr::Nil => {
                    return (p, p, p);
                }
            }
        });

        let inputs = vec![Ptr::num(Fr::from_u64(42)), Ptr::char('c')];
        synthesize_test_helper(&lem, inputs, SlotsCounter::new((4, 4, 4)));
    }
}
