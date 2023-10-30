//! ## Lurk Evaluation Model (LEM)
//!
//! LEM is a simple, first order, referentially transparent language, designed to
//! allow writing Lurk's step function and Lurk coprocessors in a convenient way.
//!
//! The motivation behind LEM is the fact that hand-writing the circuit is a
//! fragile process that hinders experimentation and safety. Thus we would like
//! to bootstrap the circuit automatically, as well as an interpretation
//! algorithm that computes all non-deterministic hints for the circuit, given a
//! higher level description of the step function.
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
//! example, a `Op::Cons2(x, t, ys)` is to be understood as `let x = cons2(ys)`.
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
//! In particular, it will compute all the non-deterministic hints that are
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

pub mod circuit;
pub mod eval;
pub mod interpreter;
mod macros;
pub mod multiframe;
mod path;
pub mod pointers;
mod slot;
pub mod store;
mod var_map;
use anyhow::{bail, Result};
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[cfg(test)]
mod tests;

use crate::{
    field::LurkField,
    symbol::Symbol,
    tag::{ContTag, ExprTag, Op1, Op2, Tag as TagTrait},
};

use self::{pointers::Ptr, slot::SlotsCounter, store::Store, var_map::VarMap};

pub type AString = Arc<str>;

/// A `Func` is a LEM function. It consist of input params, output size and a
/// function body, which is a `Block`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Func {
    pub name: String,
    pub input_params: Vec<Var>,
    pub output_size: usize,
    pub body: Block,
    pub slots_count: SlotsCounter,
}

/// LEM variables
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct Var(AString);

/// LEM tags
#[derive(Copy, Debug, PartialEq, Clone, Eq, Hash, Serialize, Deserialize)]
pub enum Tag {
    Expr(ExprTag),
    Cont(ContTag),
    Op1(Op1),
    Op2(Op2),
}

impl TryFrom<u16> for Tag {
    type Error = anyhow::Error;

    fn try_from(val: u16) -> Result<Self, Self::Error> {
        if let Ok(tag) = ExprTag::try_from(val) {
            Ok(Tag::Expr(tag))
        } else if let Ok(tag) = ContTag::try_from(val) {
            Ok(Tag::Cont(tag))
        } else {
            bail!("Invalid u16 for Tag: {val}")
        }
    }
}

impl From<Tag> for u16 {
    fn from(val: Tag) -> Self {
        match val {
            Tag::Expr(tag) => tag.into(),
            Tag::Cont(tag) => tag.into(),
            Tag::Op1(tag) => tag.into(),
            Tag::Op2(tag) => tag.into(),
        }
    }
}

impl TagTrait for Tag {
    fn from_field<F: LurkField>(f: &F) -> Option<Self> {
        Self::try_from(f.to_u16()?).ok()
    }

    fn to_field<F: LurkField>(&self) -> F {
        Tag::to_field(self)
    }
}

impl Tag {
    #[inline]
    pub fn to_field<F: LurkField>(&self) -> F {
        match self {
            Tag::Expr(tag) => tag.to_field(),
            Tag::Cont(tag) => tag.to_field(),
            Tag::Op1(tag) => tag.to_field(),
            Tag::Op2(tag) => tag.to_field(),
        }
    }
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Tag::{Cont, Expr, Op1, Op2};
        match self {
            Expr(tag) => write!(f, "expr.{}", tag),
            Cont(tag) => write!(f, "cont.{}", tag),
            Op1(tag) => write!(f, "op1.{}", tag),
            Op2(tag) => write!(f, "op2.{}", tag),
        }
    }
}

/// LEM literals
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum Lit {
    // TODO maybe it should be a LurkField instead of u128
    Num(u128),
    String(String),
    Symbol(Symbol),
}

impl Lit {
    pub fn to_ptr<F: LurkField>(&self, store: &Store<F>) -> Ptr<F> {
        match self {
            Self::Symbol(s) => store.intern_symbol(s),
            Self::String(s) => store.intern_string(s),
            Self::Num(num) => Ptr::num(F::from_u128(*num)),
        }
    }

    pub fn from_ptr<F: LurkField>(ptr: &Ptr<F>, store: &Store<F>) -> Option<Self> {
        use ExprTag::{Num, Str, Sym};
        use Tag::Expr;
        match ptr.tag() {
            Expr(Num) => match ptr {
                Ptr::Atom(_, f) => {
                    let num = LurkField::to_u128_unchecked(f);
                    Some(Self::Num(num))
                }
                _ => unreachable!(),
            },
            Expr(Str) => store.fetch_string(ptr).map(Lit::String),
            Expr(Sym) => store.fetch_symbol(ptr).map(Lit::Symbol),
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
    /// `MatchTag(x, cases, def)` checks whether the tag of `x` matches some tag
    /// among the ones provided in `cases`. If so, run the corresponding `Block`.
    /// Run `def` otherwise
    MatchTag(Var, IndexMap<Tag, Block>, Option<Box<Block>>),
    /// `MatchSymbol(x, cases, def)` requires that `x` is a symbol and checks
    /// whether `x` matches some symbol among the ones provided in `cases`. If so,
    /// run the corresponding `Block`. Run `def` otherwise
    MatchSymbol(Var, IndexMap<Symbol, Block>, Option<Box<Block>>),
    /// `If(x, true_block, false_block)` runs `true_block` if `x` is true, and
    /// otherwise runs `false_block`
    If(Var, Box<Block>, Box<Block>),
    /// `Return(rets)` sets the output to `rets`
    Return(Vec<Var>),
}

/// The atomic operations of LEMs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    /// `Cproc(ys, c, xs)` binds `ys` to the results of coprocessor `c` applied to `xs`
    Cproc(Vec<Var>, Symbol, Vec<Var>),
    /// `Call(ys, f, xs)` binds `ys` to the results of `f` applied to `xs`
    Call(Vec<Var>, Box<Func>, Vec<Var>),
    /// `Copy(x, y)` binds `x` to a copy of what `y` is bound to
    Copy(Var, Var),
    /// `Null(x, t)` binds `x` to a `Ptr::Leaf(t, F::zero())`
    Null(Var, Tag),
    /// `Lit(x, l)` binds `x` to the pointer representing that `Lit`
    Lit(Var, Lit),
    /// `Cast(y, t, x)` binds `y` to a pointer with tag `t` and the hash of `x`
    Cast(Var, Tag, Var),
    /// `EqTag(y, a, b)` binds `y` to the boolean `a.tag == b.tag`
    EqTag(Var, Var, Var),
    /// `EqVal(y, a, b)` binds `y` to the boolean `a.val == b.val`
    EqVal(Var, Var, Var),
    /// `Not(y, a)` binds `y` to the negation of `a`
    Not(Var, Var),
    /// `And(y, a, b)` binds `y` to the conjunction of `a` and `b`
    And(Var, Var, Var),
    /// `Or(y, a, b)` binds `y` to the disjunction of `a` and `b`
    Or(Var, Var, Var),
    /// `Add(y, a, b)` binds `y` to the sum of `a` and `b`
    Add(Var, Var, Var),
    /// `Sub(y, a, b)` binds `y` to the sum of `a` and `b`
    Sub(Var, Var, Var),
    /// `Mul(y, a, b)` binds `y` to the sum of `a` and `b`
    Mul(Var, Var, Var),
    /// `Div(y, a, b)` binds `y` to the sum of `a` and `b`
    Div(Var, Var, Var),
    /// `Lt(y, a, b)` binds `y` to `1` if `a < b`, or to `0` otherwise
    Lt(Var, Var, Var),
    /// `Trunc(y, a, n)` binds `y` to `a` truncated to `n` bits, up to 64 bits
    Trunc(Var, Var, u32),
    /// `DivRem64(ys, a, b)` binds `ys` to `(a / b, a % b)` as if they were u64
    DivRem64([Var; 2], Var, Var),
    /// `Emit(v)` simply prints out the value of `v` when interpreting the code
    Emit(Var),
    /// `Cons2(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 2 children `ys`
    Cons2(Var, Tag, [Var; 2]),
    /// `Cons3(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 3 children `ys`
    Cons3(Var, Tag, [Var; 3]),
    /// `Cons4(x, t, ys)` binds `x` to a `Ptr` with tag `t` and 4 children `ys`
    Cons4(Var, Tag, [Var; 4]),
    /// `Decons2([a, b], x)` binds `a` and `b` to the 2 children of `x`
    Decons2([Var; 2], Var),
    /// `Decons3([a, b, c], x)` binds `a`, `b` and `c` to the 3 children of `x`
    Decons3([Var; 3], Var),
    /// `Decons4([a, b, c, d], x)` binds `a`, `b`, `c` and `d` to the 4 children of `x`
    Decons4([Var; 4], Var),
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
        let slots_count = body.count_slots();
        let func = Func {
            slots_count,
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
        use std::collections::{HashMap, HashSet};

        /// Check if variable has already been defined. Panics
        /// if it is repeated (means `deconflict` is broken)
        #[inline]
        fn is_unique(var: &Var, map: &mut HashMap<Var, bool>) {
            assert!(
                map.insert(var.clone(), false).is_none(),
                "Variable {var} already defined. `deconflict` implementation broken."
            );
        }

        /// Check if variable is bound and sets it as "used"
        #[inline]
        fn is_bound(var: &Var, map: &mut HashMap<Var, bool>) -> Result<()> {
            if map.insert(var.clone(), true).is_none() {
                bail!("Variable {var} is unbound.");
            }
            Ok(())
        }

        fn recurse(block: &Block, return_size: usize, map: &mut HashMap<Var, bool>) -> Result<()> {
            for op in &block.ops {
                match op {
                    Op::Cproc(out, _, inp) => {
                        inp.iter().try_for_each(|arg| is_bound(arg, map))?;
                        out.iter().for_each(|var| is_unique(var, map));
                    }
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
                    Op::Copy(tgt, src) => {
                        is_bound(src, map)?;
                        is_unique(tgt, map);
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
                    Op::Not(tgt, a) => {
                        is_bound(a, map)?;
                        is_unique(tgt, map);
                    }
                    Op::EqTag(tgt, a, b)
                    | Op::EqVal(tgt, a, b)
                    | Op::And(tgt, a, b)
                    | Op::Or(tgt, a, b)
                    | Op::Add(tgt, a, b)
                    | Op::Sub(tgt, a, b)
                    | Op::Mul(tgt, a, b)
                    | Op::Div(tgt, a, b)
                    | Op::Lt(tgt, a, b) => {
                        is_bound(a, map)?;
                        is_bound(b, map)?;
                        is_unique(tgt, map);
                    }
                    Op::Trunc(tgt, a, n) => {
                        if *n > 64 {
                            bail!("Cannot yet truncate over 64 bits")
                        }
                        is_bound(a, map)?;
                        is_unique(tgt, map);
                    }
                    Op::DivRem64(tgt, a, b) => {
                        is_bound(a, map)?;
                        is_bound(b, map)?;
                        tgt.iter().for_each(|var| is_unique(var, map))
                    }
                    Op::Emit(a) => {
                        is_bound(a, map)?;
                    }
                    Op::Cons2(img, _tag, preimg) => {
                        preimg.iter().try_for_each(|arg| is_bound(arg, map))?;
                        is_unique(img, map);
                    }
                    Op::Cons3(img, _tag, preimg) => {
                        preimg.iter().try_for_each(|arg| is_bound(arg, map))?;
                        is_unique(img, map);
                    }
                    Op::Cons4(img, _tag, preimg) => {
                        preimg.iter().try_for_each(|arg| is_bound(arg, map))?;
                        is_unique(img, map);
                    }
                    Op::Decons2(preimg, img) => {
                        is_bound(img, map)?;
                        preimg.iter().for_each(|var| is_unique(var, map))
                    }
                    Op::Decons3(preimg, img) => {
                        is_bound(img, map)?;
                        preimg.iter().for_each(|var| is_unique(var, map))
                    }
                    Op::Decons4(preimg, img) => {
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
                        // make sure that this `MatchTag` doesn't have weird semantics
                        let tag_kind = match tag {
                            Tag::Expr(..) => 0,
                            Tag::Cont(..) => 1,
                            Tag::Op1(..) => 2,
                            Tag::Op2(..) => 3,
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
                Ctrl::MatchSymbol(var, cases, def) => {
                    is_bound(var, map)?;
                    for block in cases.values() {
                        recurse(block, return_size, map)?;
                    }
                    if let Some(def) = def {
                        recurse(def, return_size, map)?;
                    }
                }
                Ctrl::If(x, true_block, false_block) => {
                    is_bound(x, map)?;
                    recurse(true_block, return_size, map)?;
                    recurse(false_block, return_size, map)?;
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
                Op::Cproc(out, sym, inp) => {
                    let inp = map.get_many_cloned(&inp)?;
                    let out = insert_many(map, uniq, &out);
                    ops.push(Op::Cproc(out, sym, inp))
                }
                Op::Call(out, func, inp) => {
                    let inp = map.get_many_cloned(&inp)?;
                    let out = insert_many(map, uniq, &out);
                    let func = Box::new(func.deconflict(map, uniq)?);
                    ops.push(Op::Call(out, func, inp))
                }
                Op::Copy(tgt, src) => {
                    ops.push(Op::Copy(insert_one(map, uniq, &tgt), map.get_cloned(&src)?))
                }
                Op::Null(tgt, tag) => ops.push(Op::Null(insert_one(map, uniq, &tgt), tag)),
                Op::Lit(tgt, lit) => ops.push(Op::Lit(insert_one(map, uniq, &tgt), lit)),
                Op::Cast(tgt, tag, src) => {
                    let src = map.get_cloned(&src)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Cast(tgt, tag, src))
                }
                Op::EqTag(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::EqTag(tgt, a, b))
                }
                Op::EqVal(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::EqVal(tgt, a, b))
                }
                Op::Not(tgt, a) => {
                    let a = map.get_cloned(&a)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Not(tgt, a))
                }
                Op::And(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::And(tgt, a, b))
                }
                Op::Or(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Or(tgt, a, b))
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
                Op::Lt(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Lt(tgt, a, b))
                }
                Op::Trunc(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let tgt = insert_one(map, uniq, &tgt);
                    ops.push(Op::Trunc(tgt, a, b))
                }
                Op::DivRem64(tgt, a, b) => {
                    let a = map.get_cloned(&a)?;
                    let b = map.get_cloned(&b)?;
                    let tgt = insert_many(map, uniq, &tgt);
                    ops.push(Op::DivRem64(tgt.try_into().unwrap(), a, b))
                }
                Op::Emit(a) => {
                    let a = map.get_cloned(&a)?;
                    ops.push(Op::Emit(a))
                }
                Op::Cons2(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, uniq, &img);
                    ops.push(Op::Cons2(img, tag, preimg))
                }
                Op::Cons3(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, uniq, &img);
                    ops.push(Op::Cons3(img, tag, preimg))
                }
                Op::Cons4(img, tag, preimg) => {
                    let preimg = map.get_many_cloned(&preimg)?.try_into().unwrap();
                    let img = insert_one(map, uniq, &img);
                    ops.push(Op::Cons4(img, tag, preimg))
                }
                Op::Decons2(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, uniq, &preimg);
                    ops.push(Op::Decons2(preimg.try_into().unwrap(), img))
                }
                Op::Decons3(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, uniq, &preimg);
                    ops.push(Op::Decons3(preimg.try_into().unwrap(), img))
                }
                Op::Decons4(preimg, img) => {
                    let img = map.get_cloned(&img)?;
                    let preimg = insert_many(map, uniq, &preimg);
                    ops.push(Op::Decons4(preimg.try_into().unwrap(), img))
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
            Ctrl::MatchSymbol(var, cases, def) => {
                let var = map.get_cloned(&var)?;
                let mut new_cases = Vec::with_capacity(cases.len());
                for (sym, case) in cases {
                    let new_case = case.deconflict(&mut map.clone(), uniq)?;
                    new_cases.push((sym.clone(), new_case));
                }
                let new_def = match def {
                    Some(def) => Some(Box::new(def.deconflict(map, uniq)?)),
                    None => None,
                };
                Ctrl::MatchSymbol(var, IndexMap::from_iter(new_cases), new_def)
            }
            Ctrl::If(x, true_block, false_block) => {
                let x = map.get_cloned(&x)?;
                let true_block = Box::new(true_block.deconflict(&mut map.clone(), uniq)?);
                let false_block = Box::new(false_block.deconflict(&mut map.clone(), uniq)?);
                Ctrl::If(x, true_block, false_block)
            }
            Ctrl::Return(o) => Ctrl::Return(map.get_many_cloned(&o)?),
        };
        Ok(Block { ops, ctrl })
    }
}

impl Var {
    #[inline]
    pub fn new(name: &str) -> Self {
        Self(name.into())
    }

    fn make_unique(&self, uniq: &mut usize) -> Var {
        *uniq += 1;
        Var(format!("{}#{}", self.name(), uniq).into())
    }
}
