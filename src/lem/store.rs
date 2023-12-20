use anyhow::{bail, Result};
use arc_swap::ArcSwap;
use bellpepper::util_cs::witness_cs::SizedWitness;
use elsa::{
    sync::index_set::FrozenIndexSet,
    sync::{FrozenMap, FrozenVec},
};
use indexmap::IndexSet;
use neptune::Poseidon;
use nom::{sequence::preceded, Parser};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use std::{cell::RefCell, rc::Rc, sync::Arc};

use crate::{
    field::{FWrap, LurkField},
    hash::{InversePoseidonCache, PoseidonCache},
    lem::Tag,
    parser::{syntax, Error, Span},
    state::{lurk_sym, user_sym, State},
    symbol::Symbol,
    syntax::Syntax,
    tag::ContTag::{
        self, Binop, Binop2, Call, Call0, Call2, Dummy, Emit, If, Let, LetRec, Lookup, Outermost,
        Tail, Terminal, Unop,
    },
    tag::ExprTag::{Char, Comm, Cons, Cproc, Fun, Key, Nil, Num, Str, Sym, Thunk, U64},
};

use super::pointers::{Ptr, ZPtr};

/// The `Store` is a crucial part of Lurk's implementation and tries to be a
/// vesatile data structure for many parts of Lurk's data pipeline.
///
/// It holds Lurk data structured as trees of `Ptr`s. When a `Ptr` has children,
/// we store them in the `IndexSet`s available: `tuple2`, `tuple3` or `tuple4`.
/// These data structures speed up LEM interpretation because lookups by indices
/// are fast.
///
/// The `Store` provides an infra to speed up interning strings and symbols. This
/// data is saved in `string_ptr_cache` and `symbol_ptr_cache`.
///
/// There's also a process that we call "hydration", in which we use Poseidon
/// hashes to compute the (stable) hash of the children of a pointer. These hashes
/// are necessary when we want to create Lurk proofs because the circuit consumes
/// elements of the `LurkField`, not (unstable) indices of `IndexSet`s.
///
/// Lastly, we have a `HashMap` to hold committed data, which can be retrieved by
/// the resulting commitment hash.
#[derive(Debug)]
pub struct Store<F: LurkField> {
    f_elts: FrozenIndexSet<Box<FWrap<F>>>,
    tuple2: FrozenIndexSet<Box<(Ptr, Ptr)>>,
    tuple3: FrozenIndexSet<Box<(Ptr, Ptr, Ptr)>>,
    tuple4: FrozenIndexSet<Box<(Ptr, Ptr, Ptr, Ptr)>>,

    string_ptr_cache: FrozenMap<String, Box<Ptr>>,
    symbol_ptr_cache: FrozenMap<Symbol, Box<Ptr>>,

    ptr_string_cache: FrozenMap<Ptr, String>,
    ptr_symbol_cache: FrozenMap<Ptr, Box<Symbol>>,

    pub poseidon_cache: PoseidonCache<F>,
    pub inverse_poseidon_cache: InversePoseidonCache<F>,

    dehydrated: ArcSwap<FrozenVec<Box<Ptr>>>,
    z_cache: FrozenMap<Ptr, Box<ZPtr<F>>>,
    inverse_z_cache: FrozenMap<ZPtr<F>, Box<Ptr>>,

    comms: FrozenMap<FWrap<F>, Box<(F, Ptr)>>, // hash -> (secret, src)

    // cached indices for the hashes of 3, 4, 6 and 8 padded zeros
    pub hash3zeros_idx: usize,
    pub hash4zeros_idx: usize,
    pub hash6zeros_idx: usize,
    pub hash8zeros_idx: usize,
}

impl<F: LurkField> Default for Store<F> {
    fn default() -> Self {
        let poseidon_cache = PoseidonCache::default();
        let hash3zeros = poseidon_cache.hash3(&[F::ZERO; 3]);
        let hash4zeros = poseidon_cache.hash4(&[F::ZERO; 4]);
        let hash6zeros = poseidon_cache.hash6(&[F::ZERO; 6]);
        let hash8zeros = poseidon_cache.hash8(&[F::ZERO; 8]);

        let f_elts = FrozenIndexSet::default();
        let (hash3zeros_idx, _) = f_elts.insert_probe(FWrap(hash3zeros).into());
        let (hash4zeros_idx, _) = f_elts.insert_probe(FWrap(hash4zeros).into());
        let (hash6zeros_idx, _) = f_elts.insert_probe(FWrap(hash6zeros).into());
        let (hash8zeros_idx, _) = f_elts.insert_probe(FWrap(hash8zeros).into());

        Self {
            f_elts,
            tuple2: Default::default(),
            tuple3: Default::default(),
            tuple4: Default::default(),
            string_ptr_cache: Default::default(),
            symbol_ptr_cache: Default::default(),
            ptr_string_cache: Default::default(),
            ptr_symbol_cache: Default::default(),
            poseidon_cache,
            inverse_poseidon_cache: Default::default(),
            dehydrated: Default::default(),
            z_cache: Default::default(),
            inverse_z_cache: Default::default(),
            comms: Default::default(),
            hash3zeros_idx,
            hash4zeros_idx,
            hash6zeros_idx,
            hash8zeros_idx,
        }
    }
}

impl<F: LurkField> Store<F> {
    /// Cost of poseidon hash with arity 3, including the input
    #[inline]
    pub fn hash3_cost(&self) -> usize {
        Poseidon::new(self.poseidon_cache.constants.c3()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 4, including the input
    #[inline]
    pub fn hash4_cost(&self) -> usize {
        Poseidon::new(self.poseidon_cache.constants.c4()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 6, including the input
    #[inline]
    pub fn hash6_cost(&self) -> usize {
        Poseidon::new(self.poseidon_cache.constants.c6()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 8, including the input
    #[inline]
    pub fn hash8_cost(&self) -> usize {
        Poseidon::new(self.poseidon_cache.constants.c8()).num_aux() + 1
    }

    /// Retrieves the hash of 3 padded zeros
    #[inline]
    pub fn hash3zeros(&self) -> &F {
        self.expect_f(self.hash3zeros_idx)
    }

    /// Retrieves the hash of 4 padded zeros
    #[inline]
    pub fn hash4zeros(&self) -> &F {
        self.expect_f(self.hash4zeros_idx)
    }

    /// Retrieves the hash of 6 padded zeros
    #[inline]
    pub fn hash6zeros(&self) -> &F {
        self.expect_f(self.hash6zeros_idx)
    }

    /// Retrieves the hash of 8 padded zeros
    #[inline]
    pub fn hash8zeros(&self) -> &F {
        self.expect_f(self.hash8zeros_idx)
    }

    #[inline]
    pub fn intern_f(&self, f: F) -> (usize, bool) {
        self.f_elts.insert_probe(Box::new(FWrap(f)))
    }

    /// Creates an atom `Ptr` which points to a cached element of the finite
    /// field `F`
    pub fn intern_atom(&self, tag: Tag, f: F) -> Ptr {
        let (idx, inserted) = self.intern_f(f);
        let ptr = Ptr::Atom(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    /// Similar to `intern_atom` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_atom_hydrated(&self, tag: Tag, f: F, z: ZPtr<F>) -> Ptr {
        let ptr = Ptr::Atom(tag, self.intern_f(f).0);
        self.z_cache.insert(ptr, Box::new(z));
        self.inverse_z_cache.insert(z, Box::new(ptr));
        ptr
    }

    /// Creates a `Ptr` that's a parent of two children
    pub fn intern_2_ptrs(&self, tag: Tag, a: Ptr, b: Ptr) -> Ptr {
        let (idx, inserted) = self.tuple2.insert_probe(Box::new((a, b)));
        let ptr = Ptr::Tuple2(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    /// Similar to `intern_2_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_2_ptrs_hydrated(&self, tag: Tag, a: Ptr, b: Ptr, z: ZPtr<F>) -> Ptr {
        let ptr = Ptr::Tuple2(tag, self.tuple2.insert_probe(Box::new((a, b))).0);
        self.z_cache.insert(ptr, Box::new(z));
        self.inverse_z_cache.insert(z, Box::new(ptr));
        ptr
    }

    /// Creates a `Ptr` that's a parent of three children
    pub fn intern_3_ptrs(&self, tag: Tag, a: Ptr, b: Ptr, c: Ptr) -> Ptr {
        let (idx, inserted) = self.tuple3.insert_probe(Box::new((a, b, c)));
        let ptr = Ptr::Tuple3(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    /// Similar to `intern_3_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_3_ptrs_hydrated(&self, tag: Tag, a: Ptr, b: Ptr, c: Ptr, z: ZPtr<F>) -> Ptr {
        let ptr = Ptr::Tuple3(tag, self.tuple3.insert_probe(Box::new((a, b, c))).0);
        self.z_cache.insert(ptr, Box::new(z));
        self.inverse_z_cache.insert(z, Box::new(ptr));
        ptr
    }

    /// Creates a `Ptr` that's a parent of four children
    pub fn intern_4_ptrs(&self, tag: Tag, a: Ptr, b: Ptr, c: Ptr, d: Ptr) -> Ptr {
        let (idx, inserted) = self.tuple4.insert_probe(Box::new((a, b, c, d)));
        let ptr = Ptr::Tuple4(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    /// Similar to `intern_4_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_4_ptrs_hydrated(
        &self,
        tag: Tag,
        a: Ptr,
        b: Ptr,
        c: Ptr,
        d: Ptr,
        z: ZPtr<F>,
    ) -> Ptr {
        let ptr = Ptr::Tuple4(tag, self.tuple4.insert_probe(Box::new((a, b, c, d))).0);
        self.z_cache.insert(ptr, Box::new(z));
        self.inverse_z_cache.insert(z, Box::new(ptr));
        ptr
    }

    #[inline]
    pub fn fetch_f(&self, idx: usize) -> Option<&F> {
        self.f_elts.get_index(idx).map(|fw| &fw.0)
    }

    #[inline]
    pub fn fetch_2_ptrs(&self, idx: usize) -> Option<&(Ptr, Ptr)> {
        self.tuple2.get_index(idx)
    }

    #[inline]
    pub fn fetch_3_ptrs(&self, idx: usize) -> Option<&(Ptr, Ptr, Ptr)> {
        self.tuple3.get_index(idx)
    }

    #[inline]
    pub fn fetch_4_ptrs(&self, idx: usize) -> Option<&(Ptr, Ptr, Ptr, Ptr)> {
        self.tuple4.get_index(idx)
    }

    #[inline]
    pub fn num(&self, f: F) -> Ptr {
        self.intern_atom(Tag::Expr(Num), f)
    }

    #[inline]
    pub fn num_u64(&self, u: u64) -> Ptr {
        self.intern_atom(Tag::Expr(Num), F::from_u64(u))
    }

    #[inline]
    pub fn u64(&self, u: u64) -> Ptr {
        self.intern_atom(Tag::Expr(U64), F::from_u64(u))
    }

    #[inline]
    pub fn char(&self, c: char) -> Ptr {
        self.intern_atom(Tag::Expr(Char), F::from_char(c))
    }

    #[inline]
    pub fn comm(&self, hash: F) -> Ptr {
        self.intern_atom(Tag::Expr(Comm), hash)
    }

    #[inline]
    pub fn zero(&self, tag: Tag) -> Ptr {
        self.intern_atom(tag, F::ZERO)
    }

    pub fn is_zero(&self, ptr: &Ptr) -> bool {
        match ptr {
            Ptr::Atom(_, idx) => self.fetch_f(*idx) == Some(&F::ZERO),
            _ => false,
        }
    }

    #[inline]
    pub fn dummy(&self) -> Ptr {
        self.zero(Tag::Expr(Nil))
    }

    /// Creates an atom pointer from a `ZPtr`, with its tag and hash. Thus hashing
    /// such pointer will result on the same original `ZPtr`
    #[inline]
    pub fn opaque(&self, z_ptr: ZPtr<F>) -> Ptr {
        let crate::z_data::z_ptr::ZPtr(t, h) = z_ptr;
        self.intern_atom(t, h)
    }

    pub fn intern_string(&self, s: &str) -> Ptr {
        if let Some(ptr) = self.string_ptr_cache.get(s) {
            *ptr
        } else {
            let ptr = s.chars().rev().fold(self.zero(Tag::Expr(Str)), |acc, c| {
                self.intern_2_ptrs(Tag::Expr(Str), self.char(c), acc)
            });
            self.string_ptr_cache.insert(s.to_string(), Box::new(ptr));
            self.ptr_string_cache.insert(ptr, s.to_string());
            ptr
        }
    }

    pub fn fetch_string(&self, ptr: &Ptr) -> Option<String> {
        if let Some(str) = self.ptr_string_cache.get(ptr) {
            Some(str.to_string())
        } else {
            let mut string = String::new();
            let mut ptr = *ptr;
            loop {
                match ptr {
                    Ptr::Atom(Tag::Expr(Str), idx) => {
                        if self.fetch_f(idx)? == &F::ZERO {
                            self.ptr_string_cache.insert(ptr, string.clone());
                            return Some(string);
                        } else {
                            return None;
                        }
                    }
                    Ptr::Tuple2(Tag::Expr(Str), idx) => {
                        let (car, cdr) = self.fetch_2_ptrs(idx)?;
                        match car {
                            Ptr::Atom(Tag::Expr(Char), idx) => {
                                let f = self.fetch_f(*idx)?;
                                string.push(f.to_char().expect("malformed char pointer"));
                                ptr = *cdr
                            }
                            _ => return None,
                        }
                    }
                    _ => return None,
                }
            }
        }
    }

    pub fn intern_symbol_path(&self, path: &[String]) -> Ptr {
        path.iter().fold(self.zero(Tag::Expr(Sym)), |acc, s| {
            let s_ptr = self.intern_string(s);
            self.intern_2_ptrs(Tag::Expr(Sym), s_ptr, acc)
        })
    }

    pub fn intern_symbol(&self, sym: &Symbol) -> Ptr {
        if let Some(ptr) = self.symbol_ptr_cache.get(sym) {
            *ptr
        } else {
            let path_ptr = self.intern_symbol_path(sym.path());
            let sym_ptr = if sym == &lurk_sym("nil") {
                path_ptr.cast(Tag::Expr(Nil))
            } else if sym.is_keyword() {
                path_ptr.cast(Tag::Expr(Key))
            } else {
                path_ptr
            };
            self.symbol_ptr_cache.insert(sym.clone(), Box::new(sym_ptr));
            self.ptr_symbol_cache.insert(sym_ptr, Box::new(sym.clone()));
            sym_ptr
        }
    }

    /// Fetches a symbol path whose interning returned the provided `idx`
    fn fetch_symbol_path(&self, mut idx: usize) -> Option<Vec<String>> {
        let mut path = vec![];
        loop {
            let (car, cdr) = self.fetch_2_ptrs(idx)?;
            let string = self.fetch_string(car)?;
            path.push(string);
            match cdr {
                Ptr::Atom(Tag::Expr(Sym), idx) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        path.reverse();
                        return Some(path);
                    } else {
                        return None;
                    }
                }
                Ptr::Tuple2(Tag::Expr(Sym), idx_cdr) => idx = *idx_cdr,
                _ => return None,
            }
        }
    }

    pub fn fetch_symbol(&self, ptr: &Ptr) -> Option<Symbol> {
        if let Some(sym) = self.ptr_symbol_cache.get(ptr) {
            Some(sym.clone())
        } else {
            match ptr {
                Ptr::Atom(Tag::Expr(Sym), idx) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        let sym = Symbol::root_sym();
                        self.ptr_symbol_cache.insert(*ptr, Box::new(sym.clone()));
                        Some(sym)
                    } else {
                        None
                    }
                }
                Ptr::Atom(Tag::Expr(Key), idx) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        let key = Symbol::root_key();
                        self.ptr_symbol_cache.insert(*ptr, Box::new(key.clone()));
                        Some(key)
                    } else {
                        None
                    }
                }
                Ptr::Tuple2(Tag::Expr(Sym | Nil), idx) => {
                    let path = self.fetch_symbol_path(*idx)?;
                    let sym = Symbol::sym_from_vec(path);
                    self.ptr_symbol_cache.insert(*ptr, Box::new(sym.clone()));
                    Some(sym)
                }
                Ptr::Tuple2(Tag::Expr(Key), idx) => {
                    let path = self.fetch_symbol_path(*idx)?;
                    let key = Symbol::key_from_vec(path);
                    self.ptr_symbol_cache.insert(*ptr, Box::new(key.clone()));
                    Some(key)
                }
                _ => None,
            }
        }
    }

    pub fn fetch_sym(&self, ptr: &Ptr) -> Option<Symbol> {
        if ptr.tag() == &Tag::Expr(Sym) {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    pub fn fetch_key(&self, ptr: &Ptr) -> Option<Symbol> {
        if ptr.tag() == &Tag::Expr(Key) {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    #[inline]
    pub fn add_comm(&self, hash: F, secret: F, payload: Ptr) {
        self.comms
            .insert(FWrap::<F>(hash), Box::new((secret, payload)));
    }

    #[inline]
    pub fn hide(&self, secret: F, payload: Ptr) -> Ptr {
        self.comm(self.hide_and_return_z_payload(secret, payload).0)
    }

    pub fn hide_and_return_z_payload(&self, secret: F, payload: Ptr) -> (F, ZPtr<F>) {
        let z_ptr = self.hash_ptr(&payload);
        let hash = self
            .poseidon_cache
            .hash3(&[secret, z_ptr.tag_field(), *z_ptr.value()]);
        self.add_comm(hash, secret, payload);
        (hash, z_ptr)
    }

    #[inline]
    pub fn commit(&self, payload: Ptr) -> Ptr {
        self.hide(F::NON_HIDING_COMMITMENT_SECRET, payload)
    }

    #[inline]
    pub fn open(&self, hash: F) -> Option<&(F, Ptr)> {
        self.comms.get(&FWrap(hash))
    }

    #[inline]
    pub fn intern_lurk_symbol(&self, name: &str) -> Ptr {
        self.intern_symbol(&lurk_sym(name))
    }

    #[inline]
    pub fn intern_nil(&self) -> Ptr {
        self.intern_lurk_symbol("nil")
    }

    #[inline]
    pub fn intern_user_symbol(&self, name: &str) -> Ptr {
        self.intern_symbol(&user_sym(name))
    }

    #[inline]
    pub fn key(&self, name: &str) -> Ptr {
        self.intern_symbol(&Symbol::key(&[name.to_string()]))
    }

    #[inline]
    pub fn cons(&self, car: Ptr, cdr: Ptr) -> Ptr {
        self.intern_2_ptrs(Tag::Expr(Cons), car, cdr)
    }

    #[inline]
    pub fn intern_fun(&self, arg: Ptr, body: Ptr, env: Ptr) -> Ptr {
        self.intern_3_ptrs(Tag::Expr(Fun), arg, body, env)
    }

    #[inline]
    pub fn cont_outermost(&self) -> Ptr {
        Ptr::Atom(Tag::Cont(Outermost), self.hash8zeros_idx)
    }

    #[inline]
    pub fn cont_error(&self) -> Ptr {
        Ptr::Atom(Tag::Cont(ContTag::Error), self.hash8zeros_idx)
    }

    #[inline]
    pub fn cont_terminal(&self) -> Ptr {
        Ptr::Atom(Tag::Cont(Terminal), self.hash8zeros_idx)
    }

    pub fn car_cdr(&self, ptr: &Ptr) -> Result<(Ptr, Ptr)> {
        match ptr.tag() {
            Tag::Expr(Nil) => {
                let nil = self.intern_nil();
                Ok((nil, nil))
            }
            Tag::Expr(Cons) => {
                let Some(idx) = ptr.get_index2() else {
                    bail!("malformed cons pointer")
                };
                match self.fetch_2_ptrs(idx) {
                    Some(res) => Ok(*res),
                    None => bail!("car/cdr not found"),
                }
            }
            Tag::Expr(Str) => {
                if self.is_zero(ptr) {
                    Ok((self.intern_nil(), self.zero(Tag::Expr(Str))))
                } else {
                    let Some(idx) = ptr.get_index2() else {
                        bail!("malformed str pointer")
                    };
                    match self.fetch_2_ptrs(idx) {
                        Some(res) => Ok(*res),
                        None => bail!("car/cdr not found"),
                    }
                }
            }
            _ => bail!("invalid pointer to extract car/cdr from"),
        }
    }

    /// Interns a sequence of pointers as a cons-list. The terminating element
    /// defaults to `nil` if `last` is `None`
    fn intern_list(&self, elts: Vec<Ptr>, last: Option<Ptr>) -> Ptr {
        elts.into_iter()
            .rev()
            .fold(last.unwrap_or_else(|| self.intern_nil()), |acc, elt| {
                self.intern_2_ptrs(Tag::Expr(Cons), elt, acc)
            })
    }

    /// Interns a sequence of pointers as a proper (`nil`-terminated) cons-list
    #[inline]
    pub fn list(&self, elts: Vec<Ptr>) -> Ptr {
        self.intern_list(elts, None)
    }

    /// Interns a sequence of pointers as an improper cons-list whose last
    /// element is `last`
    #[inline]
    pub fn improper_list(&self, elts: Vec<Ptr>, last: Ptr) -> Ptr {
        self.intern_list(elts, Some(last))
    }

    /// Fetches a cons list that was interned. If the list is improper, the second
    /// element of the returned pair will carry the improper terminating value
    pub fn fetch_list(&self, ptr: &Ptr) -> Option<(Vec<Ptr>, Option<Ptr>)> {
        match ptr {
            Ptr::Tuple2(Tag::Expr(Nil), _) => Some((vec![], None)),
            Ptr::Tuple2(Tag::Expr(Cons), mut idx) => {
                let mut list = vec![];
                let mut last = None;
                while let Some((car, cdr)) = self.fetch_2_ptrs(idx) {
                    list.push(*car);
                    match cdr.tag() {
                        Tag::Expr(Nil) => break,
                        Tag::Expr(Cons) => {
                            idx = cdr.get_index2()?;
                        }
                        _ => {
                            last = Some(*cdr);
                            break;
                        }
                    }
                }
                Some((list, last))
            }
            _ => None,
        }
    }

    pub fn intern_syntax(&self, syn: Syntax<F>) -> Ptr {
        match syn {
            Syntax::Num(_, x) => self.num(x.into_scalar()),
            Syntax::UInt(_, x) => self.u64(x.into()),
            Syntax::Char(_, x) => self.char(x),
            Syntax::Symbol(_, x) => self.intern_symbol(&x),
            Syntax::String(_, x) => self.intern_string(&x),
            Syntax::Quote(_, x) => self.list(vec![
                self.intern_symbol(&lurk_sym("quote")),
                self.intern_syntax(*x),
            ]),
            Syntax::List(_, xs) => {
                self.list(xs.into_iter().map(|x| self.intern_syntax(x)).collect())
            }
            Syntax::Improper(_, xs, y) => self.improper_list(
                xs.into_iter().map(|x| self.intern_syntax(x)).collect(),
                self.intern_syntax(*y),
            ),
        }
    }

    pub fn read(&self, state: Rc<RefCell<State>>, input: &str) -> Result<Ptr> {
        match preceded(
            syntax::parse_space,
            syntax::parse_syntax(state, false, false),
        )
        .parse(Span::new(input))
        {
            Ok((_, x)) => Ok(self.intern_syntax(x)),
            Err(e) => bail!("{}", e),
        }
    }

    pub fn read_maybe_meta<'a>(
        &self,
        state: Rc<RefCell<State>>,
        input: &'a str,
    ) -> Result<(usize, Span<'a>, Ptr, bool), Error> {
        match preceded(syntax::parse_space, syntax::parse_maybe_meta(state, false))
            .parse(input.into())
        {
            Ok((i, Some((is_meta, x)))) => {
                let from_offset = x
                    .get_pos()
                    .get_from_offset()
                    .expect("Parsed syntax should have its Pos set");
                Ok((from_offset, i, self.intern_syntax(x), is_meta))
            }
            Ok((_, None)) => Err(Error::NoInput),
            Err(e) => Err(Error::Syntax(format!("{}", e))),
        }
    }

    #[inline]
    pub fn read_with_default_state(&self, input: &str) -> Result<Ptr> {
        self.read(State::init_lurk_state().rccell(), input)
    }

    #[inline]
    pub fn expect_f(&self, idx: usize) -> &F {
        self.fetch_f(idx).expect("Index missing from f_elts")
    }

    #[inline]
    pub fn expect_2_ptrs(&self, idx: usize) -> &(Ptr, Ptr) {
        self.fetch_2_ptrs(idx).expect("Index missing from tuple2")
    }

    #[inline]
    pub fn expect_3_ptrs(&self, idx: usize) -> &(Ptr, Ptr, Ptr) {
        self.fetch_3_ptrs(idx).expect("Index missing from tuple3")
    }

    #[inline]
    pub fn expect_4_ptrs(&self, idx: usize) -> &(Ptr, Ptr, Ptr, Ptr) {
        self.fetch_4_ptrs(idx).expect("Index missing from tuple4")
    }

    /// Recursively hashes the children of a `Ptr` in order to obtain its
    /// corresponding `ZPtr`. While traversing a `Ptr` tree, it consults the
    /// cache of `Ptr`s that have already been hydrated and also populates this
    /// cache for the new `Ptr`s.
    ///
    /// Warning: without cache hits, this function might blow up Rust's recursion
    /// depth limit. This limitation is circumvented by calling `hydrate_z_cache`
    /// beforehand or by using `hash_ptr` instead, which is slightly slower.
    fn hash_ptr_unsafe(&self, ptr: &Ptr) -> ZPtr<F> {
        match ptr {
            Ptr::Atom(tag, idx) => {
                if let Some(z_ptr) = self.z_cache.get(ptr) {
                    *z_ptr
                } else {
                    let z_ptr = ZPtr::from_parts(*tag, *self.expect_f(*idx));
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    self.inverse_z_cache.insert(z_ptr, Box::new(*ptr));
                    z_ptr
                }
            }
            Ptr::Tuple2(tag, idx) => {
                if let Some(z_ptr) = self.z_cache.get(ptr) {
                    *z_ptr
                } else {
                    let (a, b) = self.expect_2_ptrs(*idx);
                    let a = self.hash_ptr_unsafe(a);
                    let b = self.hash_ptr_unsafe(b);
                    let z_ptr = ZPtr::from_parts(
                        *tag,
                        self.poseidon_cache.hash4(&[
                            a.tag_field(),
                            *a.value(),
                            b.tag_field(),
                            *b.value(),
                        ]),
                    );
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    self.inverse_z_cache.insert(z_ptr, Box::new(*ptr));
                    z_ptr
                }
            }
            Ptr::Tuple3(tag, idx) => {
                if let Some(z_ptr) = self.z_cache.get(ptr) {
                    *z_ptr
                } else {
                    let (a, b, c) = self.expect_3_ptrs(*idx);
                    let a = self.hash_ptr_unsafe(a);
                    let b = self.hash_ptr_unsafe(b);
                    let c = self.hash_ptr_unsafe(c);
                    let z_ptr = ZPtr::from_parts(
                        *tag,
                        self.poseidon_cache.hash6(&[
                            a.tag_field(),
                            *a.value(),
                            b.tag_field(),
                            *b.value(),
                            c.tag_field(),
                            *c.value(),
                        ]),
                    );
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    self.inverse_z_cache.insert(z_ptr, Box::new(*ptr));
                    z_ptr
                }
            }
            Ptr::Tuple4(tag, idx) => {
                if let Some(z_ptr) = self.z_cache.get(ptr) {
                    *z_ptr
                } else {
                    let (a, b, c, d) = self.expect_4_ptrs(*idx);
                    let a = self.hash_ptr_unsafe(a);
                    let b = self.hash_ptr_unsafe(b);
                    let c = self.hash_ptr_unsafe(c);
                    let d = self.hash_ptr_unsafe(d);
                    let z_ptr = ZPtr::from_parts(
                        *tag,
                        self.poseidon_cache.hash8(&[
                            a.tag_field(),
                            *a.value(),
                            b.tag_field(),
                            *b.value(),
                            c.tag_field(),
                            *c.value(),
                            d.tag_field(),
                            *d.value(),
                        ]),
                    );
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    self.inverse_z_cache.insert(z_ptr, Box::new(*ptr));
                    z_ptr
                }
            }
        }
    }

    /// Hashes pointers in parallel, consuming chunks of length 256, which is a
    /// reasonably safe limit. The danger of longer chunks is that the rightmost
    /// pointers are the ones which are more likely to reach the recursion depth
    /// limit in `hash_ptr_unsafe`. So we move in smaller chunks from left to
    /// right, populating the `z_cache`, which can rescue `hash_ptr_unsafe` from
    /// dangerously deep recursions
    fn hydrate_z_cache_with_ptrs(&self, ptrs: &[&Ptr]) {
        ptrs.chunks(256).for_each(|chunk| {
            chunk.par_iter().for_each(|ptr| {
                self.hash_ptr_unsafe(ptr);
            });
        });
    }

    /// Hashes enqueued `Ptr` trees from the bottom to the top, avoiding deep
    /// recursions in `hash_ptr`. Resets the `dehydrated` queue afterwards.
    pub fn hydrate_z_cache(&self) {
        self.hydrate_z_cache_with_ptrs(&self.dehydrated.load().iter().collect::<Vec<_>>());
        self.dehydrated.swap(Arc::new(FrozenVec::default()));
    }

    /// Whether the length of the dehydrated queue is within the safe limit.
    /// Note: these values are experimental and may be machine dependant.
    #[inline]
    fn is_below_safe_threshold(&self) -> bool {
        if cfg!(debug_assertions) {
            // not release mode
            self.dehydrated.load().len() < 443
        } else {
            // release mode
            self.dehydrated.load().len() < 2497
        }
    }

    /// Safe version of `hash_ptr_unsafe` that doesn't hit a stack overflow by
    /// precomputing the pointers that need to be hashed in order to hash the
    /// provided `ptr`
    pub fn hash_ptr(&self, ptr: &Ptr) -> ZPtr<F> {
        if self.is_below_safe_threshold() {
            // just run `hash_ptr_unsafe` for extra speed when the dehydrated
            // queue is small enough
            return self.hash_ptr_unsafe(ptr);
        }
        let mut ptrs: IndexSet<&Ptr> = IndexSet::default();
        let mut stack = vec![ptr];
        macro_rules! feed_loop {
            ($x:expr) => {
                if $x.is_tuple() {
                    if self.z_cache.get($x).is_none() {
                        if ptrs.insert($x) {
                            stack.push($x);
                        }
                    }
                }
            };
        }
        while let Some(ptr) = stack.pop() {
            match ptr {
                Ptr::Atom(..) => (),
                Ptr::Tuple2(_, idx) => {
                    let (a, b) = self.expect_2_ptrs(*idx);
                    for ptr in [a, b] {
                        feed_loop!(ptr)
                    }
                }
                Ptr::Tuple3(_, idx) => {
                    let (a, b, c) = self.expect_3_ptrs(*idx);
                    for ptr in [a, b, c] {
                        feed_loop!(ptr)
                    }
                }
                Ptr::Tuple4(_, idx) => {
                    let (a, b, c, d) = self.expect_4_ptrs(*idx);
                    for ptr in [a, b, c, d] {
                        feed_loop!(ptr)
                    }
                }
            }
        }
        ptrs.reverse();
        self.hydrate_z_cache_with_ptrs(&ptrs.into_iter().collect::<Vec<_>>());
        // Now it's okay to call `hash_ptr_unsafe`
        self.hash_ptr_unsafe(ptr)
    }

    /// Constructs a vector of scalars that correspond to tags and hashes computed
    /// from a slice of `Ptr`s turned into `ZPtr`s
    pub fn to_scalar_vector(&self, ptrs: &[Ptr]) -> Vec<F> {
        ptrs.iter()
            .fold(Vec::with_capacity(2 * ptrs.len()), |mut acc, ptr| {
                let z_ptr = self.hash_ptr(ptr);
                acc.push(z_ptr.tag_field());
                acc.push(*z_ptr.value());
                acc
            })
    }

    /// Equality of the content-addressed versions of two pointers
    #[inline]
    pub fn ptr_eq(&self, a: &Ptr, b: &Ptr) -> bool {
        self.hash_ptr(a) == self.hash_ptr(b)
    }

    /// Attempts to recover the `Ptr` that corresponds to `z_ptr` from
    /// `inverse_z_cache`. If the mapping is not there, returns an atom pointer
    /// with the same tag and value
    #[inline]
    pub fn to_ptr(&self, z_ptr: &ZPtr<F>) -> Ptr {
        self.inverse_z_cache
            .get(z_ptr)
            .cloned()
            .unwrap_or_else(|| self.opaque(*z_ptr))
    }
}

impl Ptr {
    pub fn fmt_to_string<F: LurkField>(&self, store: &Store<F>, state: &State) -> String {
        match self.tag() {
            Tag::Expr(t) => match t {
                Nil => {
                    if let Some(sym) = store.fetch_symbol(self) {
                        state.fmt_to_string(&sym.into())
                    } else {
                        "<Opaque Nil>".into()
                    }
                }
                Sym => {
                    if let Some(sym) = store.fetch_sym(self) {
                        state.fmt_to_string(&sym.into())
                    } else {
                        "<Opaque Sym>".into()
                    }
                }
                Key => {
                    if let Some(key) = store.fetch_key(self) {
                        state.fmt_to_string(&key.into())
                    } else {
                        "<Opaque Key>".into()
                    }
                }
                Str => {
                    if let Some(str) = store.fetch_string(self) {
                        format!("\"{str}\"")
                    } else {
                        "<Opaque Str>".into()
                    }
                }
                Char => {
                    if let Some(c) = self
                        .get_atom()
                        .map(|idx| store.expect_f(idx))
                        .and_then(F::to_char)
                    {
                        format!("\'{c}\'")
                    } else {
                        "<Malformed Char>".into()
                    }
                }
                Cons => {
                    if let Some((list, non_nil)) = store.fetch_list(self) {
                        let list = list
                            .iter()
                            .map(|p| p.fmt_to_string(store, state))
                            .collect::<Vec<_>>();
                        if let Some(non_nil) = non_nil {
                            format!(
                                "({} . {})",
                                list.join(" "),
                                non_nil.fmt_to_string(store, state)
                            )
                        } else {
                            format!("({})", list.join(" "))
                        }
                    } else {
                        "<Opaque Cons>".into()
                    }
                }
                Num => {
                    if let Some(f) = self.get_atom().map(|idx| store.expect_f(idx)) {
                        if let Some(u) = f.to_u64() {
                            u.to_string()
                        } else {
                            format!("0x{}", f.hex_digits())
                        }
                    } else {
                        "<Malformed Num>".into()
                    }
                }
                U64 => {
                    if let Some(u) = self
                        .get_atom()
                        .map(|idx| store.expect_f(idx))
                        .and_then(F::to_u64)
                    {
                        format!("{u}u64")
                    } else {
                        "<Malformed U64>".into()
                    }
                }
                Fun => match self.get_index3() {
                    None => "<Malformed Fun>".into(),
                    Some(idx) => {
                        if let Some((arg, bod, _)) = store.fetch_3_ptrs(idx) {
                            match bod.tag() {
                                Tag::Expr(Nil) => {
                                    format!(
                                        "<FUNCTION ({}) {}>",
                                        arg.fmt_to_string(store, state),
                                        bod.fmt_to_string(store, state)
                                    )
                                }
                                Tag::Expr(Cons) => {
                                    if let Some(idx) = bod.get_index2() {
                                        if let Some((bod, _)) = store.fetch_2_ptrs(idx) {
                                            format!(
                                                "<FUNCTION ({}) {}>",
                                                arg.fmt_to_string(store, state),
                                                bod.fmt_to_string(store, state)
                                            )
                                        } else {
                                            "<Opaque Fun>".into()
                                        }
                                    } else {
                                        "<Malformed Fun>".into()
                                    }
                                }
                                _ => "<Malformed Fun>".into(),
                            }
                        } else {
                            "<Opaque Fun>".into()
                        }
                    }
                },
                Thunk => match self.get_index2() {
                    None => "<Malformed Thunk>".into(),
                    Some(idx) => {
                        if let Some((val, cont)) = store.fetch_2_ptrs(idx) {
                            format!(
                                "Thunk{{ value: {} => cont: {} }}",
                                val.fmt_to_string(store, state),
                                cont.fmt_to_string(store, state)
                            )
                        } else {
                            "<Opaque Thunk>".into()
                        }
                    }
                },
                Comm => match self.get_atom() {
                    Some(idx) => {
                        let f = store.expect_f(idx);
                        if store.comms.get(&FWrap(*f)).is_some() {
                            format!("(comm 0x{})", f.hex_digits())
                        } else {
                            format!("<Opaque Comm 0x{}>", f.hex_digits())
                        }
                    }
                    None => "<Malformed Comm>".into(),
                },
                Cproc => match self.get_index2() {
                    None => "<Malformed Cproc>".into(),
                    Some(idx) => {
                        if let Some((cproc_name, args)) = store.fetch_2_ptrs(idx) {
                            format!(
                                "<COPROC {} {}>",
                                cproc_name.fmt_to_string(store, state),
                                args.fmt_to_string(store, state)
                            )
                        } else {
                            "<Opaque Cproc>".into()
                        }
                    }
                },
            },
            Tag::Cont(t) => match t {
                Outermost => "Outermost".into(),
                Dummy => "Dummy".into(),
                ContTag::Error => "Error".into(),
                Terminal => "Terminal".into(),
                Call0 => self.fmt_cont2_to_string("Call0", "saved_env", store, state),
                Call => {
                    self.fmt_cont3_to_string("Call", ("unevaled_arg", "saved_env"), store, state)
                }
                Call2 => self.fmt_cont3_to_string("Call2", ("function", "saved_env"), store, state),
                Tail => self.fmt_cont2_to_string("Tail", "saved_env", store, state),
                Lookup => self.fmt_cont2_to_string("Lookup", "saved_env", store, state),
                Unop => self.fmt_cont2_to_string("Unop", "saved_env", store, state),
                Binop => self.fmt_cont4_to_string(
                    "Binop",
                    ("operator", "saved_env", "unevaled_args"),
                    store,
                    state,
                ),
                Binop2 => {
                    self.fmt_cont3_to_string("Binop2", ("operator", "evaled_arg"), store, state)
                }
                If => self.fmt_cont2_to_string("If", "unevaled_args", store, state),
                Let => self.fmt_cont4_to_string("Let", ("var", "saved_env", "body"), store, state),
                LetRec => {
                    self.fmt_cont4_to_string("LetRec", ("var", "saved_env", "body"), store, state)
                }
                Emit => "Emit <CONTINUATION>".into(),
                ContTag::Cproc => self.fmt_cont4_to_string(
                    "Cproc",
                    ("name", "unevaled_args", "evaled_args"),
                    store,
                    state,
                ),
            },
            Tag::Op1(op) => op.to_string(),
            Tag::Op2(op) => op.to_string(),
        }
    }

    fn fmt_cont2_to_string<F: LurkField>(
        &self,
        name: &str,
        field: &str,
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.get_index4() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some((a, cont, ..)) = store.fetch_4_ptrs(idx) {
                    format!(
                        "{name}{{ {field}: {}, continuation: {} }}",
                        a.fmt_to_string(store, state),
                        cont.fmt_to_string(store, state)
                    )
                } else {
                    format!("<Opaque {name}>")
                }
            }
        }
    }

    fn fmt_cont3_to_string<F: LurkField>(
        &self,
        name: &str,
        fields: (&str, &str),
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.get_index4() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some((a, b, cont, _)) = store.fetch_4_ptrs(idx) {
                    let (fa, fb) = fields;
                    format!(
                        "{name}{{ {fa}: {}, {fb}: {}, continuation: {} }}",
                        a.fmt_to_string(store, state),
                        b.fmt_to_string(store, state),
                        cont.fmt_to_string(store, state)
                    )
                } else {
                    format!("<Opaque {name}>")
                }
            }
        }
    }

    fn fmt_cont4_to_string<F: LurkField>(
        &self,
        name: &str,
        fields: (&str, &str, &str),
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.get_index4() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some((a, b, c, cont)) = store.fetch_4_ptrs(idx) {
                    let (fa, fb, fc) = fields;
                    format!(
                        "{name}{{ {fa}: {}, {fb}: {}, {fc}: {}, continuation: {} }}",
                        a.fmt_to_string(store, state),
                        b.fmt_to_string(store, state),
                        c.fmt_to_string(store, state),
                        cont.fmt_to_string(store, state)
                    )
                } else {
                    format!("<Opaque {name}>")
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use pasta_curves::pallas::Scalar as Fr;
    use proptest::prelude::*;

    use crate::{
        field::LurkField,
        lem::Tag,
        parser::position::Pos,
        state::{initial_lurk_state, lurk_sym},
        syntax::Syntax,
        tag::{ExprTag, Tag as TagTrait},
        Num, Symbol,
    };

    use super::{Ptr, Store};

    #[test]
    fn test_car_cdr() {
        let store = Store::<Fr>::default();

        // empty list
        let nil = store.intern_nil();
        let (car, cdr) = store.car_cdr(&nil).unwrap();
        assert_eq!((&car, &cdr), (&nil, &nil));

        // regular cons
        let one = store.num_u64(1);
        let a = store.char('a');
        let one_a = store.cons(one, a);
        let (car, cdr) = store.car_cdr(&one_a).unwrap();
        assert_eq!((&one, &a), (&car, &cdr));

        // string
        let abc = store.intern_string("abc");
        let bc = store.intern_string("bc");
        let (car, cdr) = store.car_cdr(&abc).unwrap();
        assert_eq!((&a, &bc), (&car, &cdr));

        // empty string
        let empty_str = store.intern_string("");
        let (car, cdr) = store.car_cdr(&empty_str).unwrap();
        assert_eq!((&nil, &empty_str), (&car, &cdr));
    }

    #[test]
    fn test_list() {
        let store = Store::<Fr>::default();
        let state = initial_lurk_state();

        // empty list
        let list = store.list(vec![]);
        let nil = store.intern_nil();
        assert_eq!(&list, &nil);
        let (elts, non_nil) = store.fetch_list(&list).unwrap();
        assert!(elts.is_empty());
        assert!(non_nil.is_none());

        // proper list
        let a = store.char('a');
        let b = store.char('b');
        let list = store.list(vec![a, b]);
        assert_eq!(list.fmt_to_string(&store, state), "('a' 'b')");
        let (elts, non_nil) = store.fetch_list(&list).unwrap();
        assert_eq!(elts.len(), 2);
        assert_eq!((&elts[0], &elts[1]), (&a, &b));
        assert!(non_nil.is_none());

        // improper list
        let c = store.char('c');
        let b_c = store.cons(b, c);
        let a_b_c = store.cons(a, b_c);
        let a_b_c_ = store.improper_list(vec![a, b], c);
        assert_eq!(a_b_c, a_b_c_);
        assert_eq!(a_b_c.fmt_to_string(&store, state), "('a' 'b' . 'c')");
        let (elts, non_nil) = store.fetch_list(&a_b_c).unwrap();
        assert_eq!(elts.len(), 2);
        assert_eq!((&elts[0], &elts[1]), (&a, &b));
        assert_eq!(non_nil, Some(c));
    }

    #[test]
    fn test_basic_hashing() {
        let store = Store::<Fr>::default();
        let zero = Fr::zero();
        let zero_tag = Tag::try_from(0).unwrap();
        let foo = store.intern_atom(zero_tag, zero);

        let z_foo = store.hash_ptr(&foo);
        assert_eq!(z_foo.tag(), &zero_tag);
        assert_eq!(z_foo.value(), &zero);

        let comm = store.hide(zero, foo);
        assert_eq!(comm.tag(), &Tag::Expr(ExprTag::Comm));
        assert_eq!(
            store.expect_f(comm.get_atom().unwrap()),
            &store.poseidon_cache.hash3(&[zero; 3])
        );

        let ptr2 = store.intern_2_ptrs(zero_tag, foo, foo);
        let z_ptr2 = store.hash_ptr(&ptr2);
        assert_eq!(z_ptr2.tag(), &zero_tag);
        assert_eq!(z_ptr2.value(), &store.poseidon_cache.hash4(&[zero; 4]));

        let ptr3 = store.intern_3_ptrs(zero_tag, foo, foo, foo);
        let z_ptr3 = store.hash_ptr(&ptr3);
        assert_eq!(z_ptr3.tag(), &zero_tag);
        assert_eq!(z_ptr3.value(), &store.poseidon_cache.hash6(&[zero; 6]));

        let ptr4 = store.intern_4_ptrs(zero_tag, foo, foo, foo, foo);
        let z_ptr4 = store.hash_ptr(&ptr4);
        assert_eq!(z_ptr4.tag(), &zero_tag);
        assert_eq!(z_ptr4.value(), &store.poseidon_cache.hash8(&[zero; 8]));
    }

    #[test]
    fn test_display_opaque_knowledge() {
        // bob creates a list
        let store = Store::<Fr>::default();
        let one = store.num_u64(1);
        let two = store.num_u64(2);
        let one_two = store.cons(one, two);
        let hi = store.intern_string("hi");
        let z1 = store.hash_ptr(&hi);
        let z2 = store.hash_ptr(&one_two);
        let list = store.list(vec![one_two, hi]);
        let z_list = store.hash_ptr(&list);

        // alice uses the hashed elements of the list to show that she
        // can produce the same hash as the original z_list
        let store = Store::<Fr>::default();
        let a1 = store.opaque(z1);
        let a2 = store.opaque(z2);
        let list1 = store.list(vec![a1, a2]);
        let list2 = store.list(vec![a2, a1]);
        let z_list1 = store.hash_ptr(&list1);
        let z_list2 = store.hash_ptr(&list2);

        // one of those lists should match the original
        assert!(z_list == z_list1 || z_list == z_list2);
    }

    #[test]
    fn test_ptr_hashing_safety() {
        let string = String::from_utf8(vec![b'0'; 4096]).unwrap();
        let store = Store::<Fr>::default();
        let ptr = store.intern_string(&string);
        // `hash_ptr_unsafe` would overflow the stack, whereas `hash_ptr` works
        let x = store.hash_ptr(&ptr);

        let store = Store::<Fr>::default();
        let ptr = store.intern_string(&string);
        store.hydrate_z_cache();
        // but `hash_ptr_unsafe` works just fine after manual hydration
        let y = store.hash_ptr_unsafe(&ptr);

        // and, of course, those functions result on the same `ZPtr`
        assert_eq!(x, y);
    }

    #[test]
    fn string_hashing() {
        let s = &Store::<Fr>::default();
        let hi_ptr = s.intern_string("hi");

        let hi_hash_manual = s.poseidon_cache.hash4(&[
            ExprTag::Char.to_field(),
            Fr::from_char('h'),
            ExprTag::Str.to_field(),
            s.poseidon_cache.hash4(&[
                ExprTag::Char.to_field(),
                Fr::from_char('i'),
                ExprTag::Str.to_field(),
                Fr::ZERO,
            ]),
        ]);

        let hi_hash = s.hash_ptr(&hi_ptr).1;
        assert_eq!(hi_hash, hi_hash_manual);
    }

    #[test]
    fn symbol_hashing() {
        let s = &Store::<Fr>::default();
        let foo_ptr = s.intern_string("foo");
        let bar_ptr = s.intern_string("bar");
        let foo_bar_ptr = s.intern_symbol(&Symbol::sym_from_vec(vec!["foo".into(), "bar".into()]));

        let foo_z_ptr = s.hash_ptr(&foo_ptr);
        let bar_z_ptr = s.hash_ptr(&bar_ptr);

        let foo_bar_hash_manual = s.poseidon_cache.hash4(&[
            ExprTag::Str.to_field(),
            bar_z_ptr.1,
            ExprTag::Sym.to_field(),
            s.poseidon_cache.hash4(&[
                ExprTag::Str.to_field(),
                foo_z_ptr.1,
                ExprTag::Sym.to_field(),
                Fr::ZERO,
            ]),
        ]);

        let foo_bar_hash = s.hash_ptr(&foo_bar_ptr).1;
        assert_eq!(foo_bar_hash, foo_bar_hash_manual);
    }

    // helper function to test syntax interning roundtrip
    fn fetch_syntax(ptr: Ptr, store: &Store<Fr>) -> Syntax<Fr> {
        match ptr {
            Ptr::Atom(Tag::Expr(ExprTag::Num), idx) => {
                Syntax::Num(Pos::No, Num::Scalar(*store.expect_f(idx)))
            }
            Ptr::Atom(Tag::Expr(ExprTag::Char), idx) => {
                Syntax::Char(Pos::No, store.expect_f(idx).to_char().unwrap())
            }
            Ptr::Atom(Tag::Expr(ExprTag::U64), idx) => Syntax::UInt(
                Pos::No,
                crate::UInt::U64(store.expect_f(idx).to_u64_unchecked()),
            ),
            Ptr::Atom(Tag::Expr(ExprTag::Sym | ExprTag::Key), _)
            | Ptr::Tuple2(Tag::Expr(ExprTag::Sym | ExprTag::Key), _) => {
                Syntax::Symbol(Pos::No, store.fetch_symbol(&ptr).unwrap().into())
            }
            Ptr::Atom(Tag::Expr(ExprTag::Str), _) | Ptr::Tuple2(Tag::Expr(ExprTag::Str), _) => {
                Syntax::String(Pos::No, store.fetch_string(&ptr).unwrap())
            }
            Ptr::Tuple2(Tag::Expr(ExprTag::Cons), _) => {
                let (elts, last) = store.fetch_list(&ptr).unwrap();
                let elts = elts
                    .into_iter()
                    .map(|e| fetch_syntax(e, store))
                    .collect::<Vec<_>>();
                if let Some(last) = last {
                    Syntax::Improper(Pos::No, elts, fetch_syntax(last, store).into())
                } else {
                    Syntax::List(Pos::No, elts)
                }
            }
            Ptr::Tuple2(Tag::Expr(ExprTag::Nil), _) => {
                Syntax::Symbol(Pos::No, lurk_sym("nil").into())
            }
            _ => unreachable!(),
        }
    }

    proptest! {
        #[test]
        fn syntax_roundtrip(x in any::<Syntax<Fr>>()) {
            let store = Store::<Fr>::default();
            let ptr1 = store.intern_syntax(x);
            let y = fetch_syntax(ptr1, &store);
            let ptr2 = store.intern_syntax(y);
            assert_eq!(ptr1, ptr2);
        }
    }
}
