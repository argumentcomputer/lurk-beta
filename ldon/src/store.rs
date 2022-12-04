use crate::expr::{Cont, Expr};
use crate::parser::position::Pos;
use crate::ptr::Ptr;
use crate::syntax::Syn;
use lurk_ff::field::LurkField;
use lurk_ff::tag::{ExprTag, TagKind};
use std::collections::BTreeMap;
use std::fmt;

use crate::hash::PoseidonCache;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Store<F: LurkField>(BTreeMap<Ptr<F>, Entry<F>>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Entry<F: LurkField> {
    Expr(Expr<F>),
    Cont(Cont<F>),
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StoreError<F: LurkField> {
    UnknownPtr(Ptr<F>),
    UnexpectedEntry(Ptr<F>, Entry<F>, &'static str),
    ExpectedChar(Ptr<F>),
    ExpectedU64(Ptr<F>),
    ExpectedString(Ptr<F>),
    ExpectedSymbol(Ptr<F>),
    ExpectedMap(Ptr<F>),
    ExpectedLink(Ptr<F>),
    Custom(&'static str),
}

impl<'a, F: LurkField> Store<F> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern_expr(&mut self, cache: &PoseidonCache<F>, expr: Expr<F>) -> Ptr<F> {
        let ptr = expr.ptr(cache);
        if !ptr.is_immediate() {
            self.0.insert(ptr, Entry::Expr(expr));
        }
        ptr
    }

    pub fn intern_string(&mut self, cache: &PoseidonCache<F>, string: &String) -> Ptr<F> {
        let mut ptr = self.intern_expr(cache, Expr::StrNil);

        for c in string.chars().rev() {
            let char_ptr = Ptr {
                tag: F::make_expr_tag(ExprTag::Char),
                val: F::from_char(c),
            };
            ptr = self.intern_expr(cache, Expr::StrCons(char_ptr, ptr));
        }
        ptr
    }

    pub fn intern_symbol(&mut self, cache: &PoseidonCache<F>, strs: &Vec<String>) -> Ptr<F> {
        let mut ptr = self.intern_expr(cache, Expr::SymNil);

        for s in strs {
            let str_ptr = self.intern_string(&cache, s);
            ptr = self.intern_expr(cache, Expr::SymCons(str_ptr, ptr));
        }
        ptr
    }

    pub fn intern_keyword(&mut self, cache: &PoseidonCache<F>, strs: &Vec<String>) -> Ptr<F> {
        let sym_ptr = self.intern_symbol(cache, strs);
        self.intern_expr(cache, Expr::Keyword(sym_ptr))
    }

    pub fn intern_list(
        &mut self,
        cache: &PoseidonCache<F>,
        xs: &Vec<Syn<F>>,
        end: &Option<Box<Syn<F>>>,
    ) -> Ptr<F> {
        if let (Some(end), true) = (end, xs.is_empty()) {
            let nil_ptr = self.intern_expr(cache, Expr::ConsNil);
            let end_ptr = self.intern_syn(cache, &end);
            return self.intern_expr(cache, Expr::Cons(nil_ptr, end_ptr));
        }
        let mut ptr = match end {
            Some(end) => self.intern_syn(cache, &end),
            None => self.intern_expr(cache, Expr::ConsNil),
        };
        for x in xs.iter().rev() {
            let head_ptr = self.intern_syn(cache, x);
            ptr = self.intern_expr(cache, Expr::Cons(head_ptr, ptr));
        }
        ptr
    }

    pub fn intern_map(&mut self, cache: &PoseidonCache<F>, xs: &Vec<(Syn<F>, Syn<F>)>) -> Ptr<F> {
        let mut ptr = self.intern_expr(cache, Expr::ConsNil);
        for (k, v) in xs.iter().rev() {
            let key_ptr = self.intern_syn(cache, k);
            let val_ptr = self.intern_syn(cache, v);
            let head_ptr = self.intern_expr(cache, Expr::Cons(key_ptr, val_ptr));
            ptr = self.intern_expr(cache, Expr::Cons(head_ptr, ptr));
        }
        self.intern_expr(cache, Expr::Map(ptr))
    }

    pub fn intern_link(
        &mut self,
        cache: &PoseidonCache<F>,
        ctx: &Box<Syn<F>>,
        val: &Vec<u64>,
    ) -> Ptr<F> {
        let ctx_ptr = self.intern_syn(cache, ctx);
        let val_ptr = self.intern_list(
            cache,
            &val.iter().map(|x| Syn::U64(Pos::No, *x)).collect(),
            &None,
        );
        self.intern_expr(cache, Expr::Link(ctx_ptr, val_ptr))
    }

    pub fn intern_syn(&mut self, cache: &PoseidonCache<F>, syn: &Syn<F>) -> Ptr<F> {
        match syn {
            Syn::Num(_, f) => self.intern_expr(cache, Expr::Num(*f)),
            Syn::Char(_, c) => self.intern_expr(cache, Expr::Char(F::from_char(*c))),
            Syn::U64(_, x) => self.intern_expr(cache, Expr::U64((*x).into())),
            Syn::String(_, s) => self.intern_string(cache, &s),
            Syn::Symbol(_, sym) => self.intern_symbol(cache, sym),
            Syn::Keyword(_, sym) => self.intern_keyword(cache, sym),
            Syn::List(_, xs, end) => self.intern_list(cache, xs, end),
            Syn::Map(_, map) => self.intern_map(cache, map),
            Syn::Link(_, ctx, val) => self.intern_link(cache, ctx, val),
        }
    }

    pub fn get_entry(&self, ptr: Ptr<F>) -> Result<Entry<F>, StoreError<F>> {
        if let Some(entry) = ptr.immediate() {
            Ok(entry)
        } else {
            let entry = self
                .0
                .get(&ptr)
                .ok_or_else(|| StoreError::UnknownPtr(ptr))?;
            Ok(entry.clone())
        }
    }

    pub fn get_expr(&self, ptr: Ptr<F>) -> Result<Expr<F>, StoreError<F>> {
        match self.get_entry(ptr)? {
            Entry::Expr(x) => Ok(x),
            Entry::Cont(x) => Err(StoreError::UnexpectedEntry(ptr, Entry::Cont(x), "Expr")),
            Entry::Opaque => Err(StoreError::UnexpectedEntry(ptr, Entry::Opaque, "Expr")),
        }
    }

    pub fn get_cont(&self, ptr: Ptr<F>) -> Result<Cont<F>, StoreError<F>> {
        match self.get_entry(ptr)? {
            Entry::Cont(x) => Ok(x),
            Entry::Expr(x) => Err(StoreError::UnexpectedEntry(ptr, Entry::Expr(x), "Cont")),
            Entry::Opaque => Err(StoreError::UnexpectedEntry(ptr, Entry::Opaque, "Cont")),
        }
    }

    pub fn get_opaque(&self, ptr: Ptr<F>) -> Result<(), StoreError<F>> {
        match self.get_entry(ptr)? {
            Entry::Cont(x) => Err(StoreError::UnexpectedEntry(ptr, Entry::Cont(x), "Opaque")),
            Entry::Expr(x) => Err(StoreError::UnexpectedEntry(ptr, Entry::Expr(x), "Opaque")),
            Entry::Opaque => Ok(()),
        }
    }

    pub fn get_syn_list(&self, ptr: Ptr<F>) -> Result<Syn<F>, StoreError<F>> {
        let mut list = vec![];
        let mut ptr = ptr;

        while let Expr::Cons(car, cdr) = self.get_expr(ptr)? {
            list.push(self.get_syn(car)?);
            ptr = cdr;
        }
        if let Expr::ConsNil = self.get_expr(ptr)? {
            Ok(Syn::List(Pos::No, list, None))
        } else {
            Ok(Syn::List(Pos::No, list, Some(Box::new(self.get_syn(ptr)?))))
        }
    }
    pub fn get_u64(&self, ptr: Ptr<F>) -> Result<u64, StoreError<F>> {
        if let Expr::U64(f) = self.get_expr(ptr)? {
            let x = F::to_u64(&f).ok_or_else(|| StoreError::ExpectedU64(ptr))?;
            Ok(x)
        } else {
            Err(StoreError::ExpectedU64(ptr))
        }
    }

    pub fn get_char(&self, ptr: Ptr<F>) -> Result<char, StoreError<F>> {
        if let Expr::Char(f) = self.get_expr(ptr)? {
            let c = F::to_char(&f).ok_or_else(|| StoreError::ExpectedChar(ptr))?;
            Ok(c)
        } else {
            Err(StoreError::ExpectedChar(ptr))
        }
    }

    pub fn get_string(&self, ptr: Ptr<F>) -> Result<String, StoreError<F>> {
        let mut s = String::new();
        let mut next = ptr;

        while let Expr::StrCons(car, cdr) = self.get_expr(next)? {
            s.push(self.get_char(car)?);
            next = cdr;
        }
        if let Expr::StrNil = self.get_expr(next)? {
            Ok(s)
        } else {
            Err(StoreError::ExpectedString(ptr))
        }
    }

    pub fn get_symbol(&self, ptr: Ptr<F>) -> Result<Vec<String>, StoreError<F>> {
        let mut list = vec![];
        let mut next = ptr;

        while let Expr::SymCons(car, cdr) = self.get_expr(next)? {
            list.push(self.get_string(car)?);
            next = cdr;
        }
        if let Expr::SymNil = self.get_expr(next)? {
            Ok(list.into_iter().rev().collect())
        } else {
            Err(StoreError::ExpectedSymbol(ptr))
        }
    }
    pub fn get_map(&self, ptr: Ptr<F>) -> Result<Vec<(Syn<F>, Syn<F>)>, StoreError<F>> {
        let mut assoc = vec![];
        let mut next = ptr;

        while let Expr::Cons(entry, cdr) = self.get_expr(next)? {
            if let Expr::Cons(key, val) = self.get_expr(entry)? {
                assoc.push((self.get_syn(key)?, self.get_syn(val)?));
                next = cdr;
            } else {
                return Err(StoreError::ExpectedMap(ptr));
            }
        }
        Ok(assoc)
    }

    pub fn get_syn(&self, ptr: Ptr<F>) -> Result<Syn<F>, StoreError<F>> {
        let expr = self.get_expr(ptr)?;
        match expr {
            Expr::ConsNil => Ok(Syn::List(Pos::No, vec![], None)),
            Expr::SymNil => Ok(Syn::Symbol(Pos::No, vec![])),
            Expr::StrNil => Ok(Syn::String(Pos::No, "".to_string())),
            Expr::Num(f) => Ok(Syn::Num(Pos::No, f)),
            Expr::Char(_) => Ok(Syn::Char(Pos::No, self.get_char(ptr)?)),
            Expr::U64(_) => Ok(Syn::U64(Pos::No, self.get_u64(ptr)?)),
            Expr::Cons(_, _) => self.get_syn_list(ptr),
            Expr::StrCons(_, _) => Ok(Syn::String(Pos::No, self.get_string(ptr)?)),
            Expr::SymCons(_, _) => Ok(Syn::Symbol(Pos::No, self.get_symbol(ptr)?)),
            Expr::Keyword(sym) => Ok(Syn::Keyword(Pos::No, self.get_symbol(sym)?)),
            Expr::Map(map) => Ok(Syn::Map(Pos::No, self.get_map(map)?)),
            _ => todo!(),
            //Expr::Comm(F, Ptr<F>),             // secret, val
            //Expr::Thunk(Ptr<F>, Ptr<F>),       // val, cont
            //Expr::Fun(Ptr<F>, Ptr<F>, Ptr<F>), // arg, body, env
        }
    }
}

impl<'a, F: LurkField> fmt::Display for Store<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        for (k, v) in self.0.iter() {
            match v {
                Entry::Expr(x) => {
                    writeln!(f, "  {}: {:?},", k, x)?;
                }
                Entry::Cont(x) => {
                    writeln!(f, "  {}: {:?},", k, x)?;
                }
                Entry::Opaque => {
                    writeln!(f, "  {}: _,", k)?;
                }
            }
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use blstrs::Scalar as Fr;

    use quickcheck::{Arbitrary, Gen};

    use crate::test::frequency;
    use im::Vector;

    #[test]
    fn unit_expr_store_get() {
        let mut store = Store::<Fr>::default();
        let cache = PoseidonCache::default();

        let mut test = |expr1| {
            let ptr = store.intern_expr(&cache, expr1);
            let expr2 = store.get_expr(ptr).unwrap();
            assert!(expr1 == expr2);
            ptr
        };

        test(Expr::Num(0u64.into()));
        test(Expr::U64(0u64.into()));
        let a = test(Expr::Char(97u64.into()));
        test(Expr::SymNil);
        let nil = test(Expr::ConsNil);
        let str_nil = test(Expr::StrNil);
        test(Expr::Cons(nil, nil));
        test(Expr::StrCons(a, str_nil));
    }

    #[test]
    fn unit_syn_store_get() {
        let mut store = Store::<Fr>::default();
        let cache = PoseidonCache::default();

        let mut test = |syn1| {
            let ptr = store.intern_syn(&cache, &syn1);
            if let Ok(syn2) = store.get_syn(ptr) {
                println!("{:?}", syn1);
                println!("{:?}", syn2);
                assert!(syn1 == syn2);
                ptr
            } else {
                println!("{:?}", store.get_syn(ptr));
                println!("{}", store);
                assert!(false);
                ptr
            }
        };

        test(Syn::Num(Pos::No, 0u64.into()));
        test(Syn::U64(Pos::No, 0u64.into()));
        test(Syn::Char(Pos::No, 'a'));
        test(Syn::String(Pos::No, "foo".to_string()));
        test(Syn::List(
            Pos::No,
            vec![Syn::Num(Pos::No, 0u64.into())],
            None,
        ));
        test(Syn::List(
            Pos::No,
            vec![Syn::Num(Pos::No, 0u64.into())],
            Some(Box::new(Syn::Num(Pos::No, 0u64.into()))),
        ));
        test(Syn::Symbol(Pos::No, vec![]));
        test(Syn::Symbol(Pos::No, vec!["foo".to_string()]));
        test(Syn::Symbol(
            Pos::No,
            vec!["foo".to_string(), "bar".to_string()],
        ));
    }

    #[quickcheck]
    fn prop_syn_store_get(syn1: Syn<Fr>) -> bool {
        let mut store1 = Store::<Fr>::default();
        let cache = PoseidonCache::default();
        let ptr1 = store1.intern_syn(&cache, &syn1);
        let syn2 = store1.get_syn(ptr1).unwrap();
        println!("{:?}", syn1);
        println!("{:?}", syn2);
        syn1 == syn2
    }
}
