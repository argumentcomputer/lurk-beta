use std::collections::BTreeMap;
use std::fmt;

use crate::field::LurkField;

use crate::store::{
    ContTag, Op1, Op2, Pointer, Ptr, ScalarContPtr, ScalarPointer, ScalarPtr, Store, Tag,
};
use crate::Num;
use serde::Deserialize;
use serde::Serialize;

/// `ScalarStore` allows realization of a graph of `ScalarPtr`s suitable for serialization to IPLD. `ScalarExpression`s
/// are composed only of `ScalarPtr`s, so `scalar_map` suffices to allow traverseing an arbitrary DAG.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScalarStore<F: LurkField> {
    scalar_map: BTreeMap<ScalarPtr<F>, ScalarExpression<F>>,
    scalar_cont_map: BTreeMap<ScalarContPtr<F>, ScalarContinuation<F>>,
}

impl<'a, F: LurkField> fmt::Display for ScalarStore<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        for (k, v) in self.scalar_map.iter() {
            writeln!(f, "  {}: {},", k, v)?;
        }
        for (k, v) in self.scalar_cont_map.iter() {
            writeln!(f, "  {:?}: {:?}", k, v)?;
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}

impl<'a, F: LurkField> ScalarStore<F> {
    pub fn new_with_root(store: &Store<F>, root: &Ptr<F>) -> Option<(Self, ScalarPtr<F>)> {
        let mut scalar_store = Self::default();
        let mut scalars = Vec::new();

        let root_scalar = store.get_expr_hash(root)?;
        scalars.push(root_scalar);

        // TODO: Ensure the store is actually a DAG so this doesn't loop
        while let Some(scalar) = scalars.pop() {
            let ptr = store.scalar_ptr_map.get(&scalar)?;
            let scalar_expr = ScalarStore::<F>::expr_from_ptr(store, &ptr)?;
            if !scalar_store.scalar_map.contains_key(&scalar) {
                let child_scalars = ScalarStore::<F>::child_scalars(&scalar_expr);
                scalars.extend(child_scalars);
                scalar_store.scalar_map.insert(scalar, scalar_expr);
            }
        }

        Some((scalar_store, root_scalar))
    }

    fn child_scalars(scalar_expression: &ScalarExpression<F>) -> Vec<ScalarPtr<F>> {
        match scalar_expression {
            ScalarExpression::Cons(car, cdr) => [*car, *cdr].into(),
            ScalarExpression::Comm(_, payload) => [*payload].into(),
            ScalarExpression::Sym(_str) => [*_str].into(),
            ScalarExpression::Fun(arg, body, closed_env) => [*arg, *body, *closed_env].into(),
            ScalarExpression::Num(_) => vec![],
            ScalarExpression::Str(_str) => [*_str].into(),
            ScalarExpression::StrNil => vec![],
            ScalarExpression::StrCons(_, tail) => [*tail].into(),
            ScalarExpression::Thunk(_) => vec![],
            ScalarExpression::Char(_) => vec![],
        }
    }

    fn expr_from_ptr(store: &Store<F>, ptr: &Ptr<F>) -> Option<ScalarExpression<F>> {
        match ptr.tag() {
            Tag::Nil => {
                let hash = store.hash_string("NIL");
                Some(ScalarExpression::Sym(ScalarPtr::from_parts(
                    Tag::Str.as_field(),
                    hash,
                )))
            }
            Tag::Cons => store.fetch_cons(ptr).and_then(|(car, cdr)| {
                store.get_expr_hash(car).and_then(|car| {
                    store
                        .get_expr_hash(cdr)
                        .map(|cdr| ScalarExpression::Cons(car, cdr))
                })
            }),
            Tag::Comm => store.fetch_comm(ptr).and_then(|(secret, payload)| {
                store
                    .get_expr_hash(payload)
                    .map(|payload| ScalarExpression::Comm(secret.0, payload))
            }),
            Tag::Sym => {
                let scalar_ptr = store.get_hash_sym(*ptr)?;
                Some(ScalarExpression::Sym(ScalarPtr::from_parts(
                    Tag::StrCons.as_field(),
                    *scalar_ptr.value(),
                )))
            }
            Tag::Str => {
                let scalar_ptr = store.get_hash_sym(*ptr)?;
                Some(ScalarExpression::Str(ScalarPtr::from_parts(
                    Tag::StrCons.as_field(),
                    *scalar_ptr.value(),
                )))
            }
            Tag::Fun => store.fetch_fun(ptr).and_then(|(arg, body, closed_env)| {
                store.get_expr_hash(arg).and_then(|arg| {
                    store.get_expr_hash(body).and_then(|body| {
                        store
                            .get_expr_hash(closed_env)
                            .map(|closed_env| ScalarExpression::Fun(arg, body, closed_env))
                    })
                })
            }),
            Tag::Num => store.fetch_num(ptr).map(|num| match num {
                Num::U64(x) => ScalarExpression::Num((*x).into()),
                Num::Scalar(x) => ScalarExpression::Num(*x),
            }),
            Tag::StrNil => Some(ScalarExpression::StrNil),
            Tag::StrCons => {
                let string = store.fetch_str(ptr)?;
                if string.is_empty() {
                    Some(ScalarExpression::StrNil)
                } else {
                    let head: char = string.chars().nth(0)?;
                    let tail = &string[1..];
                    let tail_hash = store.hash_string(tail);
                    Some(ScalarExpression::StrCons(
                        ScalarPtr::from_parts(Tag::Char.as_field(), (head as u64).into()),
                        ScalarPtr::from_parts(Tag::Str.as_field(), tail_hash),
                    ))
                }
            }
            Tag::Char => store
                .fetch_char(ptr)
                .map(|x| ScalarExpression::Char((x as u64).into())),
            Tag::Thunk => unimplemented!(),
        }
    }

    pub fn get_expr(&self, ptr: &ScalarPtr<F>) -> Option<&ScalarExpression<F>> {
        self.scalar_map.get(ptr)
    }

    pub fn get_cont(&self, ptr: &ScalarContPtr<F>) -> Option<&ScalarContinuation<F>> {
        self.scalar_cont_map.get(ptr)
    }

    pub fn to_store_with_expr(&mut self, ptr: &ScalarPtr<F>) -> Option<(Store<F>, Ptr<F>)> {
        let mut store = Store::new();

        let ptr = store.intern_scalar_ptr(*ptr, self)?;

        for scalar_ptr in self.scalar_map.keys() {
            store.intern_scalar_ptr(*scalar_ptr, self);
        }
        for ptr in self.scalar_cont_map.keys() {
            store.intern_scalar_cont_ptr(*ptr, self);
        }
        Some((store, ptr))
    }
    pub fn to_store(&mut self) -> Option<Store<F>> {
        let mut store = Store::new();

        for ptr in self.scalar_map.keys() {
            store.intern_scalar_ptr(*ptr, self);
        }
        for ptr in self.scalar_cont_map.keys() {
            store.intern_scalar_cont_ptr(*ptr, self);
        }
        Some(store)
    }

    pub fn get_str_tails(&self, ptr: ScalarPtr<F>) -> Option<Vec<(char, ScalarPtr<F>)>> {
        let mut vec = Vec::new();
        let mut ptr = ptr;
        while ptr != ScalarPtr::from_parts(Tag::Str.as_field(), F::zero()) {
            let (head, tail) = self.scalar_map.get(&ptr).and_then(|x| match x {
                ScalarExpression::StrCons(head, tail) => Some((head, tail)),
                _ => None,
            })?;
            let chr = self.scalar_map.get(&head).and_then(|x| match x {
                ScalarExpression::Char(f) => f.to_char(),
                _ => None,
            })?;
            vec.push((chr, *tail));
            ptr = *tail;
        }
        Some(vec)
    }
    pub fn get_str(&self, ptr: ScalarPtr<F>) -> Option<String> {
        let s: String = self
            .get_str_tails(ptr)?
            .into_iter()
            .map(|(x, _)| x)
            .collect();
        Some(s)
    }

    pub fn ser_f(self) -> Vec<F> {
        let mut res = Vec::new();
        for (ptr, expr) in self.scalar_map {
            res.push(*ptr.tag());
            res.push(*ptr.value());
            res.extend(expr.ser_f().into_iter());
        }
        for (ptr, cont) in self.scalar_cont_map {
            res.push(*ptr.tag());
            res.push(*ptr.value());
            res.extend(cont.ser_f().into_iter());
        }
        res
    }
    pub fn de_f(stream: &Vec<F>) -> Result<Self, ()> {
        let mut idx: usize = 0;
        let len = stream.len();
        let mut scalar_map: BTreeMap<ScalarPtr<F>, ScalarExpression<F>> = BTreeMap::new();
        let mut scalar_cont_map: BTreeMap<ScalarContPtr<F>, ScalarContinuation<F>> =
            BTreeMap::new();

        while idx < len {
            if let Some(tag) = Tag::from_field(stream[idx]) {
                let value = stream[idx + 1];
                let ptr = ScalarPtr::from_parts(tag.as_field(), value);
                let (idx2, expr) = ScalarExpression::de_f(stream, idx + 2, tag, value)?;
                scalar_map.insert(ptr, expr);
                idx = idx2
            }
            if let Some(cont_tag) = ContTag::from_field(stream[idx]) {
                let value = stream[idx + 1];
                let ptr = ScalarContPtr::from_parts(cont_tag.as_field(), value);
                let (idx2, expr) = ScalarContinuation::de_f(stream, idx + 2, cont_tag, value)?;
                scalar_cont_map.insert(ptr, expr);
                idx = idx2
            } else {
                return Err(());
            }
        }
        Ok(ScalarStore {
            scalar_map,
            scalar_cont_map,
        })
    }
}

impl<'a, F: LurkField> ScalarExpression<F> {
    pub fn ser_f(self) -> Vec<F> {
        match self {
            // TODO: replace F::zero() with the actual hash of Str("nil")
            ScalarExpression::Cons(car, cdr) => {
                vec![*car.tag(), *car.value(), *cdr.tag(), *cdr.value()]
            }
            ScalarExpression::Comm(a, b) => {
                vec![a, *b.tag(), *b.value()]
            }
            ScalarExpression::Sym(string) => vec![*string.tag(), *string.value()],
            ScalarExpression::Fun(arg, body, closed_env) => {
                vec![
                    *arg.tag(),
                    *arg.value(),
                    *body.tag(),
                    *body.value(),
                    *closed_env.tag(),
                    *closed_env.value(),
                ]
            }
            ScalarExpression::Str(string) => vec![*string.tag(), *string.value()],
            ScalarExpression::StrCons(head, tail) => {
                vec![*head.tag(), *head.value(), *tail.tag(), *tail.value()]
            }
            ScalarExpression::Thunk(thunk) => {
                vec![
                    *thunk.value.tag(),
                    *thunk.value.value(),
                    *thunk.continuation.tag(),
                    *thunk.continuation.value(),
                ]
            }
            ScalarExpression::Char(_) => vec![],
            ScalarExpression::Num(_) => vec![],
            ScalarExpression::StrNil => vec![],
        }
    }
    // (<tag>,<val>, (<values>)*)*
    pub fn de_f(
        stream: &Vec<F>,
        idx: usize,
        tag: Tag,
        val: F,
    ) -> Result<(usize, ScalarExpression<F>), ()> {
        match tag {
            Tag::Nil => {
                let s = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                Ok((idx + 2, ScalarExpression::Sym(s)))
            }
            Tag::Cons => {
                let car = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let cdr = ScalarPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                Ok((idx + 4, ScalarExpression::Cons(car, cdr)))
            }
            Tag::Sym => {
                let s = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                Ok((idx + 2, ScalarExpression::Sym(s)))
            }
            Tag::Comm => {
                let a = stream[idx];
                let b = ScalarPtr::from_parts(stream[idx + 1], stream[idx + 2]);
                Ok((idx + 3, ScalarExpression::Comm(a, b)))
            }
            Tag::Fun => {
                let arg = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let body = ScalarPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                let closed_env = ScalarPtr::from_parts(stream[idx + 4], stream[idx + 5]);
                Ok((idx + 6, ScalarExpression::Fun(arg, body, closed_env)))
            }
            Tag::Str => {
                let s = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                Ok((idx + 2, ScalarExpression::Str(s)))
            }
            Tag::StrCons => {
                let head = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let tail = ScalarPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                Ok((idx + 4, ScalarExpression::StrCons(head, tail)))
            }
            Tag::StrNil => Ok((idx, ScalarExpression::StrNil)),
            Tag::Thunk => {
                let value = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                Ok((
                    idx + 4,
                    ScalarExpression::Thunk(ScalarThunk {
                        value,
                        continuation,
                    }),
                ))
            }
            Tag::Char => Ok((idx, ScalarExpression::Char(val))),
            Tag::Num => Ok((idx, ScalarExpression::Num(val))),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ScalarExpression<F: LurkField> {
    Cons(ScalarPtr<F>, ScalarPtr<F>),
    Comm(F, ScalarPtr<F>),
    Sym(ScalarPtr<F>),
    Fun(ScalarPtr<F>, ScalarPtr<F>, ScalarPtr<F>),
    Num(F),
    Str(ScalarPtr<F>),
    StrCons(ScalarPtr<F>, ScalarPtr<F>),
    StrNil,
    Thunk(ScalarThunk<F>),
    Char(F),
}

impl<'a, F: LurkField> fmt::Display for ScalarExpression<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cons(x, y) => write!(f, "Cons({}, {})", x, y),
            Self::Comm(x, y) => write!(f, "Comm({:?}, {})", x, y),
            Self::Sym(x) => write!(f, "Sym({})", x),
            Self::Fun(x, y, z) => write!(f, "Fun({}, {}, {})", x, y, z),
            Self::Num(x) => {
                if let Some(x) = x.to_u64() {
                    write!(f, "Num({})", x)
                } else {
                    write!(f, "Num({:?})", x)
                }
            }
            Self::Char(x) => {
                if let Some(x) = x.to_char() {
                    write!(f, "Char('{}')", x)
                } else {
                    write!(f, "Char({:?})", x)
                }
            }
            Self::Str(x) => write!(f, "Str({})", x),
            Self::StrCons(x, y) => write!(f, "StrCons({}, {})", x, y),
            Self::StrNil => write!(f, "StrNil"),
            Self::Thunk(x) => write!(f, "Thunk({:?})", x),
        }
    }
}

impl<'a, F: LurkField> Default for ScalarExpression<F> {
    fn default() -> Self {
        Self::StrNil
    }
}

// Unused for now, but will be needed when we serialize Thunks to IPLD.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScalarThunk<F: LurkField> {
    pub(crate) value: ScalarPtr<F>,
    pub(crate) continuation: ScalarContPtr<F>,
}

impl<F: LurkField> Copy for ScalarThunk<F> {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ScalarContinuation<F: LurkField> {
    Outermost,
    Call {
        unevaled_arg: ScalarPtr<F>,
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Call2 {
        function: ScalarPtr<F>,
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Tail {
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Error,
    Lookup {
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Unop {
        operator: Op1,
        continuation: ScalarContPtr<F>,
    },
    Binop {
        operator: Op2,
        saved_env: ScalarPtr<F>,
        unevaled_args: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Binop2 {
        operator: Op2,
        evaled_arg: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    If {
        unevaled_args: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Let {
        var: ScalarPtr<F>,
        body: ScalarPtr<F>,
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    LetRec {
        var: ScalarPtr<F>,
        body: ScalarPtr<F>,
        saved_env: ScalarPtr<F>,
        continuation: ScalarContPtr<F>,
    },
    Emit {
        continuation: ScalarContPtr<F>,
    },
    Dummy,
    Terminal,
}

impl<F: LurkField> ScalarContinuation<F> {
    pub fn ser_f(self) -> Vec<F> {
        match self {
            ScalarContinuation::Outermost => todo!(),
            ScalarContinuation::Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => {
                vec![
                    *unevaled_arg.tag(),
                    *unevaled_arg.value(),
                    *saved_env.tag(),
                    *saved_env.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::Call2 {
                function,
                saved_env,
                continuation,
            } => {
                vec![
                    *function.tag(),
                    *function.value(),
                    *saved_env.tag(),
                    *saved_env.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::Tail {
                saved_env,
                continuation,
            } => {
                vec![
                    *saved_env.tag(),
                    *saved_env.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::Error => todo!(),
            ScalarContinuation::Lookup {
                saved_env,
                continuation,
            } => {
                vec![
                    *saved_env.tag(),
                    *saved_env.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::Unop {
                operator,
                continuation,
            } => {
                vec![
                    operator.as_field(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => {
                vec![
                    operator.as_field(),
                    *saved_env.tag(),
                    *saved_env.value(),
                    *unevaled_args.tag(),
                    *unevaled_args.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => {
                vec![
                    operator.as_field(),
                    *evaled_arg.tag(),
                    *evaled_arg.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::If {
                unevaled_args,
                continuation,
            } => {
                vec![
                    *unevaled_args.tag(),
                    *unevaled_args.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::Let {
                var,
                body,
                saved_env,
                continuation,
            } => {
                vec![
                    *var.tag(),
                    *var.value(),
                    *body.tag(),
                    *body.value(),
                    *saved_env.tag(),
                    *saved_env.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::LetRec {
                var,
                body,
                saved_env,
                continuation,
            } => {
                vec![
                    *var.tag(),
                    *var.value(),
                    *body.tag(),
                    *body.value(),
                    *saved_env.tag(),
                    *saved_env.value(),
                    *continuation.tag(),
                    *continuation.value(),
                ]
            }
            ScalarContinuation::Emit { continuation } => {
                vec![*continuation.tag(), *continuation.value()]
            }
            ScalarContinuation::Dummy => todo!(),
            ScalarContinuation::Terminal => todo!(),
        }
    }
    pub fn de_f(
        stream: &Vec<F>,
        idx: usize,
        tag: ContTag,
        _val: F,
    ) -> Result<(usize, ScalarContinuation<F>), ()> {
        match tag {
            ContTag::Outermost => todo!(),
            ContTag::Call0 => todo!(),
            ContTag::Call => {
                let unevaled_arg = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let saved_env = ScalarPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 4], stream[idx + 5]);
                Ok((
                    idx + 6,
                    ScalarContinuation::Call {
                        unevaled_arg,
                        saved_env,
                        continuation,
                    },
                ))
            }
            ContTag::Call2 => {
                let function = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let saved_env = ScalarPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 4], stream[idx + 5]);
                Ok((
                    idx + 6,
                    ScalarContinuation::Call2 {
                        function,
                        saved_env,
                        continuation,
                    },
                ))
            }
            ContTag::Tail => {
                let saved_env = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                Ok((
                    idx + 4,
                    ScalarContinuation::Tail {
                        saved_env,
                        continuation,
                    },
                ))
            }
            ContTag::Lookup => {
                let saved_env = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                Ok((
                    idx + 4,
                    ScalarContinuation::Lookup {
                        saved_env,
                        continuation,
                    },
                ))
            }
            ContTag::Unop => {
                let operator = Op1::from_field(stream[idx]).map_or_else(|| Err(()), Ok)?;
                let continuation = ScalarContPtr::from_parts(stream[idx + 1], stream[idx + 2]);
                Ok((
                    idx + 3,
                    ScalarContinuation::Unop {
                        operator,
                        continuation,
                    },
                ))
            }
            ContTag::Binop => {
                let operator = Op2::from_field(stream[idx]).map_or_else(|| Err(()), Ok)?;
                let saved_env = ScalarPtr::from_parts(stream[idx + 1], stream[idx + 2]);
                let unevaled_args = ScalarPtr::from_parts(stream[idx + 3], stream[idx + 4]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 5], stream[idx + 6]);
                Ok((
                    idx + 7,
                    ScalarContinuation::Binop {
                        operator,
                        saved_env,
                        unevaled_args,
                        continuation,
                    },
                ))
            }
            ContTag::Binop2 => {
                let operator = Op2::from_field(stream[idx]).map_or_else(|| Err(()), Ok)?;
                let evaled_arg = ScalarPtr::from_parts(stream[idx + 1], stream[idx + 2]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 3], stream[idx + 4]);
                Ok((
                    idx + 5,
                    ScalarContinuation::Binop2 {
                        operator,
                        evaled_arg,
                        continuation,
                    },
                ))
            }
            ContTag::If => {
                let unevaled_args = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                Ok((
                    idx + 4,
                    ScalarContinuation::If {
                        unevaled_args,
                        continuation,
                    },
                ))
            }
            ContTag::Let => {
                let var = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let body = ScalarPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                let saved_env = ScalarPtr::from_parts(stream[idx + 4], stream[idx + 5]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 6], stream[idx + 7]);
                Ok((
                    idx + 8,
                    ScalarContinuation::Let {
                        var,
                        body,
                        saved_env,
                        continuation,
                    },
                ))
            }
            ContTag::LetRec => {
                let var = ScalarPtr::from_parts(stream[idx], stream[idx + 1]);
                let body = ScalarPtr::from_parts(stream[idx + 2], stream[idx + 3]);
                let saved_env = ScalarPtr::from_parts(stream[idx + 4], stream[idx + 5]);
                let continuation = ScalarContPtr::from_parts(stream[idx + 6], stream[idx + 7]);
                Ok((
                    idx + 8,
                    ScalarContinuation::LetRec {
                        var,
                        body,
                        saved_env,
                        continuation,
                    },
                ))
            }
            ContTag::Emit => {
                let continuation = ScalarContPtr::from_parts(stream[idx], stream[idx + 1]);
                Ok((idx + 1, ScalarContinuation::Emit { continuation }))
            }
            ContTag::Dummy => todo!(),
            ContTag::Terminal => todo!(),

            _ => Err(()),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::eval::empty_sym_env;
    use crate::field::FWrap;
    use crate::store::ScalarPointer;
    use blstrs::Scalar as Fr;

    use quickcheck::{Arbitrary, Gen};

    use crate::test::frequency;

    use libipld::serde::from_ipld;
    use libipld::serde::to_ipld;

    impl Arbitrary for ScalarThunk<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            ScalarThunk {
                value: Arbitrary::arbitrary(g),
                continuation: Arbitrary::arbitrary(g),
            }
        }
    }

    #[quickcheck]
    fn prop_scalar_thunk_ipld(x: ScalarThunk<Fr>) -> bool {
        if let Ok(ipld) = to_ipld(x) {
            if let Ok(y) = from_ipld(ipld) {
                x == y
            } else {
                false
            }
        } else {
            false
        }
    }

    impl Arbitrary for ScalarExpression<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> ScalarExpression<Fr>>)> = vec![
                (100, Box::new(|_| Self::StrNil)),
                (
                    100,
                    Box::new(|g| Self::Cons(ScalarPtr::arbitrary(g), ScalarPtr::arbitrary(g))),
                ),
                //(100, Box::new(|g| Self::Sym(String::arbitrary(g)))),
                //(100, Box::new(|g| Self::Str(String::arbitrary(g)))),
                (
                    100,
                    Box::new(|g| {
                        let f = FWrap::arbitrary(g);
                        Self::Num(f.0)
                    }),
                ),
                (
                    100,
                    Box::new(|g| {
                        Self::Fun(
                            ScalarPtr::arbitrary(g),
                            ScalarPtr::arbitrary(g),
                            ScalarPtr::arbitrary(g),
                        )
                    }),
                ),
                (100, Box::new(|g| Self::Thunk(ScalarThunk::arbitrary(g)))),
            ];
            frequency(g, input)
        }
    }

    impl Arbitrary for ScalarContinuation<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> ScalarContinuation<Fr>>)> = vec![
                (100, Box::new(|_| Self::Outermost)),
                (
                    100,
                    Box::new(|g| Self::Call {
                        unevaled_arg: ScalarPtr::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Call2 {
                        function: ScalarPtr::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Tail {
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (100, Box::new(|_| Self::Error)),
                (
                    100,
                    Box::new(|g| Self::Lookup {
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Unop {
                        operator: Op1::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Binop {
                        operator: Op2::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        unevaled_args: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Binop2 {
                        operator: Op2::arbitrary(g),
                        evaled_arg: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::If {
                        unevaled_args: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::Let {
                        var: ScalarPtr::arbitrary(g),
                        body: ScalarPtr::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (
                    100,
                    Box::new(|g| Self::LetRec {
                        var: ScalarPtr::arbitrary(g),
                        saved_env: ScalarPtr::arbitrary(g),
                        body: ScalarPtr::arbitrary(g),
                        continuation: ScalarContPtr::arbitrary(g),
                    }),
                ),
                (100, Box::new(|_| Self::Dummy)),
                (100, Box::new(|_| Self::Terminal)),
            ];
            frequency(g, input)
        }
    }

    #[quickcheck]
    fn prop_scalar_expression_ipld(x: ScalarExpression<Fr>) -> bool {
        match to_ipld(x.clone()) {
            Ok(ipld) => match from_ipld(ipld.clone()) {
                Ok(y) => {
                    println!("x: {:?}", x);
                    println!("y: {:?}", y);
                    x == y
                }
                Err(e) => {
                    println!("ser x: {:?}", x);
                    println!("de ipld: {:?}", ipld);
                    println!("err e: {:?}", e);
                    false
                }
            },
            Err(e) => {
                println!("ser x: {:?}", x);
                println!("err e: {:?}", e);
                false
            }
        }
    }

    #[quickcheck]
    fn prop_scalar_continuation_ipld(x: ScalarExpression<Fr>) -> bool {
        if let Ok(ipld) = to_ipld(x.clone()) {
            if let Ok(y) = from_ipld(ipld) {
                x == y
            } else {
                false
            }
        } else {
            false
        }
    }

    // This doesn't create well-defined ScalarStores, so is only useful for
    // testing ipld
    impl Arbitrary for ScalarStore<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            let map: Vec<(ScalarPtr<Fr>, ScalarExpression<Fr>)> = Arbitrary::arbitrary(g);
            let cont_map: Vec<(ScalarContPtr<Fr>, ScalarContinuation<Fr>)> =
                Arbitrary::arbitrary(g);
            ScalarStore {
                scalar_map: map.into_iter().collect(),
                scalar_cont_map: cont_map.into_iter().collect(),
            }
        }
    }

    #[quickcheck]
    fn prop_scalar_store_ipld(x: ScalarStore<Fr>) -> bool {
        if let Ok(ipld) = to_ipld(x.clone()) {
            if let Ok(y) = from_ipld(ipld) {
                x == y
            } else {
                false
            }
        } else {
            false
        }
    }

    #[test]
    fn test_expr_ipld() {
        let test = |src| {
            let mut store1 = Store::<Fr>::default();
            let expr1 = store1.read(src).unwrap();
            store1.hydrate_scalar_cache();

            if let Some((scalar_store, scalar_expr)) = ScalarStore::new_with_root(&store1, &expr1) {
                let ipld = to_ipld(scalar_store.clone()).unwrap();
                let mut scalar_store2 = from_ipld(ipld).unwrap();
                assert_eq!(scalar_store, scalar_store2);
                if let Some((mut store2, expr2)) = scalar_store2.to_store_with_expr(&scalar_expr) {
                    store2.hydrate_scalar_cache();
                    let (scalar_store3, _) = ScalarStore::new_with_root(&store2, &expr2).unwrap();
                    assert_eq!(scalar_store2, scalar_store3)
                } else {
                    assert!(false)
                }
            } else {
                assert!(false)
            }
        };

        //test("symbol");
        //test("1");
        //test("(1 . 2)");
        //test("\"foo\" . \"bar\")");
        //test("(foo . bar)");
        //test("(1 . 2)");
        //test("(+ 1 2 3)");
        //test("(+ 1 2 (* 3 4))");
        //test("(+ 1 2 (* 3 4) \"asdf\" )");
        //test("(+ 1 2 2 (* 3 4) \"asdf\" \"asdf\")");
    }

    #[test]
    fn test_expr_eval_ipld() {
        use crate::eval;
        let test = |src| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            let env = empty_sym_env(&s);
            let mut eval = eval::Evaluator::new(expr, env, &mut s, 100);
            let (
                eval::IO {
                    expr,
                    env: _,
                    cont: _,
                },
                _lim,
                _emitted,
            ) = eval.eval().unwrap();

            let (scalar_store, _) = ScalarStore::new_with_root(&s, &expr).unwrap();
            println!("{:?}", scalar_store);
            let ipld = to_ipld(scalar_store.clone()).unwrap();
            let scalar_store2 = from_ipld(ipld).unwrap();
            println!("{:?}", scalar_store2);
            assert_eq!(scalar_store, scalar_store2);
        };

        test("(let ((a 123)) (lambda (x) (+ x a)))");
    }

    #[test]
    fn test_scalar_store_top() {
        let test = |src, expected| {
            let mut s = Store::<Fr>::default();
            let expr = s.read(src).unwrap();
            s.hydrate_scalar_cache();

            let (scalar_store, _) = ScalarStore::new_with_root(&s, &expr).unwrap();
            //println!("scalar_store: {}", scalar_store);
            if let Some((scalar_store2, _)) = ScalarStore::new_with_root(&s, &expr) {
                println!("scalar_store2: {}", scalar_store2);
                assert_eq!(expected, scalar_store.scalar_map.len());
                assert_eq!(scalar_store, scalar_store2);
            } else {
                assert!(false)
            }
        };

        test("(1 . 2)", 3);
        test("symbol", 8);
        test("|symbol|", 8);
        test("\"foo\"", 4);
        test("+", 3);
        test("t", 3);
        test("(+ 1 2 3)", 14);
        test("(+ 1 2 (* 3 4))", 20);
        // String are handled.
        test("(+ 1 2 (* 3 4) \"asdf\" )", 25);
        // Duplicate strings or symbols appear only once.
        test("(+ 1 2 2 (* 3 4) \"asdf\" \"asdf\")", 27);
        assert!(false)
    }

    #[test]
    fn test_scalar_store_opaque_cons() {
        let mut store = Store::<Fr>::default();

        let num1 = store.num(123);
        let num2 = store.num(987);
        let cons = store.intern_cons(num1, num2);
        let cons_hash = store.hash_expr(&cons).unwrap();
        let opaque_cons = store.intern_maybe_opaque_cons(*cons_hash.value());

        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_root(&store, &opaque_cons).unwrap();
        println!("{:?}", scalar_store.scalar_map);
        println!("{:?}", scalar_store.scalar_map.len());
        // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
        assert_eq!(3, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_fun() {
        let mut store = Store::<Fr>::default();

        let arg = store.sym("A");
        let body = store.num(123);
        let empty_env = empty_sym_env(&store);
        let fun = store.intern_fun(arg, body, empty_env);
        let fun_hash = store.hash_expr(&fun).unwrap();
        let opaque_fun = store.intern_maybe_opaque_fun(*fun_hash.value());
        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_root(&store, &opaque_fun).unwrap();
        // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
        assert_eq!(4, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_sym() {
        let mut store = Store::<Fr>::default();

        let sym = store.sym(&"sym");
        let sym_hash = store.hash_expr(&sym).unwrap();
        let opaque_sym = store.intern_maybe_opaque_sym(*sym_hash.value());

        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_root(&store, &opaque_sym).unwrap();
        // Only the symbol's string itself, not all of its substrings, appears in `ScalarStore`.
        assert_eq!(1, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_str() {
        let mut store = Store::<Fr>::default();

        let str = store.str(&"str");
        let str_hash = store.hash_expr(&str).unwrap();
        let opaque_str = store.intern_maybe_opaque_sym(*str_hash.value());

        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_root(&store, &opaque_str).unwrap();
        // Only the string itself, not all of its substrings, appears in `ScalarStore`.
        assert_eq!(1, scalar_store.scalar_map.len());
    }
    #[test]
    fn test_scalar_store_opaque_comm() {
        let mut store = Store::<Fr>::default();

        let num = store.num(987);
        let comm = store.intern_comm(Fr::from(123), num);
        let comm_hash = store.hash_expr(&comm).unwrap();
        let opaque_comm = store.intern_maybe_opaque_comm(*comm_hash.value());

        store.hydrate_scalar_cache();

        let (scalar_store, _) = ScalarStore::new_with_root(&store, &opaque_comm).unwrap();
        println!("{:?}", scalar_store.scalar_map);
        println!("{:?}", scalar_store.scalar_map.len());
        // If a non-opaque version has been found when interning opaque, children appear in `ScalarStore`.
        assert_eq!(2, scalar_store.scalar_map.len());
    }
}
