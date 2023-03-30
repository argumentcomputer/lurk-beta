use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;

use crate::error::ReductionError;
use crate::field::LurkField;
use crate::store::{self, ContPtr, Continuation, Pointer, Ptr, Store};
use crate::tag::ExprTag;

pub const MAX_CONSES_PER_REDUCTION: usize = 11;
pub const MAX_CONTS_PER_REDUCTION: usize = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stub<T> {
    Dummy,
    Blank,
    Value(T),
}

impl<T> Stub<T> {
    fn is_dummy(&self) -> bool {
        matches!(self, Self::Dummy)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cons<F: LurkField> {
    pub car: Ptr<F>,
    pub cdr: Ptr<F>,
    pub cons: Ptr<F>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cont<F: LurkField> {
    pub cont_ptr: ContPtr<F>,
    pub continuation: Continuation<F>,
}

pub type ConsStub<F> = Stub<Cons<F>>;
pub type ContStub<F> = Stub<Cont<F>>;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Default)]
pub enum ConsName {
    #[default]
    NeverUsed,
    Env,
    EnvCar,
    EnvCaar,
    Expr,
    ExprCdr,
    ExprCadr,
    ExprCaadr,
    ExprCaaadr,
    ExprCddr,
    UnopConsLike,
    FunBody,
    NewRec,
    NewRecCadr,
    ExtendedRec,
    UnevaledArgs,
    UnevaledArgsCdr,
    Begin,
    EnvToUse,
    InnerBody,
    Lambda,
    InnerLambda,
    TheCons,
    FunExpanded,
    ExtendedClosureEnv,
    Binding,
    ClosedEnv,
    ExpandedInner0,
    ExpandedInner,
    Expanded,
}

pub trait HashName {
    fn index(&self) -> usize;
}

impl HashName for ConsName {
    fn index(&self) -> usize {
        match self {
            Self::NeverUsed => MAX_CONSES_PER_REDUCTION + 1,
            Self::Expr => 0,
            Self::ExprCdr => 1,
            Self::UnevaledArgsCdr => 1,
            Self::ExprCadr => 2,
            Self::ExprCddr => 3,
            Self::UnopConsLike => 3,
            Self::Lambda => 3,
            Self::ExprCaadr => 4,
            Self::Begin => 4,
            Self::InnerBody => 4,
            Self::ExtendedClosureEnv => 4,
            Self::UnevaledArgs => 5,
            Self::ExprCaaadr => 5,
            Self::ExtendedRec => 5,
            Self::EnvToUse => 5,
            Self::Binding => 5,
            Self::FunBody => 6,
            Self::NewRecCadr => 6,
            Self::NewRec => 7,
            Self::ClosedEnv => 7,
            Self::Env => 8,
            Self::ExpandedInner0 => 8,
            Self::FunExpanded => 9,
            Self::Expanded => 9,
            Self::EnvCar => 9,
            Self::InnerLambda => 10,
            Self::TheCons => 10,
            Self::EnvCaar => 10,
            Self::ExpandedInner => 10,
        }
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Default)]
pub enum ContName {
    #[default]
    NeverUsed,
    ApplyContinuation,
    LetLike,
    NewerCont,
    NewerCont2,
    MakeThunk,
    Lookup,
}

impl HashName for ContName {
    fn index(&self) -> usize {
        match self {
            Self::NeverUsed => MAX_CONTS_PER_REDUCTION + 1,
            Self::ApplyContinuation => 0,
            Self::Lookup => 0,
            Self::NewerCont => 1,
            Self::NewerCont2 => 1,
            Self::LetLike => 1,
            Self::MakeThunk => 1,
        }
    }
}

impl<F: LurkField> ConsStub<F> {
    pub fn car_cdr(
        &mut self,
        s: &Store<F>,
        cons: &Ptr<F>,
    ) -> Result<(Ptr<F>, Ptr<F>), store::Error> {
        match self {
            Self::Dummy => {
                let (car, cdr) = Cons::get_car_cdr(s, cons)?;

                *self = Self::Value(Cons {
                    car,
                    cdr,
                    cons: *cons,
                });

                Ok((car, cdr))
            }
            Self::Blank => unreachable!("Blank ConsStub should be used only in blank circuits."),
            Self::Value(h) => Ok(h.car_cdr(cons)),
        }
    }

    pub fn car_cdr_mut(
        &mut self,
        s: &mut Store<F>,
        cons: &Ptr<F>,
    ) -> Result<(Ptr<F>, Ptr<F>), store::Error> {
        match self {
            Self::Dummy => {
                let (car, cdr) = Cons::get_car_cdr_mut(s, cons)?;

                *self = Self::Value(Cons {
                    car,
                    cdr,
                    cons: *cons,
                });

                Ok((car, cdr))
            }
            Self::Blank => unreachable!("Blank ConsStub should be used only in blank circuits."),
            Self::Value(h) => Ok(h.car_cdr(cons)),
        }
    }

    pub fn cons(&mut self, store: &mut Store<F>, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        match self {
            Self::Dummy => {
                let cons = Cons::cons(store, car, cdr);

                *self = Self::Value(Cons { car, cdr, cons });

                cons
            }
            Self::Blank => unreachable!("Blank ConsStub should be used only in blank circuits."),
            Self::Value(_) => Cons::cons(store, car, cdr),
        }
    }
    pub fn strcons(&mut self, store: &mut Store<F>, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        match self {
            Self::Dummy => {
                let cons = Cons::strcons(store, car, cdr);

                *self = Self::Value(Cons { car, cdr, cons });

                cons
            }
            Self::Blank => unreachable!("Blank ConsStub should be used only in blank circuits."),
            Self::Value(_) => Cons::strcons(store, car, cdr),
        }
    }
}

impl<F: LurkField> ContStub<F> {}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct HashWitness<Name: HashName, T, const L: usize, F: LurkField> {
    pub slots: [(Name, Stub<T>); L],
    _f: PhantomData<F>,
}

impl<Name: HashName, T, const L: usize, F: LurkField> HashWitness<Name, T, L, F> {
    pub fn length() -> usize {
        L
    }
}

pub type ConsWitness<F> = HashWitness<ConsName, Cons<F>, MAX_CONSES_PER_REDUCTION, F>;
pub type ContWitness<F> = HashWitness<ContName, Cont<F>, MAX_CONTS_PER_REDUCTION, F>;

impl<F: LurkField> HashWitness<ConsName, Cons<F>, MAX_CONSES_PER_REDUCTION, F> {
    #[allow(dead_code)]
    fn assert_specific_invariants(&self, store: &Store<F>) {
        // Use the commented code below to search for (non-nil) duplicated conses, which could indicate that two
        // different Cons are being used to reference the identical structural value. In that case, they could be
        // coalesced, potentially leading to fewer slots being required.
        //
        // As of the initial optimization pass, Env and ExtendedClosureEnv appear to be duplicated in this way. However,
        // it's not clear why that is, and coalescing them does not obviously lead to a potential savings, so we will
        // leave them distinct for now.

        let mut digests = HashMap::new();

        for (name, p) in self.slots.iter() {
            match p {
                Stub::Value(hash) => {
                    if let Some(existing_name) = digests.insert(hash.cons, name) {
                        let nil = store.get_nil();
                        if !store.ptr_eq(&hash.cons, &nil).unwrap() {
                            use crate::writer::Write;
                            let cons = hash.cons.fmt_to_string(store);
                            dbg!(hash.cons, cons, name, existing_name);
                            panic!("duplicate");
                        }
                    };
                }
                _ => (),
            };
        }
    }
}

impl<
        Name: HashName + Default + Copy + Eq + Debug,
        T: Copy,
        const MAX_T_PER_REDUCTION: usize,
        F: LurkField,
    > HashWitness<Name, T, MAX_T_PER_REDUCTION, F>
{
    pub fn new_from_stub(stub: Stub<T>) -> Self {
        Self {
            slots: [(Name::default(), stub); MAX_T_PER_REDUCTION],
            _f: Default::default(),
        }
    }

    pub fn new_dummy() -> Self {
        Self::new_from_stub(Stub::Dummy)
    }

    pub fn new_blank() -> Self {
        Self::new_from_stub(Stub::Blank)
    }

    pub fn get_assigned_slot(&mut self, name: Name) -> &mut Stub<T> {
        let i = name.index();
        let (slot_name, p) = self.slots[i];
        if p.is_dummy() {
            self.slots[i].0 = name;
            return &mut self.slots[i].1;
        }
        if slot_name == name {
            &mut self.slots[i].1
        } else {
            panic!(
                "double booked: found {:?} when getting {:?}",
                &slot_name, &name
            );
        }
    }

    pub fn assert_invariants(&self, _store: &Store<F>) {
        // TODO: Figure out how to make this work.
        // self.assert_specific_invariants(store);
        assert!(self.stubs_used_count() <= MAX_T_PER_REDUCTION);
    }

    fn all_stubs(&self) -> Vec<Stub<T>> {
        self.slots.iter().map(|x| x.1).collect()
    }

    pub fn all_names(&self) -> Vec<Name> {
        self.slots.iter().map(|x| x.0).collect()
    }

    pub fn stubs_used(&self) -> Vec<Stub<T>> {
        self.all_stubs()
            .into_iter()
            .filter(|c| !c.is_dummy())
            .collect()
    }

    pub fn stubs_used_count(&self) -> usize {
        self.all_stubs().iter().filter(|c| !c.is_dummy()).count()
    }

    pub fn total_stub(&self) -> usize {
        self.all_stubs().len()
    }
}

impl<F: LurkField> ConsWitness<F> {
    pub fn car_cdr_named(
        &mut self,
        name: ConsName,
        store: &Store<F>,
        cons: &Ptr<F>,
    ) -> Result<(Ptr<F>, Ptr<F>), ReductionError> {
        if !matches!(cons.tag(), ExprTag::Cons | ExprTag::Nil) {
            return Err(ReductionError::CarCdrType(name));
        };
        self.get_assigned_slot(name)
            .car_cdr(store, cons)
            .map_err(|e| e.into())
    }

    pub fn cons_named(
        &mut self,
        name: ConsName,
        store: &mut Store<F>,
        car: Ptr<F>,
        cdr: Ptr<F>,
    ) -> Ptr<F> {
        self.get_assigned_slot(name).cons(store, car, cdr)
    }

    pub fn strcons_named(
        &mut self,
        name: ConsName,
        store: &mut Store<F>,
        car: Ptr<F>,
        cdr: Ptr<F>,
    ) -> Ptr<F> {
        self.get_assigned_slot(name).strcons(store, car, cdr)
    }

    pub fn car_cdr_mut_named(
        &mut self,
        name: ConsName,
        store: &mut Store<F>,
        cons: &Ptr<F>,
    ) -> Result<(Ptr<F>, Ptr<F>), store::Error> {
        self.get_assigned_slot(name).car_cdr_mut(store, cons)
    }

    pub fn extend_named(
        &mut self,
        name: ConsName,
        env: Ptr<F>,
        var: Ptr<F>,
        val: Ptr<F>,
        store: &mut Store<F>,
    ) -> Ptr<F> {
        let binding = self.cons_named(ConsName::Binding, store, var, val);

        self.cons_named(name, store, binding, env)
    }
}

impl<F: LurkField> Cons<F> {
    fn cons(store: &mut Store<F>, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        store.cons(car, cdr)
    }

    fn strcons(store: &mut Store<F>, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        store.strcons(car, cdr)
    }

    fn car_cdr(&self, cons: &Ptr<F>) -> (Ptr<F>, Ptr<F>) {
        assert_eq!(cons, &self.cons, "wrong cons found when destructuring");

        (self.car, self.cdr)
    }

    fn get_car_cdr(s: &Store<F>, cons: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>), store::Error> {
        s.car_cdr(cons)
    }

    fn get_car_cdr_mut(s: &mut Store<F>, cons: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>), store::Error> {
        s.car_cdr_mut(cons)
    }
}

impl<F: LurkField> ContWitness<F> {
    pub fn fetch_named_cont(
        &mut self,
        name: ContName,
        store: &mut Store<F>,
        cont: &ContPtr<F>,
    ) -> Option<Continuation<F>> {
        self.get_assigned_slot(name).fetch_cont(store, cont)
    }

    pub fn intern_named_cont(
        &mut self,
        name: ContName,
        store: &mut Store<F>,
        continuation: Continuation<F>,
    ) -> ContPtr<F> {
        self.get_assigned_slot(name)
            .intern_cont(store, continuation)
    }
}

impl<F: LurkField> ContStub<F> {
    pub fn fetch_cont(
        &mut self,
        store: &mut Store<F>,
        cont: &ContPtr<F>,
    ) -> Option<Continuation<F>> {
        match self {
            Self::Dummy => {
                let continuation = store.fetch_cont(cont)?;
                // dbg!("overwriting dummy", continuation, store.hash_cont(&cont));
                *self = Self::Value(Cont {
                    cont_ptr: *cont,
                    continuation,
                });

                Some(continuation)
            }
            Self::Blank => unreachable!("Blank ContStub should be used only in blank circuits."),
            Self::Value(h) => Some(h.fetch_cont(cont)),
        }
    }
    pub fn intern_cont(
        &mut self,
        store: &mut Store<F>,
        continuation: Continuation<F>,
    ) -> ContPtr<F> {
        match self {
            Self::Dummy => {
                let cont_ptr = continuation.intern_aux(store);
                *self = Self::Value(Cont {
                    cont_ptr,
                    continuation,
                });
                cont_ptr
            }
            Self::Blank => unreachable!("Blank ContStub should be used only in blank circuits."),
            Self::Value(h) => h.cont_ptr,
        }
    }
}

impl<F: LurkField> Cont<F> {
    fn fetch_cont(&mut self, cont: &ContPtr<F>) -> Continuation<F> {
        assert_eq!(cont, &self.cont_ptr);

        self.continuation
    }
}
