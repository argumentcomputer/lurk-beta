use crate::field::LurkField;
use crate::store;
use crate::store::{Ptr, Store};

pub const MAX_CONSES_PER_REDUCTION: usize = 11;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stub<T> {
    Dummy,
    Blank,
    Value(T),
}

pub type HashStub<F> = Stub<Cons<F>>;

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

impl ConsName {
    pub fn index(&self) -> usize {
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

impl<F: LurkField> HashStub<F> {
    pub fn car_cdr(&mut self, s: &mut Store<F>, cons: &Ptr<F>) -> (Ptr<F>, Ptr<F>) {
        match self {
            Self::Dummy => {
                let (car, cdr) = Cons::get_car_cdr(s, cons);

                *self = Self::Value(Cons {
                    car,
                    cdr,
                    cons: *cons,
                });

                (car, cdr)
            }
            Self::Blank => unreachable!("Blank HashStub should be used only in blank circuits."),
            Self::Value(h) => h.car_cdr(cons),
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
            Self::Blank => unreachable!("Blank HashStub should be used only in blank circuits."),
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
            Self::Blank => unreachable!("Blank HashStub should be used only in blank circuits."),
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
            Self::Blank => unreachable!("Blank HashStub should be used only in blank circuits."),
            Self::Value(_) => Cons::strcons(store, car, cdr),
        }
    }

    fn is_dummy(&self) -> bool {
        matches!(self, Self::Dummy)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct HashWitness<F: LurkField> {
    pub slots: [(ConsName, HashStub<F>); MAX_CONSES_PER_REDUCTION],
}

impl<F: LurkField> HashWitness<F> {
    pub fn new_from_stub(stub: HashStub<F>) -> Self {
        Self {
            slots: [(ConsName::NeverUsed, stub); MAX_CONSES_PER_REDUCTION],
        }
    }

    pub fn new_dummy() -> Self {
        Self::new_from_stub(HashStub::Dummy)
    }

    pub fn new_blank() -> Self {
        Self::new_from_stub(HashStub::Blank)
    }

    pub fn get_assigned_slot(&mut self, name: ConsName) -> &mut HashStub<F> {
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

    pub fn get_named_cons(&self, name: &ConsName) -> HashStub<F> {
        for (slot_name, p) in &self.slots {
            if slot_name == name {
                return *p;
            }
        }

        Stub::Dummy
    }

    pub fn car_cdr_named(
        &mut self,
        name: ConsName,
        store: &mut Store<F>,
        cons: &Ptr<F>,
    ) -> (Ptr<F>, Ptr<F>) {
        self.get_assigned_slot(name).car_cdr(store, cons)
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

    pub fn assert_invariants(&self, _store: &Store<F>) {
        // Use the commented code below to search for (non-nil) duplicated conses, which could indicate that two
        // different Cons are being used to reference the identical structural value. In that case, they could be
        // coalesced, potentially leading to fewer slots being required.
        //
        // As of the initial optimization pass, Env and ExtendedClosureEnv appear to be duplicated in this way. However,
        // it's not clear why that is, and coalescing them does not obviously lead to a potential savings, so we will
        // leave them distinct for now.

        // let mut digests = HashMap::new();

        // for (name, p) in self.slots.iter() {
        //     match p {
        //         Stub::Value(hash) => {
        //             if let Some(existing_name) = digests.insert(hash.cons, name) {
        //                 use crate::writer::Write;
        //                 let nil = store.get_nil();
        //                 if !store.ptr_eq(&hash.cons, &nil).unwrap() {
        //                     let cons = hash.cons.fmt_to_string(store);
        //                     dbg!(hash.cons, cons, name, existing_name);
        //                     panic!("duplicate");
        //                 }
        //             };
        //         }
        //         _ => (),
        //     };
        // }

        assert!(self.conses_used_count() <= MAX_CONSES_PER_REDUCTION);
    }

    fn all_conses(&self) -> Vec<HashStub<F>> {
        self.slots.iter().map(|x| x.1).collect()
    }

    pub fn conses_used(&self) -> Vec<HashStub<F>> {
        self.all_conses()
            .into_iter()
            .filter(|c| !c.is_dummy())
            .collect()
    }

    pub fn conses_used_count(&self) -> usize {
        self.all_conses().iter().filter(|c| !c.is_dummy()).count()
    }

    pub fn total_conses(&self) -> usize {
        self.all_conses().len()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cons<F: LurkField> {
    pub car: Ptr<F>,
    pub cdr: Ptr<F>,
    pub cons: Ptr<F>,
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

    fn get_car_cdr(s: &mut Store<F>, cons: &Ptr<F>) -> (Ptr<F>, Ptr<F>) {
        s.car_cdr(cons)
    }

    fn get_car_cdr_mut(s: &mut Store<F>, cons: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>), store::Error> {
        s.car_cdr_mut(cons)
    }
}
