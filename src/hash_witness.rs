use std::fmt::Debug;
use std::marker::PhantomData;

use crate::cont::Continuation;
use crate::field::LurkField;

use crate::ptr::{ContPtr, Ptr};
use crate::z_ptr::ZExprPtr;

pub(crate) const MAX_CONSES_PER_REDUCTION: usize = 11;
pub(crate) const MAX_CONTS_PER_REDUCTION: usize = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Stub<T>(PhantomData<T>);

pub(crate) trait CAddr<F: LurkField> {
    fn preimage(&self) -> Preimage<F>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Cons<F: LurkField> {
    pub(crate) car: Ptr<F>,
    pub(crate) cdr: Ptr<F>,
    pub(crate) cons: Ptr<F>,
}

#[derive(Clone, Debug)]
pub(crate) struct ScalarCons<F: LurkField> {
    pub(crate) car: ZExprPtr<F>,
    pub(crate) cdr: ZExprPtr<F>,
}

#[derive(Clone, Debug)]
pub(crate) struct ScalarCont<F: LurkField> {
    pub(crate) components: [F; 8],
}

impl<F: LurkField> CAddr<F> for ScalarCons<F> {
    fn preimage(&self) -> Preimage<F> {
        vec![
            self.car.tag_field(),
            *self.car.value(),
            self.cdr.tag_field(),
            *self.cdr.value(),
        ]
    }
}

impl<F: LurkField> CAddr<F> for ScalarCont<F> {
    fn preimage(&self) -> Preimage<F> {
        self.components.to_vec()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Cont<F: LurkField> {
    pub(crate) cont_ptr: ContPtr<F>,
    pub(crate) continuation: Continuation<F>,
}

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

pub(crate) trait HashName: Copy {
    fn index(&self) -> usize;
}

impl HashName for ConsName {
    fn index(&self) -> usize {
        #[allow(clippy::match_same_arms)]
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
pub(crate) enum ContName {
    #[default]
    NeverUsed,
}

impl HashName for ContName {
    fn index(&self) -> usize {
        #[allow(clippy::match_same_arms)]
        match self {
            Self::NeverUsed => MAX_CONTS_PER_REDUCTION + 1,
        }
    }
}

pub(crate) type Preimage<F> = Vec<F>;
pub(crate) type WitnessBlock<F> = Vec<F>;
pub(crate) type Digest<F> = F;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct HashWitness<Name: HashName, T, const L: usize, F: LurkField> {
    pub(crate) slots: [(Name, Stub<T>); L],
    _f: PhantomData<F>,
}

pub(crate) type ConsWitness<F> = HashWitness<ConsName, Cons<F>, MAX_CONSES_PER_REDUCTION, F>;
pub(crate) type ContWitness<F> = HashWitness<ContName, Cont<F>, MAX_CONTS_PER_REDUCTION, F>;
