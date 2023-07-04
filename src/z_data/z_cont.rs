#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::BoxedStrategy;
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
use serde::{Deserialize, Serialize};

use crate::field::LurkField;
use crate::hash::PoseidonCache;
use crate::tag::ContTag;
use crate::tag::Op1;
use crate::tag::Op2;
use crate::tag::Tag;
use crate::z_ptr::{ZContPtr, ZExprPtr, ZPtr};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
/// A `ZCont` is the content-addressed representation of a Lurk continuation, which enables
/// efficient serialization and sharing of hashed Lurk data via associated `ZContPtr`s.
pub enum ZCont<F: LurkField> {
    /// The outermost continuation, meaning no further computations will take place
    Outermost,
    /// A function call with no arguments
    Call0 {
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    /// A function call with one argument
    Call {
        saved_env: ZExprPtr<F>,
        unevaled_arg: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    /// A nested function call
    Call2 {
        saved_env: ZExprPtr<F>,
        function: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Tail {
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Error,
    Lookup {
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Unop {
        operator: Op1,
        continuation: ZContPtr<F>,
    },
    Binop {
        operator: Op2,
        saved_env: ZExprPtr<F>,
        unevaled_args: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Binop2 {
        operator: Op2,
        evaled_arg: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    If {
        unevaled_args: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Let {
        var: ZExprPtr<F>,
        body: ZExprPtr<F>,
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    LetRec {
        var: ZExprPtr<F>,
        body: ZExprPtr<F>,
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Emit {
        continuation: ZContPtr<F>,
    },
    Dummy,
    Terminal,
}

impl<F: LurkField> ZCont<F> {
    /// Creates a list of field elements corresponding to the `ZCont` for hashing
    pub fn hash_components(&self) -> [F; 8] {
        match self {
            Self::Outermost => [F::ZERO; 8],
            Self::Call0 {
                saved_env,
                continuation,
            } => [
                saved_env.0.to_field(),
                saved_env.1,
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
                F::ZERO,
                F::ZERO,
            ],
            Self::Call {
                saved_env,
                unevaled_arg,
                continuation,
            } => [
                saved_env.0.to_field(),
                saved_env.1,
                unevaled_arg.0.to_field(),
                unevaled_arg.1,
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
            ],
            Self::Call2 {
                saved_env,
                function,
                continuation,
            } => [
                saved_env.0.to_field(),
                saved_env.1,
                function.0.to_field(),
                function.1,
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
            ],
            Self::Tail {
                saved_env,
                continuation,
            } => [
                saved_env.0.to_field(),
                saved_env.1,
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
                F::ZERO,
                F::ZERO,
            ],
            Self::Error => [F::ZERO; 8],
            Self::Lookup {
                saved_env,
                continuation,
            } => [
                saved_env.0.to_field(),
                saved_env.1,
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
                F::ZERO,
                F::ZERO,
            ],
            Self::Unop {
                operator,
                continuation,
            } => [
                operator.to_field(),
                F::ZERO,
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
                F::ZERO,
                F::ZERO,
            ],
            Self::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => [
                operator.to_field(),
                F::ZERO,
                saved_env.0.to_field(),
                saved_env.1,
                unevaled_args.0.to_field(),
                unevaled_args.1,
                continuation.0.to_field(),
                continuation.1,
            ],
            Self::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => [
                operator.to_field(),
                F::ZERO,
                evaled_arg.0.to_field(),
                evaled_arg.1,
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
            ],
            Self::If {
                unevaled_args,
                continuation,
            } => [
                unevaled_args.0.to_field(),
                unevaled_args.1,
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
                F::ZERO,
                F::ZERO,
            ],
            Self::Let {
                var,
                body,
                saved_env,
                continuation,
            } => [
                var.0.to_field(),
                var.1,
                body.0.to_field(),
                body.1,
                saved_env.0.to_field(),
                saved_env.1,
                continuation.0.to_field(),
                continuation.1,
            ],
            Self::LetRec {
                var,
                body,
                saved_env,
                continuation,
            } => [
                var.0.to_field(),
                var.1,
                body.0.to_field(),
                body.1,
                saved_env.0.to_field(),
                saved_env.1,
                continuation.0.to_field(),
                continuation.1,
            ],
            Self::Emit { continuation } => [
                continuation.0.to_field(),
                continuation.1,
                F::ZERO,
                F::ZERO,
                F::ZERO,
                F::ZERO,
                F::ZERO,
                F::ZERO,
            ],
            Self::Dummy => [F::ZERO; 8],
            Self::Terminal => [F::ZERO; 8],
        }
    }

    /// Hashes the `ZCont` field representation and creates a corresponding `ZContPtr`
    pub fn z_ptr(&self, cache: &PoseidonCache<F>) -> ZContPtr<F> {
        let hash = cache.hash8(&self.hash_components());
        match self {
            Self::Outermost => ZPtr(ContTag::Outermost, hash),
            Self::Call0 { .. } => ZPtr(ContTag::Call0, hash),
            Self::Call { .. } => ZPtr(ContTag::Call, hash),
            Self::Call2 { .. } => ZPtr(ContTag::Call2, hash),
            Self::Tail { .. } => ZPtr(ContTag::Tail, hash),
            Self::Error => ZPtr(ContTag::Error, hash),
            Self::Lookup { .. } => ZPtr(ContTag::Lookup, hash),
            Self::Unop { .. } => ZPtr(ContTag::Unop, hash),
            Self::Binop { .. } => ZPtr(ContTag::Binop, hash),
            Self::Binop2 { .. } => ZPtr(ContTag::Binop2, hash),
            Self::If { .. } => ZPtr(ContTag::If, hash),
            Self::Let { .. } => ZPtr(ContTag::Let, hash),
            Self::LetRec { .. } => ZPtr(ContTag::LetRec, hash),
            Self::Emit { .. } => ZPtr(ContTag::Emit, hash),
            Self::Dummy => ZPtr(ContTag::Dummy, hash),
            Self::Terminal => ZPtr(ContTag::Terminal, hash),
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
impl<F: LurkField> Arbitrary for ZCont<F> {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
        prop_oneof![
            Just(ZCont::Outermost),
            any::<(ZExprPtr<F>, ZContPtr<F>)>().prop_map(|(saved_env, continuation)| {
                ZCont::Call0 {
                    saved_env,
                    continuation,
                }
            }),
            any::<(ZExprPtr<F>, ZExprPtr<F>, ZContPtr<F>)>().prop_map(
                |(saved_env, unevaled_arg, continuation)| ZCont::Call {
                    saved_env,
                    unevaled_arg,
                    continuation
                }
            ),
            any::<(ZExprPtr<F>, ZExprPtr<F>, ZContPtr<F>)>().prop_map(
                |(saved_env, function, continuation)| ZCont::Call2 {
                    saved_env,
                    function,
                    continuation
                }
            ),
            any::<(ZExprPtr<F>, ZContPtr<F>)>().prop_map(|(saved_env, continuation)| ZCont::Tail {
                saved_env,
                continuation
            }),
            Just(ZCont::Error),
            any::<(ZExprPtr<F>, ZContPtr<F>)>().prop_map(|(saved_env, continuation)| {
                ZCont::Lookup {
                    saved_env,
                    continuation,
                }
            }),
            any::<(Op1, ZContPtr<F>)>().prop_map(|(operator, continuation)| ZCont::Unop {
                operator,
                continuation
            }),
            any::<(Op2, ZExprPtr<F>, ZExprPtr<F>, ZContPtr<F>)>().prop_map(
                |(operator, saved_env, unevaled_args, continuation)| ZCont::Binop {
                    operator,
                    saved_env,
                    unevaled_args,
                    continuation
                }
            ),
            any::<(Op2, ZExprPtr<F>, ZContPtr<F>)>().prop_map(
                |(operator, evaled_arg, continuation)| ZCont::Binop2 {
                    operator,
                    evaled_arg,
                    continuation
                }
            ),
            any::<(ZExprPtr<F>, ZContPtr<F>)>().prop_map(|(unevaled_args, continuation)| {
                ZCont::If {
                    unevaled_args,
                    continuation,
                }
            }),
            any::<(ZExprPtr<F>, ZExprPtr<F>, ZExprPtr<F>, ZContPtr<F>)>().prop_map(
                |(var, body, saved_env, continuation)| ZCont::Let {
                    var,
                    body,
                    saved_env,
                    continuation,
                }
            ),
            any::<(ZExprPtr<F>, ZExprPtr<F>, ZExprPtr<F>, ZContPtr<F>)>().prop_map(
                |(var, body, saved_env, continuation)| ZCont::LetRec {
                    var,
                    body,
                    saved_env,
                    continuation,
                }
            ),
            any::<ZContPtr<F>>().prop_map(|continuation| ZCont::Emit { continuation }),
            Just(ZCont::Dummy),
            Just(ZCont::Terminal),
        ]
        .boxed()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::z_data::{from_z_data, to_z_data};
    use pasta_curves::pallas::Scalar;

    proptest! {
          #[test]
          fn prop_serde_z_cont(x in any::<ZCont<Scalar>>()) {
              let ser = to_z_data(&x).expect("write ZCont");
              let de: ZCont<Scalar> = from_z_data(&ser).expect("read ZCont");
              assert_eq!(x, de);

              let ser: Vec<u8> = bincode::serialize(&x).expect("write ZCont");
              let de: ZCont<Scalar> = bincode::deserialize(&ser).expect("read ZCont");
              assert_eq!(x, de);
          }
    }
}
