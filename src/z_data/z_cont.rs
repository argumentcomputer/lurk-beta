use anyhow::anyhow;
use serde::{Deserialize, Serialize};

use crate::field::LurkField;
use crate::z_data::Encodable;
use crate::z_data::ZData;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::BoxedStrategy;
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use crate::hash::PoseidonCache;
use crate::tag::ContTag;
use crate::tag::Op1;
use crate::tag::Op2;
use crate::tag::Tag;
use crate::z_ptr::{ZContPtr, ZExprPtr, ZPtr};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub enum ZCont<F: LurkField> {
    Outermost,
    Call0 {
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Call {
        saved_env: ZExprPtr<F>,
        // TODO: name should be arg or args?
        unevaled_arg: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
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

impl<F: LurkField> Encodable for ZCont<F> {
    fn ser(&self) -> ZData {
        match self {
            ZCont::Outermost => ZData::Cell(vec![ZData::Atom(vec![0u8])]),
            ZCont::Call0 {
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![1u8]),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![2u8]),
                unevaled_arg.ser(),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Call2 {
                function,
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![3u8]),
                function.ser(),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Tail {
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![4u8]),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Error => ZData::Cell(vec![ZData::Atom(vec![5u8])]),
            ZCont::Lookup {
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![6u8]),
                saved_env.ser(),
                continuation.ser(),
            ]),

            ZCont::Unop {
                operator,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![7u8]),
                operator.ser(),
                continuation.ser(),
            ]),
            ZCont::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![8u8]),
                operator.ser(),
                saved_env.ser(),
                unevaled_args.ser(),
                continuation.ser(),
            ]),
            ZCont::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![9u8]),
                operator.ser(),
                evaled_arg.ser(),
                continuation.ser(),
            ]),
            ZCont::If {
                unevaled_args,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![10u8]),
                unevaled_args.ser(),
                continuation.ser(),
            ]),
            ZCont::Let {
                var,
                body,
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![11u8]),
                var.ser(),
                body.ser(),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::LetRec {
                var,
                body,
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![12u8]),
                var.ser(),
                body.ser(),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Emit { continuation } => {
                ZData::Cell(vec![ZData::Atom(vec![13u8]), continuation.ser()])
            }
            ZCont::Dummy => ZData::Cell(vec![ZData::Atom(vec![14u8])]),
            ZCont::Terminal => ZData::Cell(vec![ZData::Atom(vec![15u8])]),
        }
    }
    fn de(ld: &ZData) -> anyhow::Result<Self> {
        match ld {
            ZData::Atom(v) => Err(anyhow!("ZExpr::Atom({:?})", v)),
            ZData::Cell(v) => match (*v).as_slice() {
                [ZData::Atom(u)] if *u == vec![0u8] => Ok(ZCont::Outermost),
                [ZData::Atom(u), x, y] if *u == vec![1u8] => Ok(ZCont::Call0 {
                    saved_env: ZExprPtr::de(x)?,
                    continuation: ZContPtr::de(y)?,
                }),
                [ZData::Atom(u), x, y, z] if *u == vec![2u8] => Ok(ZCont::Call {
                    unevaled_arg: ZExprPtr::de(x)?,
                    saved_env: ZExprPtr::de(y)?,
                    continuation: ZContPtr::de(z)?,
                }),
                [ZData::Atom(u), x, y, z] if *u == vec![3u8] => Ok(ZCont::Call2 {
                    function: ZExprPtr::de(x)?,
                    saved_env: ZExprPtr::de(y)?,
                    continuation: ZContPtr::de(z)?,
                }),
                [ZData::Atom(u), x, y] if *u == vec![4u8] => Ok(ZCont::Tail {
                    saved_env: ZExprPtr::de(x)?,
                    continuation: ZContPtr::de(y)?,
                }),
                [ZData::Atom(u)] if *u == vec![5u8] => Ok(ZCont::Error),
                [ZData::Atom(u), x, y] if *u == vec![6u8] => Ok(ZCont::Lookup {
                    saved_env: ZExprPtr::de(x)?,
                    continuation: ZContPtr::de(y)?,
                }),
                [ZData::Atom(u), x, y] if *u == vec![7u8] => Ok(ZCont::Unop {
                    operator: Op1::de(x)?,
                    continuation: ZContPtr::de(y)?,
                }),
                [ZData::Atom(u), w, x, y, z] if *u == vec![8u8] => Ok(ZCont::Binop {
                    operator: Op2::de(w)?,
                    saved_env: ZExprPtr::de(x)?,
                    unevaled_args: ZExprPtr::de(y)?,
                    continuation: ZContPtr::de(z)?,
                }),
                [ZData::Atom(u), x, y, z] if *u == vec![9u8] => Ok(ZCont::Binop2 {
                    operator: Op2::de(x)?,
                    evaled_arg: ZExprPtr::de(y)?,
                    continuation: ZContPtr::de(z)?,
                }),
                [ZData::Atom(u), x, y] if *u == vec![10u8] => Ok(ZCont::If {
                    unevaled_args: ZExprPtr::de(x)?,
                    continuation: ZContPtr::de(y)?,
                }),
                [ZData::Atom(u), w, x, y, z] if *u == vec![11u8] => Ok(ZCont::Let {
                    var: ZExprPtr::de(w)?,
                    body: ZExprPtr::de(x)?,
                    saved_env: ZExprPtr::de(y)?,
                    continuation: ZContPtr::de(z)?,
                }),
                [ZData::Atom(u), w, x, y, z] if *u == vec![12u8] => Ok(ZCont::LetRec {
                    var: ZExprPtr::de(w)?,
                    body: ZExprPtr::de(x)?,
                    saved_env: ZExprPtr::de(y)?,
                    continuation: ZContPtr::de(z)?,
                }),
                [ZData::Atom(u), x] if *u == vec![13u8] => Ok(ZCont::Emit {
                    continuation: ZContPtr::de(x)?,
                }),
                [ZData::Atom(u)] if *u == vec![14u8] => Ok(ZCont::Dummy),
                [ZData::Atom(u)] if *u == vec![15u8] => Ok(ZCont::Terminal),
                _ => Err(anyhow!("ZExpr::Cell({:?})", v)),
            },
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
          fn prop_z_cont(x in any::<ZCont<Scalar>>()) {
             let ser = to_z_data(&x).expect("write ZCont");
             let de: ZCont<Scalar> = from_z_data(&ser).expect("read ZCont");
              assert_eq!(x, de)
          }
    }
}
