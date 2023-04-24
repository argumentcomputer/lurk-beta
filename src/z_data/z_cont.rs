use crate::field::LurkField;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

use crate::tag::Op1;
use crate::tag::Op2;
use crate::z_data::ZContPtr;
use crate::z_data::ZExprPtr;

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
pub enum ZCont<F: LurkField> {
    Outermost,
    Call {
        unevaled_arg: ZExprPtr<F>,
        saved_env: ZExprPtr<F>,
        continuation: ZContPtr<F>,
    },
    Call2 {
        function: ZExprPtr<F>,
        saved_env: ZExprPtr<F>,
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
