use std::fmt::Debug;

use bellperson::{ConstraintSystem, SynthesisError};

use crate::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use crate::eval::IO;
use crate::field::LurkField;
use crate::store::{ContPtr, Ptr, Store};

pub trait Coprocessor<F: LurkField>: Clone + Debug + Sync + CoCircuit<F> {
    fn eval_arity(&self) -> usize;

    fn evaluate(&self, s: &mut Store<F>, args: Ptr<F>, env: Ptr<F>, cont: ContPtr<F>) -> IO<F> {
        let argv: Vec<Ptr<F>> = if let Some(list) = s.fetch_list(&args) {
            list
        } else {
            return IO {
                expr: args,
                env,
                cont: s.intern_cont_error(),
            };
        };

        if argv.len() != self.eval_arity() {
            return IO {
                expr: args,
                env,
                cont: s.intern_cont_error(),
            };
        };

        let result = self.simple_evaluate(s, &argv);

        IO {
            expr: result,
            env,
            cont,
        }
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F>;
}

pub trait CoCircuit<F: LurkField>: Send + Sync + Clone {
    fn arity(&self) -> usize {
        todo!()
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _store: &Store<F>,
        _input_exprs: &[AllocatedPtr<F>],
        _input_env: &AllocatedPtr<F>,
        _input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        todo!()
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use std::marker::PhantomData;

    /// A dumb Coprocessor for testing.
    #[derive(Clone, Debug)]
    pub(crate) struct DumbCoprocessor<F: LurkField> {
        pub(crate) _p: PhantomData<F>,
    }

    impl<F: LurkField> CoCircuit<F> for DumbCoprocessor<F> {}

    impl<F: LurkField> Coprocessor<F> for DumbCoprocessor<F> {
        /// Dumb Coprocessor takes two arguments.
        fn eval_arity(&self) -> usize {
            2
        }

        /// It squares the first arg and adds it to the second.
        fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
            let a = args[0];
            let b = args[1];

            let a_num = s.fetch_num(&a).unwrap();
            let b_num = s.fetch_num(&b).unwrap();
            let mut result = *a_num;
            result *= *a_num;
            result += *b_num;
            use crate::writer::Write;
            let x = s.intern_num(result);

            return x;
        }
    }

    impl<F: LurkField> DumbCoprocessor<F> {
        pub(crate) fn new() -> Self {
            Self {
                _p: Default::default(),
            }
        }
    }
}
