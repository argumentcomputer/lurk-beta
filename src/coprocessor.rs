use std::marker::PhantomData;

use crate::eval::IO;
use crate::field::LurkField;
use crate::store::{ContPtr, Ptr, Store};

pub trait Coprocessor<F: LurkField> {
    fn arity(&self) -> usize;

    fn evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>], env: Ptr<F>, cont: ContPtr<F>) -> IO<F> {
        assert_eq!(args.len(), self.arity());

        let result = self.simple_evaluate(s, args);

        IO {
            expr: result,
            env,
            cont,
        }
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F>;
}

struct DumbCoprocessor<F: LurkField> {
    _p: PhantomData<F>,
}

impl<F: LurkField> Coprocessor<F> for DumbCoprocessor<F> {
    fn arity(&self) -> usize {
        2
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let a = args[0];
        let b = args[1];

        let a_num = s.fetch_num(&a).unwrap();
        let b_num = s.fetch_num(&b).unwrap();
        let mut result = *a_num;
        result *= *a_num;
        result += *b_num;

        s.intern_num(result)
    }
}
