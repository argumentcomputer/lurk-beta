use std::fmt::Debug;
use std::marker::PhantomData;

use crate::eval::IO;
use crate::field::LurkField;
use crate::store::{ContPtr, Ptr, Store};

pub trait Coprocessor<F: LurkField>: Debug + Sync {
    fn arity(&self) -> usize;

    fn evaluate(&self, s: &mut Store<F>, args: Ptr<F>, env: Ptr<F>, cont: ContPtr<F>) -> IO<F> {
        let argv: Vec<Ptr<F>> = s.fetch_list(&args);

        use crate::writer::Write;
        dbg!(args.fmt_to_string(s));
        assert_eq!(argv.len(), self.arity());

        let result = self.simple_evaluate(s, &argv);

        IO {
            expr: result,
            env,
            cont,
        }
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F>;
}

#[derive(Debug, Default)]
/// A dumb Coprocessor for testing.
pub(crate) struct DumbCoprocessor<F: LurkField> {
    pub _p: PhantomData<F>,
}

impl<F: LurkField> Coprocessor<F> for DumbCoprocessor<F> {
    /// Dumb Coprocessor takes two arguments.
    fn arity(&self) -> usize {
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

        s.intern_num(result)
    }
}

impl<F: LurkField> DumbCoprocessor<F> {
    pub fn new() -> Self {
        Self {
            _p: Default::default(),
        }
    }
}
