use std::fmt;

#[derive(PartialEq, Eq, Debug, Clone)]
#[repr(C)]
pub enum Syntax {
    Var(String, usize),
    Lam(String, Box<Syntax>),
    App(Box<Syntax>, Box<Syntax>),
}

impl fmt::Display for Syntax {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Var(name, _) => write!(f, "{}", name),
            Self::Lam(name, bod) => {
                write!(f, "λ{}", name)?;
                let mut bod = &**bod;
                while let Syntax::Lam(name, body) = bod {
                    write!(f, " {}", name)?;
                    bod = &*body;
                }
                write!(f, ".{}", bod)
            }
            Self::App(fun, arg) => {
                write!(f, "(")?;
                let mut args = vec![arg];
                let mut fun = &**fun;
                while let Syntax::App(fun2, arg2) = fun {
                    args.push(arg2);
                    fun = fun2;
                }
                write!(f, "{}", fun)?;
                for arg in args.iter().rev() {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    use im::Vector;
    use std::ops::Range;

    use quickcheck::{Arbitrary, Gen};
    use std::mem::MaybeUninit;

    // implement quickcheck arbitrary generator
    #[derive(Debug)]
    #[repr(C)]
    pub enum SyntaxMaybeUninit {
        Var(String, usize),
        Lam(String, Box<MaybeUninit<SyntaxMaybeUninit>>),
        App(
            Box<MaybeUninit<SyntaxMaybeUninit>>,
            Box<MaybeUninit<SyntaxMaybeUninit>>,
        ),
    }

    #[derive(Debug, Clone, Copy)]
    pub enum Case {
        VAR,
        LAM,
        APP,
    }

    pub fn gen_range(g: &mut Gen, range: Range<usize>) -> usize {
        let res: usize = Arbitrary::arbitrary(g);
        (res % (range.end - range.start)) + range.start
    }

    pub fn next_case(g: &mut Gen, gens: &Vec<(usize, Case)>) -> Case {
        let sum: usize = gens.iter().map(|x| x.0).sum();
        let mut weight: usize = gen_range(g, 1..(sum + 1));
        for gen in gens {
            match weight.checked_sub(gen.0) {
                None | Some(0) => {
                    return gen.1;
                }
                _ => {
                    weight -= gen.0;
                }
            }
        }
        panic!("Calculation error for weight = {}", weight);
    }

    pub fn arbitrary_name(g: &mut Gen) -> String {
        let c: u32 = Arbitrary::arbitrary(g);
        unsafe { char::from_u32_unchecked((c % 26) + 97).to_string() }
    }

    pub fn arbitrary_syntax(g: &mut Gen) -> Syntax {
        let mut todo: Vec<(Vector<String>, *mut MaybeUninit<SyntaxMaybeUninit>)> = vec![];
        let root: Box<MaybeUninit<SyntaxMaybeUninit>> = Box::new(MaybeUninit::uninit());
        let root_ptr = Box::leak(root);
        todo.push((Vector::new(), root_ptr));

        while let Some((ctx, uninit)) = todo.pop() {
            let depth = ctx.len();
            let gens: Vec<(usize, Case)> = vec![
                (if ctx.is_empty() { 0 } else { 100 }, Case::VAR),
                (90usize.saturating_sub(depth), Case::LAM),
                (80usize.saturating_sub(2 * depth), Case::APP),
            ];
            match next_case(g, &gens) {
                Case::LAM => {
                    let n = arbitrary_name(g);
                    let mut ctx = ctx.clone();
                    ctx.push_front(n.clone());
                    let bod = Box::new(MaybeUninit::uninit());
                    let bod_ptr = Box::leak(bod);
                    todo.push((ctx, bod_ptr));
                    unsafe {
                        (*uninit).write(SyntaxMaybeUninit::Lam(n, Box::from_raw(bod_ptr)));
                    }
                }
                Case::APP => {
                    let fun = Box::new(MaybeUninit::uninit());
                    let arg = Box::new(MaybeUninit::uninit());
                    let fun_ptr = Box::leak(fun);
                    let arg_ptr = Box::leak(arg);
                    todo.push((ctx.clone(), fun_ptr));
                    todo.push((ctx.clone(), arg_ptr));
                    unsafe {
                        (*uninit).write(SyntaxMaybeUninit::App(
                            Box::from_raw(fun_ptr),
                            Box::from_raw(arg_ptr),
                        ));
                    }
                }
                Case::VAR => {
                    let idx = gen_range(g, 0..ctx.len());
                    let n = &ctx[idx];
                    // emulate shadowing behavior so that λx.λx.x always refers to the inner binder
                    let (i, _) = ctx.iter().enumerate().find(|(_, x)| *x == n).unwrap();
                    unsafe {
                        (*uninit).write(SyntaxMaybeUninit::Var(n.clone(), i));
                    }
                }
            }
        }
        let root = unsafe { Box::from_raw(root_ptr) };
        unsafe { std::mem::transmute((*root).assume_init()) }
    }

    impl Arbitrary for Syntax {
        fn arbitrary(g: &mut Gen) -> Self {
            arbitrary_syntax(g)
        }
    }

    #[quickcheck]
    fn display_syntax(syn: Syntax) -> bool {
        println!("syn: {}", syn);
        true
    }
}
