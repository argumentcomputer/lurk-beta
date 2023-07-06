use std::fs::read_to_string;
use std::io;
use std::path::Path;
use std::sync::Arc;

use anyhow::{bail, Context, Result};

use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

use lurk::{
    eval::{
        lang::{Coproc, Lang},
        Evaluable, Evaluator, Witness,
    },
    expr::Expression,
    field::LurkField,
    parser,
    ptr::Ptr,
    public_parameters::{Claim, LurkCont, LurkPtr, PtrEvaluation},
    store::Store,
    tag::{ContTag, ExprTag},
    writer::Write,
    Num, UInt,
    {coprocessor::Coprocessor, eval::IO},
};

use super::prove_and_verify::prove_claim;

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

pub struct Loader<F: LurkField, C: Coprocessor<F>> {
    store: Store<F>,
    env: Ptr<F>,
    limit: usize,
    lang: Arc<Lang<F, C>>,
    last_claim: Option<Claim<F>>,
    rc: usize,
}

impl<F: LurkField + serde::Serialize + for<'de> serde::Deserialize<'de>, C: Coprocessor<F>>
    Loader<F, C>
{
    pub fn new(store: Store<F>, env: Ptr<F>, limit: usize, rc: usize) -> Loader<F, C> {
        Loader {
            store,
            env,
            limit,
            lang: Arc::new(Lang::<F, C>::new()),
            last_claim: None,
            rc,
        }
    }

    #[inline]
    fn eval_expr(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, usize, Vec<Ptr<F>>)> {
        Ok(Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang).eval()?)
    }

    fn handle_meta(&mut self, expr_ptr: Ptr<F>, pwd_path: &Path) -> Result<()> {
        let res = match self.store.fetch(&expr_ptr).unwrap() {
            Expression::Cons(car, rest) => match &self.store.fetch(&car).unwrap() {
                Expression::Sym(..) => {
                    let s = &self.store.fetch_sym(&car).unwrap();
                    match format!("{}", s).as_str() {
                        "assert" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            if !rest.is_nil() {
                                bail!("`assert` accepts at most one argument")
                            }
                            let (first_io, ..) = self.eval_expr(*first)?;
                            if first_io.expr.is_nil() {
                                bail!(
                                    "`assert` failed. {} evaluates to `nil`",
                                    first.fmt_to_string(&self.store)
                                )
                            }
                            None
                        }
                        "assert-eq" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            let (second, rest) = &self.store.car_cdr(rest)?;
                            if !rest.is_nil() {
                                bail!("`assert-eq` accepts at most two arguments")
                            }
                            let (first_io, ..) = self
                                .eval_expr(*first)
                                .with_context(|| "evaluating first arg")?;
                            let (second_io, ..) = self
                                .eval_expr(*second)
                                .with_context(|| "evaluating second arg")?;
                            if !&self.store.ptr_eq(&first_io.expr, &second_io.expr)? {
                                bail!(
                                    "`assert-eq` failed. Expected:\n  {} = {}\nGot:\n  {} != {}",
                                    first.fmt_to_string(&self.store),
                                    second.fmt_to_string(&self.store),
                                    first_io.expr.fmt_to_string(&self.store),
                                    second_io.expr.fmt_to_string(&self.store)
                                )
                            }
                            None
                        }
                        "assert-emitted" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            let (second, rest) = &self.store.car_cdr(rest)?;

                            if !rest.is_nil() {
                                bail!("`assert-emitted` accepts at most two arguments")
                            }
                            let (first_io, ..) = self
                                .eval_expr(*first)
                                .with_context(|| "evaluating first arg")?;
                            let (.., emitted) = self
                                .eval_expr(*second)
                                .with_context(|| "evaluating second arg")?;
                            let (mut first_emitted, mut rest_emitted) =
                                &self.store.car_cdr(&first_io.expr)?;
                            for (i, elem) in emitted.iter().enumerate() {
                                if elem != &first_emitted {
                                    bail!(
                                            "`assert-emitted` failed at position {i}. Expected {}, but found {}.",
                                            first_emitted.fmt_to_string(&self.store),
                                            elem.fmt_to_string(&self.store),
                                        );
                                }
                                (first_emitted, rest_emitted) =
                                    self.store.car_cdr(&rest_emitted)?;
                            }
                            None
                        }
                        "assert-error" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            if !rest.is_nil() {
                                bail!("`assert-error` accepts at most one argument")
                            }
                            let (first_io, ..) = self.eval_expr(*first)?;
                            if first_io.cont.tag != ContTag::Error {
                                bail!(
                                    "`assert-error` failed. {} doesn't result on evaluation error.",
                                    first.fmt_to_string(&self.store)
                                )
                            }
                            None
                        }
                        "clear" => {
                            self.env = self.store.nil();
                            None
                        }
                        "def" => {
                            // Extends env with a non-recursive binding.
                            //
                            // This: !(:def foo (lambda () 123))
                            //
                            // Gets macroexpanded to this: (let ((foo (lambda () 123)))
                            //                               (current-env))
                            //
                            // And the state's env is set to the result.
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            let (second, rest) = &self.store.car_cdr(rest)?;
                            if !rest.is_nil() {
                                bail!("`def` accepts at most two arguments")
                            }
                            let l = &self.store.lurk_sym("let");
                            let current_env = &self.store.lurk_sym("current-env");
                            let binding = &self.store.list(&[*first, *second]);
                            let bindings = &self.store.list(&[*binding]);
                            let current_env_call = &self.store.list(&[*current_env]);
                            let expanded = &self.store.list(&[*l, *bindings, *current_env_call]);
                            let (expanded_io, ..) = self.eval_expr(*expanded)?;

                            self.env = expanded_io.expr;

                            let (new_binding, _) = &self.store.car_cdr(&expanded_io.expr)?;
                            let (new_name, _) = self.store.car_cdr(new_binding)?;
                            Some(new_name)
                        }
                        "defrec" => {
                            // Extends env with a recursive binding.
                            //
                            // This: !(:defrec foo (lambda () 123))
                            //
                            // Gets macroexpanded to this: (letrec ((foo (lambda () 123)))
                            //                               (current-env))
                            //
                            // And the state's env is set to the result.
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            let (second, rest) = &self.store.car_cdr(rest)?;
                            if !rest.is_nil() {
                                bail!("`defrec` accepts at most two arguments")
                            }
                            let l = &self.store.lurk_sym("letrec");
                            let current_env = &self.store.lurk_sym("current-env");
                            let binding = &self.store.list(&[*first, *second]);
                            let bindings = &self.store.list(&[*binding]);
                            let current_env_call = &self.store.list(&[*current_env]);
                            let expanded = &self.store.list(&[*l, *bindings, *current_env_call]);
                            let (expanded_io, ..) = self.eval_expr(*expanded)?;

                            self.env = expanded_io.expr;

                            let (new_binding_outer, _) = &self.store.car_cdr(&expanded_io.expr)?;
                            let (new_binding_inner, _) = &self.store.car_cdr(new_binding_outer)?;
                            let (new_name, _) = self.store.car_cdr(new_binding_inner)?;
                            Some(new_name)
                        }
                        "load" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            if !rest.is_nil() {
                                bail!("`load` accepts at most one argument")
                            }
                            match &self.store.fetch(first).unwrap() {
                                Expression::Str(..) => {
                                    let path = &self.store.fetch_string(first).unwrap();
                                    let joined = pwd_path.join(Path::new(&path));
                                    self.load_file(&joined)?
                                }
                                _ => bail!("Argument of `load` must be a string."),
                            }
                            io::Write::flush(&mut io::stdout()).unwrap();
                            None
                        }
                        "set-env" => {
                            // The state's env is set to the result of evaluating the first argument.
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            if !rest.is_nil() {
                                bail!("`set-env` accepts at most one argument")
                            }
                            let (first_io, ..) = self.eval_expr(*first)?;
                            self.env = first_io.expr;
                            None
                        }
                        "set-rc" => {
                            let (first, rest) = &self.store.car_cdr(&rest)?;
                            if !rest.is_nil() {
                                bail!("`set-rc` accepts at most one argument")
                            }
                            self.rc = match first.tag {
                                ExprTag::Num => match self.store.fetch_num(first).unwrap() {
                                    Num::U64(u) => *u as usize,
                                    _ => bail!(
                                        "Invalid value for `rc`: {}",
                                        first.fmt_to_string(&self.store)
                                    ),
                                },
                                ExprTag::U64 => match self.store.fetch_uint(first).unwrap() {
                                    UInt::U64(u) => u as usize,
                                },
                                _ => bail!(
                                    "Invalid value for `rc`: {}",
                                    first.fmt_to_string(&self.store)
                                ),
                            };
                            None
                        }
                        _ => {
                            bail!("Unsupported command: {}", car.fmt_to_string(&self.store));
                        }
                    }
                }
                _ => bail!("Unsupported command: {}", car.fmt_to_string(&self.store)),
            },
            _ => bail!(
                "Unsupported meta form: {}",
                expr_ptr.fmt_to_string(&self.store)
            ),
        };

        if let Some(expr) = res {
            let mut handle = io::stdout().lock();
            expr.fmt(&self.store, &mut handle)?;

            // TODO: Why is this seemingly necessary to flush?
            // This doesn't work: io::stdout().flush().unwrap();
            // We don't really want the newline.
            println!();
        };

        io::Write::flush(&mut io::stdout()).unwrap();
        Ok(())
    }

    fn handle_non_meta(&mut self, expr_ptr: Ptr<F>) -> Result<()> {
        match self.eval_expr(expr_ptr) {
            Ok((output, iterations, _)) => {
                if iterations != 1 {
                    print!("[{iterations} iterations] => ");
                } else {
                    print!("[1 iteration] => ");
                }

                match output.cont.tag {
                    ContTag::Outermost | ContTag::Terminal => {
                        let mut handle = io::stdout().lock();

                        output.expr.fmt(&self.store, &mut handle)?;

                        println!();
                    }
                    ContTag::Error => println!("ERROR!"),
                    _ => println!("Computation incomplete after limit: {}", self.limit),
                }

                let input = IO {
                    expr: expr_ptr,
                    env: self.env,
                    cont: self.store.get_cont_outermost(),
                };

                let claim = Claim::PtrEvaluation::<F>(PtrEvaluation {
                    expr: LurkPtr::from_ptr(&mut self.store, &input.expr),
                    env: LurkPtr::from_ptr(&mut self.store, &input.env),
                    cont: LurkCont::from_cont_ptr(&mut self.store, &input.cont),
                    expr_out: LurkPtr::from_ptr(&mut self.store, &output.expr),
                    env_out: LurkPtr::from_ptr(&mut self.store, &output.env),
                    cont_out: LurkCont::from_cont_ptr(&mut self.store, &output.cont),
                    status: <lurk::eval::IO<F> as Evaluable<F, Witness<F>, Coproc<F>>>::status(
                        &output,
                    ),
                    // `Some(iterations)`?
                    iterations: None,
                });

                self.last_claim = Some(claim);

                Ok(())
            }
            Err(e) => {
                println!("Evaluation error: {e}");
                Err(e)
            }
        }
    }

    fn handle_form<'a>(
        &mut self,
        input: parser::Span<'a>,
        pwd_path: &Path,
    ) -> Result<parser::Span<'a>> {
        let (input, ptr, is_meta) = self.store.read_maybe_meta(input)?;

        if is_meta {
            self.handle_meta(ptr, pwd_path)?;
        } else {
            self.handle_non_meta(ptr)?;
        }
        Ok(input)
    }

    pub fn load_file(&mut self, file_path: &Path) -> Result<()> {
        let input = read_to_string(file_path)?;
        println!("Loading {}", file_path.display());

        let mut input = parser::Span::new(&input);
        loop {
            match self.handle_form(input, file_path) {
                Ok(new_input) => input = new_input,
                Err(e) => {
                    if let Some(parser::Error::NoInput) = e.downcast_ref::<parser::Error>() {
                        // It's ok, it just means we've hit the EOF
                        return Ok(());
                    } else {
                        return Err(e);
                    }
                }
            }
        }
    }

    pub fn repl(&mut self) -> Result<()> {
        println!("Lurk REPL welcomes you.");

        let pwd_path = &std::env::current_dir()?;

        let mut editor: Editor<InputValidator, DefaultHistory> = Editor::new()?;

        loop {
            match editor.readline("> ") {
                Ok(line) =>
                {
                    #[cfg(not(target_arch = "wasm32"))]
                    match self.store.read_maybe_meta(parser::Span::new(&line)) {
                        Ok((_, expr_ptr, is_meta)) => {
                            if is_meta {
                                if let Err(e) = self.handle_meta(expr_ptr, pwd_path) {
                                    println!("!Error: {e}");
                                }
                            } else if let Err(e) = self.handle_non_meta(expr_ptr) {
                                println!("Error: {e}");
                            }
                        }
                        Err(parser::Error::NoInput) => (),
                        Err(e) => {
                            println!("Read error: {e}")
                        }
                    }
                }
                Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                    println!("Exiting...");
                    break;
                }
                Err(err) => {
                    println!("Error: {err}");
                    break;
                }
            }
        }
        Ok(())
    }

    pub fn prove_last_claim(&mut self) -> Result<()> {
        match &self.last_claim {
            Some(claim) => {
                let _ = prove_claim(claim);
                Ok(())
            }
            None => {
                bail!("No claim to prove");
            }
        }
    }
}
