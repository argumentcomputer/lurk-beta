use std::fs::read_to_string;
use std::io;
use std::path::Path;
use std::sync::Arc;

use anyhow::{bail, Context, Result};

use log::warn;
use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Config, Editor,
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
    public_parameters::{
        nova_proof_cache, Claim, LurkCont, LurkPtr, NovaProofCache, PtrEvaluation,
    },
    store::Store,
    tag::{ContTag, ExprTag},
    writer::Write,
    Num, UInt,
    {coprocessor::Coprocessor, eval::IO},
};

use crate::cli::paths::repl_history;

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
    proof_map: NovaProofCache,
}

fn validate_rc(rc: usize) -> Result<()> {
    if rc == 0 {
        bail!("Invalid value for `rc`: 0")
    }
    Ok(())
}

impl<F: LurkField + serde::Serialize + for<'de> serde::Deserialize<'de>, C: Coprocessor<F>>
    Loader<F, C>
{
    pub fn new(store: Store<F>, env: Ptr<F>, limit: usize, rc: usize) -> Result<Loader<F, C>> {
        validate_rc(rc)?;
        Ok(Loader {
            store,
            env,
            limit,
            lang: Arc::new(Lang::<F, C>::new()),
            last_claim: None,
            rc,
            proof_map: nova_proof_cache(rc),
        })
    }

    #[inline]
    fn eval_expr(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, usize, Vec<Ptr<F>>)> {
        Ok(Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang).eval()?)
    }

    fn handle_meta_cases(&mut self, cmd: &str, args: &Ptr<F>, pwd_path: &Path) -> Result<()> {
        match cmd {
            "assert" => {
                let (first, rest) = &self.store.car_cdr(args)?;
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
                Ok(())
            }
            "assert-eq" => {
                let (first, rest) = &self.store.car_cdr(args)?;
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
                Ok(())
            }
            "assert-emitted" => {
                let (first, rest) = &self.store.car_cdr(args)?;
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
                let (mut first_emitted, mut rest_emitted) = &self.store.car_cdr(&first_io.expr)?;
                for (i, elem) in emitted.iter().enumerate() {
                    if elem != &first_emitted {
                        bail!(
                            "`assert-emitted` failed at position {i}. Expected {}, but found {}.",
                            first_emitted.fmt_to_string(&self.store),
                            elem.fmt_to_string(&self.store),
                        );
                    }
                    (first_emitted, rest_emitted) = self.store.car_cdr(&rest_emitted)?;
                }
                Ok(())
            }
            "assert-error" => {
                let (first, rest) = &self.store.car_cdr(args)?;
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
                Ok(())
            }
            "clear" => {
                self.env = self.store.nil();
                Ok(())
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
                let (first, rest) = &self.store.car_cdr(args)?;
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
                println!("{}", new_name.fmt_to_string(&self.store));
                Ok(())
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
                let (first, rest) = &self.store.car_cdr(args)?;
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
                println!("{}", new_name.fmt_to_string(&self.store));
                Ok(())
            }
            "load" => {
                let (first, rest) = &self.store.car_cdr(args)?;
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
                Ok(())
            }
            "set-env" => {
                // The state's env is set to the result of evaluating the first argument.
                let (first, rest) = &self.store.car_cdr(args)?;
                if !rest.is_nil() {
                    bail!("`set-env` accepts at most one argument")
                }
                let (first_io, ..) = self.eval_expr(*first)?;
                self.env = first_io.expr;
                Ok(())
            }
            "set-rc" => {
                let (first, rest) = &self.store.car_cdr(args)?;
                if !rest.is_nil() {
                    bail!("`set-rc` accepts at most one argument")
                }
                let rc = match first.tag {
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
                validate_rc(rc)?;
                self.rc = rc;
                // TODO: improve this
                warn!("Warning: changing `rc` resets the proof cache");
                self.proof_map = nova_proof_cache(rc);
                Ok(())
            }
            "prove" => {
                todo!()
            }
            "verify" => {
                todo!()
            }
            _ => bail!("Unsupported meta command: {cmd}"),
        }
    }

    fn handle_meta(&mut self, expr_ptr: Ptr<F>, pwd_path: &Path) -> Result<()> {
        match self.store.fetch(&expr_ptr).unwrap() {
            Expression::Cons(car, cdr) => match &self.store.fetch_symbol(&car) {
                Some(s) => self.handle_meta_cases(format!("{}", s).as_str(), &cdr, pwd_path)?,
                _ => bail!(
                    "Meta command must be a symbol. Found {}",
                    car.fmt_to_string(&self.store)
                ),
            },
            _ => bail!(
                "Unsupported meta form: {}",
                expr_ptr.fmt_to_string(&self.store)
            ),
        };
        Ok(())
    }

    fn eval_expr_and_set_last_claim(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, usize)> {
        self.eval_expr(expr_ptr).map(|(output, iterations, _)| {
            let cont = self.store.get_cont_outermost();

            let claim = Claim::PtrEvaluation::<F>(PtrEvaluation {
                expr: LurkPtr::from_ptr(&mut self.store, &expr_ptr),
                env: LurkPtr::from_ptr(&mut self.store, &self.env),
                cont: LurkCont::from_cont_ptr(&mut self.store, &cont),
                expr_out: LurkPtr::from_ptr(&mut self.store, &output.expr),
                env_out: LurkPtr::from_ptr(&mut self.store, &output.env),
                cont_out: LurkCont::from_cont_ptr(&mut self.store, &output.cont),
                status: <lurk::eval::IO<F> as Evaluable<F, Witness<F>, Coproc<F>>>::status(&output),
                // `Some(iterations)`?
                iterations: None,
            });

            self.last_claim = Some(claim);
            (output, iterations)
        })
    }

    fn handle_non_meta(&mut self, expr_ptr: Ptr<F>) -> Result<()> {
        self.eval_expr_and_set_last_claim(expr_ptr)
            .map(|(output, iterations)| {
                let prefix = if iterations != 1 {
                    format!("[{iterations} iterations] => ")
                } else {
                    "[1 iteration] => ".into()
                };

                let suffix = match output.cont.tag {
                    ContTag::Outermost | ContTag::Terminal => {
                        output.expr.fmt_to_string(&self.store)
                    }
                    ContTag::Error => "ERROR!".into(),
                    _ => format!("Computation incomplete after limit: {}", self.limit),
                };

                println!("{}{}", prefix, suffix);
            })
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

        let mut editor: Editor<InputValidator, DefaultHistory> = Editor::with_config(
            Config::builder()
                .color_mode(rustyline::ColorMode::Enabled)
                .auto_add_history(true)
                .build(),
        )?;

        editor.set_helper(Some(InputValidator {
            brackets: MatchingBracketValidator::new(),
        }));

        let history_path = &repl_history();

        #[cfg(not(target_arch = "wasm32"))]
        if history_path.exists() {
            editor.load_history(history_path)?;
        }

        loop {
            match editor.readline("> ") {
                Ok(line) => {
                    editor.save_history(history_path)?;
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
                    println!("Read line error: {err}");
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
