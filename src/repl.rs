use crate::eval::{empty_sym_env, Evaluator, IO};
use crate::field::LurkField;
use crate::package::Package;
use crate::parser;
use crate::store::{ContPtr, Expression, Pointer, Ptr, Store};
use crate::tag::{ContTag, ExprTag};
use crate::writer::Write;
use anyhow::{anyhow, Context, Result};
use peekmore::PeekMore;
use rustyline::error::ReadlineError;
use rustyline::validate::{
    MatchingBracketValidator, ValidationContext, ValidationResult, Validator,
};
use rustyline::{Config, Editor};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};
use std::fs::read_to_string;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

#[derive(Clone)]
pub struct ReplState<F: LurkField> {
    pub env: Ptr<F>,
    pub limit: usize,
}

pub struct Repl<F: LurkField, T: ReplTrait<F>> {
    state: T,
    rl: Editor<InputValidator>,
    history_path: PathBuf,
    _phantom: F,
}

pub trait ReplTrait<F: LurkField> {
    fn new(s: &mut Store<F>, limit: usize) -> Self;

    fn name() -> String;

    fn prompt(&self) -> String;

    fn handle_run<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
    ) -> Result<()>;

    /// Returns two bools.
    /// First bool is true if input is a command.
    /// Second bool is true if processing should continue.
    fn maybe_handle_command(
        &mut self,
        store: &mut Store<F>,
        line: &str,
        package: &Package,
    ) -> Result<(bool, bool)>;

    fn handle_meta<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        package: &Package,
        p: P,
    ) -> Result<()>;

    fn handle_non_meta(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        update_env: bool,
    ) -> Result<()>;
}

impl<F: LurkField, T: ReplTrait<F>> Repl<F, T> {
    pub fn new(s: &mut Store<F>, limit: usize) -> Result<Self> {
        let history_path = dirs::home_dir()
            .expect("missing home directory")
            .join(".lurk-history");

        let h = InputValidator {
            brackets: MatchingBracketValidator::new(),
        };
        let config = Config::builder()
            .color_mode(rustyline::ColorMode::Enabled)
            .auto_add_history(true)
            .build();
        let mut rl = Editor::with_config(config);
        rl.set_helper(Some(h));
        if history_path.exists() {
            rl.load_history(&history_path)?;
        }

        let state = T::new(s, limit);
        Ok(Self {
            state,
            rl,
            history_path,
            _phantom: Default::default(),
        })
    }
    pub fn save_history(&mut self) -> Result<()> {
        self.rl.save_history(&self.history_path)?;
        Ok(())
    }
}

pub fn repl<P: AsRef<Path>, F: LurkField, T: ReplTrait<F>>(lurk_file: Option<P>) -> Result<()> {
    let s = &mut Store::<F>::default();
    let limit = 100_000_000;
    let repl: Repl<F, T> = Repl::new(s, limit)?;

    run_repl(s, repl, lurk_file)
}

// For the moment, input must be on a single line.
pub fn run_repl<P: AsRef<Path>, F: LurkField, T: ReplTrait<F>>(
    s: &mut Store<F>,
    mut repl: Repl<F, T>,
    lurk_file: Option<P>,
) -> Result<()> {
    let package = Package::lurk();

    if lurk_file.is_none() {
        let name = T::name();
        eprintln!("{name} welcomes you.");
    }

    {
        if let Some(lurk_file) = lurk_file {
            repl.state.handle_run(s, &lurk_file, &package).unwrap();
            return Ok(());
        }
    }

    let pwd_path = std::env::current_dir().unwrap();
    let p: &Path = pwd_path.as_ref();
    loop {
        match repl.rl.readline(&repl.state.prompt()) {
            Ok(line) => {
                repl.save_history()?;

                let result = repl.state.maybe_handle_command(s, &line, &package);

                match result {
                    Ok((handled_command, should_continue)) if handled_command => {
                        if should_continue {
                            continue;
                        } else {
                            break;
                        };
                    }
                    Ok(_) => (),
                    Err(e) => {
                        eprintln!("Error when handling {line}: {e:?}");
                        continue;
                    }
                };

                let mut chars = line.chars().peekmore();

                match s.read_maybe_meta(&mut chars, &package) {
                    Ok((expr, is_meta)) => {
                        if is_meta {
                            if let Err(e) = repl.state.handle_meta(s, expr, &package, p) {
                                eprintln!("!Error: {e:?}");
                            };
                            continue;
                        } else {
                            if let Err(e) = repl.state.handle_non_meta(s, expr, false) {
                                eprintln!("REPL Error: {e:?}");
                            }

                            continue;
                        }
                    }
                    Err(parser::Error::NoInput) => {
                        continue;
                    }
                    Err(e) => {
                        eprintln!("Read error: {e:?}")
                    }
                }
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                eprintln!("Exiting...");
                break;
            }
            Err(err) => {
                eprintln!("Error: {err:?}");
                break;
            }
        }
    }

    Ok(())
}

impl<F: LurkField> ReplState<F> {
    pub fn new(s: &mut Store<F>, limit: usize) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
        }
    }
    pub fn eval_expr(
        &mut self,
        expr: Ptr<F>,
        store: &mut Store<F>,
    ) -> Result<(Ptr<F>, usize, ContPtr<F>, Vec<Ptr<F>>)> {
        let (
            IO {
                expr: result,
                env: _env,
                cont: next_cont,
            },
            iterations,
            emitted,
        ) = Evaluator::new(expr, self.env, store, self.limit).eval()?;

        if next_cont == store.get_cont_terminal() {
            Ok((result, iterations, next_cont, emitted))
        } else {
            Err(anyhow!(
                "Error while evaluating: {}",
                expr.fmt_to_string(&store)
            ))
        }
    }

    pub fn maybe_handle_command(
        &mut self,
        store: &mut Store<F>,
        line: &str,
        package: &Package,
    ) -> Result<(bool, bool)> {
        let mut chars = line.chars().peekmore();
        let maybe_command = store.read_next(&mut chars, package);

        let result = match &maybe_command {
            Ok(maybe_command) => match maybe_command.tag() {
                ExprTag::Sym => {
                    if let Some(key_string) = store
                        .fetch(maybe_command)
                        .unwrap()
                        .as_simple_keyword_string()
                    {
                        match key_string.as_str() {
                            "QUIT" => (true, false),
                            "LOAD" => match store.read_string(&mut chars) {
                                Ok(s) => match s.tag() {
                                    ExprTag::Str => {
                                        let file_path = store.fetch(&s).unwrap();
                                        let file_path = PathBuf::from(file_path.as_str().unwrap());
                                        self.handle_load(store, file_path, package)?;
                                        (true, true)
                                    }
                                    other => {
                                        anyhow::bail!("No valid path found: {:?}", other);
                                    }
                                },
                                Err(_) => {
                                    anyhow::bail!("No path found");
                                }
                            },
                            "RUN" => {
                                if let Ok(s) = store.read_string(&mut chars) {
                                    if s.tag() == ExprTag::Str {
                                        let file_path = store.fetch(&s).unwrap();
                                        let file_path = PathBuf::from(file_path.as_str().unwrap());
                                        self.handle_run(store, &file_path, package)?;
                                    }
                                }
                                (true, true)
                            }
                            "CLEAR" => {
                                self.env = empty_sym_env(store);
                                (true, true)
                            }
                            _ => (true, true),
                        }
                    } else {
                        (false, true)
                    }
                }
                _ => (false, true),
            },
            _ => (false, true),
        };

        Ok(result)
    }

    pub fn handle_load<P: AsRef<Path>>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
    ) -> Result<()> {
        eprintln!("Loading from {}.", file_path.as_ref().to_str().unwrap());
        self.handle_file(store, file_path.as_ref(), package, true)
    }

    pub fn handle_file<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
        update_env: bool,
    ) -> Result<()> {
        let file_path = file_path;

        let input = read_to_string(file_path)?;
        eprintln!(
            "Read from {}: {}",
            file_path.as_ref().to_str().unwrap(),
            input
        );
        let mut chars = input.chars().peekmore();

        loop {
            if let Err(e) = self.handle_form(
                store,
                &mut chars,
                package,
                // use this file's dir as pwd for further loading
                file_path.as_ref().parent().unwrap(),
                update_env,
            ) {
                if let Some(parser::Error::NoInput) = e.downcast_ref::<parser::Error>() {
                    // It's ok, it just means we've hit the EOF
                    return Ok(());
                } else {
                    return Err(e);
                }
            }
        }
    }

    fn handle_form<P: AsRef<Path> + Copy, T: Iterator<Item = char>>(
        &mut self,
        store: &mut Store<F>,
        chars: &mut peekmore::PeekMoreIterator<T>,
        package: &Package,
        pwd: P,
        update_env: bool,
    ) -> Result<()> {
        let (ptr, is_meta) = store.read_maybe_meta(chars, package)?;

        if is_meta {
            let pwd: &Path = pwd.as_ref();
            self.handle_meta(store, ptr, package, pwd)
        } else {
            self.handle_non_meta(store, ptr, update_env)
        }
    }
}

impl<F: LurkField> ReplTrait<F> for ReplState<F> {
    fn new(s: &mut Store<F>, limit: usize) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
        }
    }

    fn name() -> String {
        "Lurk REPL".into()
    }

    fn prompt(&self) -> String {
        "> ".into()
    }

    fn handle_run<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
    ) -> Result<()> {
        eprintln!("Running from {}.", file_path.as_ref().to_str().unwrap());
        self.handle_file(store, file_path, package, false)
    }

    fn maybe_handle_command(
        &mut self,
        store: &mut Store<F>,
        line: &str,
        package: &Package,
    ) -> Result<(bool, bool)> {
        let mut chars = line.chars().peekmore();
        let maybe_command = store.read_next(&mut chars, package);

        let result = match &maybe_command {
            Ok(maybe_command) => match maybe_command.tag() {
                ExprTag::Sym => {
                    if let Some(key_string) = store
                        .fetch(maybe_command)
                        .unwrap()
                        .as_simple_keyword_string()
                    {
                        match key_string.as_str() {
                            "QUIT" => (true, false),
                            "LOAD" => match store.read_string(&mut chars) {
                                Ok(s) => match s.tag() {
                                    ExprTag::Str => {
                                        let file_path = store.fetch(&s).unwrap();
                                        let file_path = PathBuf::from(file_path.as_str().unwrap());
                                        self.handle_load(store, file_path, package)?;
                                        (true, true)
                                    }
                                    other => {
                                        anyhow::bail!("No valid path found: {:?}", other);
                                    }
                                },
                                Err(_) => {
                                    anyhow::bail!("No path found");
                                }
                            },
                            "RUN" => {
                                if let Ok(s) = store.read_string(&mut chars) {
                                    if s.tag() == ExprTag::Str {
                                        let file_path = store.fetch(&s).unwrap();
                                        let file_path = PathBuf::from(file_path.as_str().unwrap());
                                        self.handle_run(store, &file_path, package)?;
                                    }
                                }
                                (true, true)
                            }
                            "CLEAR" => {
                                self.env = empty_sym_env(store);
                                (true, true)
                            }
                            _ => (true, true),
                        }
                    } else {
                        (false, true)
                    }
                }
                _ => (false, true),
            },
            _ => (false, true),
        };

        Ok(result)
    }

    fn handle_meta<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        package: &Package,
        p: P,
    ) -> Result<()> {
        let expr = store.fetch(&expr_ptr).unwrap();

        let res = match expr {
            Expression::Cons(car, rest) => match &store.fetch(&car).unwrap() {
                Expression::Sym(s) => {
                    if let Some(name) = s.simple_keyword_name() {
                        match name.as_str() {
                            "ASSERT" => {
                                let (first, rest) = store.car_cdr(&rest)?;
                                assert!(rest.is_nil());
                                let (first_evaled, _, _, _) = self
                                    .eval_expr(first, store)
                                    .with_context(|| "evaluating first arg")
                                    .unwrap();
                                assert!(!first_evaled.is_nil());
                                None
                            }
                            "ASSERT-EQ" => {
                                let (first, rest) = store.car_cdr(&rest)?;
                                let (second, rest) = store.car_cdr(&rest)?;
                                assert!(rest.is_nil());
                                let (first_evaled, _, _, _) = self
                                    .eval_expr(first, store)
                                    .with_context(|| "evaluating first arg")
                                    .unwrap();
                                let (second_evaled, _, _, _) = self
                                    .eval_expr(second, store)
                                    .with_context(|| "evaluating second arg")
                                    .unwrap();
                                assert!(
                                    store.ptr_eq(&first_evaled, &second_evaled).unwrap(),
                                    "Assertion failed {:?} = {:?},\n {:?} != {:?}",
                                    first.fmt_to_string(store),
                                    second.fmt_to_string(store),
                                    first_evaled.fmt_to_string(store),
                                    second_evaled.fmt_to_string(store)
                                );
                                None
                            }
                            "ASSERT-EMITTED" => {
                                let (first, rest) = store.car_cdr(&rest)?;
                                let (second, rest) = store.car_cdr(&rest)?;

                                assert!(rest.is_nil());
                                let (first_evaled, _, _, _) =
                                    self.clone().eval_expr(first, store)?;
                                let (_, _, _, emitted) = self
                                    .eval_expr(second, store)
                                    .with_context(|| "evaluating first arg")
                                    .unwrap();
                                let (mut first_emitted, mut rest_emitted) =
                                    store.car_cdr(&first_evaled)?;
                                for (i, elem) in emitted.iter().enumerate() {
                                    if elem != &first_emitted {
                                        panic!(
                                            ":ASSERT-EMITTED failed at position {}. Expected {}, but found {}.",
                                            i,
                                            first_emitted.fmt_to_string(store),
                                            elem.fmt_to_string(store),
                                        );
                                    }
                                    (first_emitted, rest_emitted) = store.car_cdr(&rest_emitted)?;
                                }
                                None
                            }
                            "ASSERT-ERROR" => {
                                let (first, rest) = store.car_cdr(&rest)?;

                                assert!(rest.is_nil());
                                let (_, _, continuation, _) = self
                                    .clone()
                                    .eval_expr(first, store)
                                    .with_context(|| "evaluating first arg")
                                    .unwrap();
                                assert!(continuation.is_error());
                                None
                            }
                            "CLEAR" => {
                                self.env = empty_sym_env(store);
                                None
                            }
                            "DEF" => {
                                // Extends env with a non-recursive binding.
                                //
                                // This: !(:def foo (lambda () 123))
                                //
                                // Gets macroexpanded to this: (let ((foo (lambda () 123)))
                                //                               (current-env))
                                //
                                // And the state's env is set to the result.
                                let (first, rest) = store.car_cdr(&rest)?;
                                let (second, rest) = store.car_cdr(&rest)?;
                                assert!(rest.is_nil());
                                let l = store.sym("LET");
                                let current_env = store.sym("CURRENT-ENV");
                                let binding = store.list(&[first, second]);
                                let bindings = store.list(&[binding]);
                                let current_env_call = store.list(&[current_env]);
                                let expanded = store.list(&[l, bindings, current_env_call]);
                                let (expanded_evaled, _, _, _) = self.eval_expr(expanded, store)?;

                                self.env = expanded_evaled;

                                let (new_binding, _) = store.car_cdr(&expanded_evaled)?;
                                let (new_name, _) = store.car_cdr(&new_binding)?;
                                Some(new_name)
                            }
                            "DEFREC" => {
                                // Extends env with a recursive binding.
                                //
                                // This: !(:def foo (lambda () 123))
                                //
                                // Gets macroexpanded to this: (letrec ((foo (lambda () 123)))
                                //                               (current-env))
                                //
                                // And the state's env is set to the result.
                                let (first, rest) = store.car_cdr(&rest)?;
                                let (second, rest) = store.car_cdr(&rest)?;
                                assert!(rest.is_nil());
                                let l = store.sym("LETREC");
                                let current_env = store.sym("CURRENT-ENV");
                                let binding = store.list(&[first, second]);
                                let bindings = store.list(&[binding]);
                                let current_env_call = store.list(&[current_env]);
                                let expanded = store.list(&[l, bindings, current_env_call]);
                                let (expanded_evaled, _, _, _) = self.eval_expr(expanded, store)?;

                                self.env = expanded_evaled;

                                let (new_binding_outer, _) = store.car_cdr(&expanded_evaled)?;
                                let (new_binding_inner, _) = store.car_cdr(&new_binding_outer)?;
                                let (new_name, _) = store.car_cdr(&new_binding_inner)?;
                                Some(new_name)
                            }
                            "LOAD" => {
                                match store.fetch(&store.car(&rest)?).unwrap() {
                                    Expression::Str(path) => {
                                        let joined = p.as_ref().join(Path::new(&path));
                                        self.handle_load(store, &joined, package)?
                                    }
                                    _ => panic!("Argument to :LOAD must be a string."),
                                }
                                io::stdout().flush().unwrap();
                                None
                            }
                            "RUN" => {
                                // Running and loading are equivalent, except that :RUN does not modify the env.
                                match store.fetch(&store.car(&rest)?).unwrap() {
                                    Expression::Str(path) => {
                                        let joined = p.as_ref().join(Path::new(&path));
                                        self.handle_run(store, &joined, package)?
                                    }
                                    _ => panic!("Argument to :RUN must be a string."),
                                }
                                io::stdout().flush().unwrap();
                                None
                            }
                            "SET-ENV" => {
                                // The state's env is set to the result of evaluating the first argument.
                                let (first, rest) = store.car_cdr(&rest)?;
                                assert!(rest.is_nil());
                                let (first_evaled, _, _, _) = self.eval_expr(first, store)?;
                                self.env = first_evaled;
                                None
                            }
                            _ => {
                                panic!("!({} ...) is unsupported.", s.name());
                            }
                        }
                    } else {
                        panic!("!({} ...) is unsupported.", s.name());
                    }
                }
                _ => panic!("!(<COMMAND> ...) must be a (:keyword) symbol."),
            },
            _ => panic!("!<COMMAND> form is unsupported."),
        };

        if let Some(expr) = res {
            let mut handle = io::stdout().lock();
            expr.fmt(store, &mut handle)?;
            println!();
        };
        Ok(())
    }

    fn handle_non_meta(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        update_env: bool,
    ) -> Result<()> {
        match Evaluator::new(expr_ptr, self.env, store, self.limit).eval() {
            Ok((
                IO {
                    expr: result,
                    env: _env,
                    cont: next_cont,
                },
                iterations,
                _emitted,
            )) => {
                if !update_env {
                    print!("[{iterations} iterations] => ");
                }

                match next_cont.tag() {
                    ContTag::Outermost | ContTag::Terminal => {
                        let mut handle = io::stdout().lock();

                        // We are either loading/running and update the env, or evaluating and don't.
                        if update_env {
                            self.env = result
                        } else {
                            result.fmt(store, &mut handle)?;

                            println!();
                        }
                    }
                    ContTag::Error => println!("ERROR!"),
                    _ => println!("Computation incomplete after limit: {}", self.limit),
                }

                Ok(())
            }
            Err(e) => {
                eprintln!("Evaluation error: {e:?}");
                Err(e.into())
            }
        }
    }
}
