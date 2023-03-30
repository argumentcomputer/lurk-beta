use crate::error::LurkError;
use crate::eval::{empty_sym_env, Evaluator, IO};
use crate::field::LurkField;
use crate::light_data::{Encodable, LightData, LightStore};
use crate::package::Package;
use crate::parser;
use crate::scalar_store::ScalarStore;
use crate::store::{ContPtr, Expression, Pointer, Ptr, Store};
use crate::tag::{ContTag, ExprTag};
use crate::writer::Write;
use anyhow::{Context, Result};
use clap::{Arg, ArgAction, Command};
use peekmore::PeekMore;
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::validate::{
    MatchingBracketValidator, ValidationContext, ValidationResult, Validator,
};
use rustyline::{Config, Editor};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};
use std::fs::{self, read_to_string};
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};
use tap::TapOptional;

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
    pub command: Option<Command>,
}

pub struct Repl<F: LurkField, T: ReplTrait<F>> {
    state: T,
    rl: Editor<InputValidator, DefaultHistory>,
    history_path: PathBuf,
    _phantom: F,
}

pub trait ReplTrait<F: LurkField> {
    fn new(s: &mut Store<F>, limit: usize, command: Option<Command>) -> Self;

    fn name() -> String;

    fn prompt(&mut self) -> String;

    fn process_line(&mut self, line: String) -> String;

    fn command() -> Command;

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
    ) -> Result<(IO<F>, IO<F>, usize)>;
}

impl<F: LurkField, T: ReplTrait<F>> Repl<F, T> {
    pub fn new(s: &mut Store<F>, limit: usize, command: Option<Command>) -> Result<Self> {
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
        let mut rl = Editor::with_config(config)?;
        rl.set_helper(Some(h));
        if history_path.exists() {
            rl.load_history(&history_path)?;
        }

        let state = T::new(s, limit, command);
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

pub fn repl_cli<F: LurkField, T: ReplTrait<F>>() -> Result<()> {
    let command = T::command();
    let matches = command.clone().get_matches();

    let lurk_file = matches.get_one::<String>("lurk_file");
    let light_store = matches.get_one::<String>("lightstore");

    repl_aux::<_, F, T>(lurk_file, light_store, Some(command))
}

pub fn repl<F: LurkField, T: ReplTrait<F>, P: AsRef<Path>>(lurk_file: Option<P>) -> Result<()> {
    repl_aux::<_, F, T>(lurk_file, None, None)
}

fn repl_aux<P: AsRef<Path>, F: LurkField, T: ReplTrait<F>>(
    lurk_file: Option<P>,
    light_store: Option<P>,
    command: Option<Command>,
) -> Result<()> {
    let received_light_store = light_store.is_some();
    let mut s = light_store
        .and_then(|light_store_path| fs::read(light_store_path).ok())
        .and_then(|bytes| LightData::de(&bytes).ok())
        .and_then(|ld| Encodable::de(&ld).ok())
        .and_then(|store: LightStore<F>| ScalarStore::try_from(store).ok())
        .and_then(|mut scalar_store: ScalarStore<F>| scalar_store.to_store())
        .tap_none(|| {
            if received_light_store {
                eprintln!("Failed to load light store. Starting with empty store.")
            }
        })
        .unwrap_or_default();
    let s_ref = &mut s;
    let limit = 100_000_000;
    let repl: Repl<F, T> = Repl::new(s_ref, limit, command)?;

    run_repl(s_ref, repl, lurk_file)
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
        let line = repl
            .rl
            .readline(&repl.state.prompt())
            .map(|line| repl.state.process_line(line));
        match line {
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
    pub fn new(s: &mut Store<F>, limit: usize, command: Option<Command>) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
            command,
        }
    }
    pub fn eval_expr(
        &mut self,
        expr: Ptr<F>,
        store: &mut Store<F>,
    ) -> Result<(Ptr<F>, usize, ContPtr<F>, Vec<Ptr<F>>)> {
        let (io, iterations, emitted) = Evaluator::new(expr, self.env, store, self.limit).eval()?;

        let IO {
            expr: result,
            env: _env,
            cont: next_cont,
        } = io;

        if next_cont == store.get_cont_error() {
            Err(LurkError::IO(io))?
        } else {
            Ok((result, iterations, next_cont, emitted))
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
            self.handle_non_meta(store, ptr, update_env).map(|_| ())
        }
    }
}

impl<F: LurkField> ReplTrait<F> for ReplState<F> {
    fn new(s: &mut Store<F>, limit: usize, command: Option<Command>) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
            command,
        }
    }

    fn name() -> String {
        "Lurk REPL".into()
    }

    fn prompt(&mut self) -> String {
        "> ".into()
    }

    fn process_line(&mut self, line: String) -> String {
        line
    }
    fn command() -> Command {
        Command::new("Lurk REPL")
            .arg(
                Arg::new("lurk_file")
                    .help("Lurk file to run")
                    .action(ArgAction::Set)
                    .value_name("LURKFILE")
                    .index(1)
                    .help("Specifies the path of a lurk file to run"),
            )
            .arg(
                Arg::new("lightstore")
                    .long("lightstore")
                    .value_parser(clap::builder::NonEmptyStringValueParser::new())
                    .action(ArgAction::Set)
                    .value_name("LIGHTSTORE")
                    .help("Specifies the lightstore file path"),
            )
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
                                assert!(self.clone().eval_expr(first, store).is_err());

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

            // TODO: Why is this seemingly necessary to flush?
            // This doesn't work: io::stdout().flush().unwrap();
            // We don't really want the newline.
            println!();
        };

        io::stdout().flush().unwrap();
        Ok(())
    }

    fn handle_non_meta(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        update_env: bool,
    ) -> Result<(IO<F>, IO<F>, usize)> {
        match Evaluator::new(expr_ptr, self.env, store, self.limit).eval() {
            Ok((output, iterations, _emitted)) => {
                let IO {
                    expr: result,
                    env: _env,
                    cont: next_cont,
                } = output;
                {
                    if !update_env {
                        print!("[{iterations} iterations] => ");
                    }

                    let input = IO {
                        expr: expr_ptr,
                        env: self.env,
                        cont: store.get_cont_terminal(),
                    };

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

                    Ok((input, output, 12345))
                }
            }

            Err(e) => {
                eprintln!("Evaluation error: {e:?}");
                Err(e.into())
            }
        }
    }
}
