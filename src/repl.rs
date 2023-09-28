use crate::coprocessor::Coprocessor;
use crate::error::LurkError;
use crate::eval::{empty_sym_env, lang::Lang, Evaluator, IO};
use crate::expr::Expression;
use crate::field::LurkField;
use crate::ptr::{ContPtr, Ptr};
use crate::state::State;
use crate::store::Store;
use crate::symbol::Symbol;
use crate::tag::ContTag;
use crate::writer::Write;
use crate::z_data::{from_z_data, ZData};
use crate::z_store::ZStore;
use crate::{lurk_sym_ptr, parser};
use anyhow::{bail, Context, Error, Result};
use clap::{Arg, ArgAction, Command};
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::validate::{
    MatchingBracketValidator, ValidationContext, ValidationResult, Validator,
};
use rustyline::{Config, Editor};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};
use std::fs::{self, read_to_string};
use std::io::{self, Write as _};
use std::marker::PhantomData;
use std::path::Path;
#[cfg(not(target_arch = "wasm32"))]
use std::path::PathBuf;
use std::sync::Arc;
use std::{cell::RefCell, rc::Rc};
use tap::TapOptional;

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

#[derive(Clone, Debug)]
pub struct ReplState<F: LurkField, C: Coprocessor<F>> {
    pub env: Ptr<F>,
    pub limit: usize,
    pub command: Option<Command>,
    pub lang: Arc<Lang<F, C>>,
}

#[derive(Debug)]
pub struct Repl<F: LurkField, T: ReplTrait<F, C>, C: Coprocessor<F>> {
    state: T,
    rl: Editor<InputValidator, DefaultHistory>,
    #[cfg(not(target_arch = "wasm32"))]
    history_path: PathBuf,
    _phantom: PhantomData<(F, C)>,
}

pub trait ReplTrait<F: LurkField, C: Coprocessor<F>> {
    fn new(s: &Store<F>, limit: usize, command: Option<Command>, lang: Lang<F, C>) -> Self;

    fn name() -> String;

    fn prompt(&mut self) -> String;

    fn process_line(&mut self, line: String) -> String;

    fn command() -> Command;

    fn handle_form<'a, P: AsRef<Path> + Copy>(
        &mut self,
        store: &Store<F>,
        state: Rc<RefCell<State>>,
        input: parser::Span<'a>,
        pwd: P,
    ) -> Result<parser::Span<'a>> {
        let (input, ptr, is_meta) = store.read_maybe_meta_with_state(state.clone(), input)?;

        if is_meta {
            let pwd: &Path = pwd.as_ref();
            self.handle_meta(store, state, ptr, pwd)?;
            Ok(input)
        } else {
            self.handle_non_meta(store, &state.borrow(), ptr)
                .map(|_| ())?;
            Ok(input)
        }
    }

    fn handle_load<P: AsRef<Path>>(
        &mut self,
        store: &Store<F>,
        state: Rc<RefCell<State>>,
        file_path: P,
    ) -> Result<()> {
        eprintln!("Loading from {}.", file_path.as_ref().to_str().unwrap());
        self.handle_file(store, state, file_path.as_ref())
    }

    fn handle_file<P: AsRef<Path> + Copy>(
        &mut self,
        store: &Store<F>,
        state: Rc<RefCell<State>>,
        file_path: P,
    ) -> Result<()> {
        let input = read_to_string(file_path)?;
        eprintln!(
            "Read from {}: {}",
            file_path.as_ref().to_str().unwrap(),
            input
        );

        let mut input = parser::Span::new(&input);
        loop {
            match self.handle_form(
                store,
                state.clone(),
                input,
                // use this file's dir as pwd for further loading
                file_path.as_ref().parent().unwrap(),
            ) {
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

    fn handle_meta<P: AsRef<Path> + Copy>(
        &mut self,
        store: &Store<F>,
        state: Rc<RefCell<State>>,
        expr_ptr: Ptr<F>,
        p: P,
    ) -> Result<()>;

    fn handle_non_meta(
        &mut self,
        store: &Store<F>,
        state: &State,
        expr_ptr: Ptr<F>,
    ) -> Result<(IO<F>, IO<F>, usize)>;
}

impl<F: LurkField, T: ReplTrait<F, C>, C: Coprocessor<F>> Repl<F, T, C> {
    pub fn new(
        s: &Store<F>,
        limit: usize,
        command: Option<Command>,
        lang: Lang<F, C>,
    ) -> Result<Self> {
        #[cfg(not(target_arch = "wasm32"))]
        let history_path = home::home_dir()
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

        #[cfg(not(target_arch = "wasm32"))]
        if history_path.exists() {
            rl.load_history(&history_path)?;
        }

        let state = T::new(s, limit, command, lang);
        Ok(Self {
            state,
            rl,
            #[cfg(not(target_arch = "wasm32"))]
            history_path,
            _phantom: Default::default(),
        })
    }
    #[cfg(not(target_arch = "wasm32"))]
    pub fn save_history(&mut self) -> Result<()> {
        self.rl.save_history(&self.history_path)?;
        Ok(())
    }
}

pub fn repl_cli<
    F: LurkField + for<'de> serde::Deserialize<'de>,
    T: ReplTrait<F, C>,
    C: Coprocessor<F>,
>(
    lang: Lang<F, C>,
) -> Result<()> {
    let command = T::command();
    let matches = command.clone().get_matches();

    let lurk_file = matches.get_one::<String>("lurk_file");
    let z_store = matches.get_one::<String>("zstore");

    repl_aux::<_, F, T, C>(lurk_file, z_store, Some(command), lang)
}

pub fn repl<
    F: LurkField + for<'de> serde::Deserialize<'de>,
    T: ReplTrait<F, C>,
    P: AsRef<Path>,
    C: Coprocessor<F>,
>(
    lurk_file: Option<P>,
    lang: Lang<F, C>,
) -> Result<()> {
    repl_aux::<_, F, T, C>(lurk_file, None, None, lang)
}

fn repl_aux<
    P: AsRef<Path>,
    F: LurkField + for<'de> serde::Deserialize<'de>,
    T: ReplTrait<F, C>,
    C: Coprocessor<F>,
>(
    lurk_file: Option<P>,
    z_store: Option<P>,
    command: Option<Command>,
    lang: Lang<F, C>,
) -> Result<()> {
    let received_z_store = z_store.is_some();
    let mut s = z_store
        .and_then(|z_store_path| fs::read(z_store_path).ok())
        .and_then(|bytes| ZData::from_bytes(&bytes).ok())
        .and_then(|zd| from_z_data(&zd).ok())
        .map(|z_store: ZStore<F>| ZStore::to_store(&z_store))
        .tap_none(|| {
            if received_z_store {
                eprintln!("Failed to load ZStore. Starting with empty store.")
            }
        })
        .unwrap_or_default();
    let s_ref = &mut s;
    let limit = 100_000_000;
    let repl: Repl<F, T, C> = Repl::new(s_ref, limit, command, lang)?;

    run_repl(s_ref, repl, lurk_file)
}

// For the moment, input must be on a single line.
pub fn run_repl<P: AsRef<Path>, F: LurkField, T: ReplTrait<F, C>, C: Coprocessor<F>>(
    s: &Store<F>,
    mut repl: Repl<F, T, C>,
    lurk_file: Option<P>,
) -> Result<()> {
    if lurk_file.is_none() {
        let name = T::name();
        eprintln!("{name} welcomes you.");
    }
    let state = State::init_lurk_state().rccell();

    {
        if let Some(lurk_file) = lurk_file {
            repl.state.handle_load(s, state, &lurk_file).unwrap();
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
                let input = parser::Span::new(&line);
                #[cfg(not(target_arch = "wasm32"))]
                repl.save_history()?;

                match s.read_maybe_meta_with_state(state.clone(), input) {
                    Ok((_, expr, is_meta)) => {
                        if is_meta {
                            if let Err(e) = repl.state.handle_meta(s, state.clone(), expr, p) {
                                eprintln!("!Error: {e}");
                            };
                            continue;
                        } else {
                            if let Err(e) = repl.state.handle_non_meta(s, &state.borrow(), expr) {
                                eprintln!("REPL Error: {e}");
                            }

                            continue;
                        }
                    }
                    Err(parser::Error::NoInput) => {
                        continue;
                    }
                    Err(e) => {
                        eprintln!("Read error: {e}")
                    }
                }
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                eprintln!("Exiting...");
                break;
            }
            Err(err) => {
                eprintln!("Error: {err}");
                break;
            }
        }
    }

    Ok(())
}

impl<F: LurkField, C: Coprocessor<F>> ReplState<F, C> {
    pub fn new(s: &Store<F>, limit: usize, command: Option<Command>, lang: Lang<F, C>) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
            command,
            lang: Arc::new(lang),
        }
    }
    pub fn eval_expr(
        &mut self,
        expr: Ptr<F>,
        store: &Store<F>,
    ) -> Result<(Ptr<F>, usize, ContPtr<F>, Vec<Ptr<F>>)> {
        let (io, iterations, emitted) =
            Evaluator::new(expr, self.env, store, self.limit, &self.lang).eval()?;

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
}

impl<F: LurkField, C: Coprocessor<F>> ReplTrait<F, C> for ReplState<F, C> {
    fn new(s: &Store<F>, limit: usize, command: Option<Command>, lang: Lang<F, C>) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
            command,
            lang: Arc::new(lang),
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
                Arg::new("zstore")
                    .long("zstore")
                    .value_parser(clap::builder::NonEmptyStringValueParser::new())
                    .action(ArgAction::Set)
                    .value_name("ZSTORE")
                    .help("Specifies the zstore file path"),
            )
    }

    fn handle_meta<P: AsRef<Path> + Copy>(
        &mut self,
        store: &Store<F>,
        state: Rc<RefCell<State>>,
        expr_ptr: Ptr<F>,
        p: P,
    ) -> Result<()> {
        let expr = store.fetch(&expr_ptr).unwrap();

        let res = match expr {
            Expression::Cons(car, rest) => match &store.fetch(&car).unwrap() {
                Expression::Sym(..) => {
                    let s: Symbol = store
                        .fetch_sym(&car)
                        .ok_or(Error::msg("handle_meta fetch symbol"))?;
                    match s.name()? {
                        "assert" => {
                            let (first, rest) = store.car_cdr(&rest)?;
                            assert!(rest.is_nil());
                            let (first_evaled, _, _, _) = self
                                .eval_expr(first, store)
                                .with_context(|| "evaluating first arg")
                                .unwrap();
                            assert!(!first_evaled.is_nil());
                            None
                        }
                        "assert-eq" => {
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
                                first.fmt_to_string(store, &state.borrow()),
                                second.fmt_to_string(store, &state.borrow()),
                                first_evaled.fmt_to_string(store, &state.borrow()),
                                second_evaled.fmt_to_string(store, &state.borrow())
                            );
                            None
                        }
                        "assert-emitted" => {
                            let (first, rest) = store.car_cdr(&rest)?;
                            let (second, rest) = store.car_cdr(&rest)?;

                            assert!(rest.is_nil());
                            let (first_evaled, _, _, _) = self.clone().eval_expr(first, store)?;
                            let (_, _, _, emitted) = self
                                .eval_expr(second, store)
                                .with_context(|| "evaluating first arg")
                                .unwrap();
                            let (mut first_emitted, mut rest_emitted) =
                                store.car_cdr(&first_evaled)?;
                            for (i, elem) in emitted.iter().enumerate() {
                                assert_eq!(elem , &first_emitted,
                                            ":ASSERT-EMITTED failed at position {}. Expected {}, but found {}.",
                                            i,
                                            first_emitted.fmt_to_string(store, &state.borrow()),
                                            elem.fmt_to_string(store, &state.borrow()),
                                        );
                                (first_emitted, rest_emitted) = store.car_cdr(&rest_emitted)?;
                            }
                            None
                        }
                        "assert-error" => {
                            let (first, rest) = store.car_cdr(&rest)?;

                            assert!(rest.is_nil());
                            assert!(self.clone().eval_expr(first, store).is_err());

                            None
                        }
                        "clear" => {
                            self.env = empty_sym_env(store);
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
                            let (first, rest) = store.car_cdr(&rest)?;
                            let (second, rest) = store.car_cdr(&rest)?;
                            assert!(rest.is_nil());
                            let l = lurk_sym_ptr!(store, let_);
                            let current_env = lurk_sym_ptr!(store, current_env);
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
                        "defrec" => {
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
                            let l = lurk_sym_ptr!(store, letrec);
                            let current_env = lurk_sym_ptr!(store, current_env);
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
                        "load" => {
                            let car = &store.car(&rest)?;
                            match store.fetch(car).unwrap() {
                                Expression::Str(..) => {
                                    let path: String = store
                                        .fetch_string(car)
                                        .ok_or(Error::msg("handle_meta fetch_string"))?;
                                    let joined = p.as_ref().join(Path::new(&path));
                                    self.handle_load(store, state.clone(), &joined)?
                                }
                                _ => bail!("Argument to LOAD must be a string."),
                            }
                            io::stdout().flush().unwrap();
                            None
                        }
                        "set-env" => {
                            // The state's env is set to the result of evaluating the first argument.
                            let (first, rest) = store.car_cdr(&rest)?;
                            assert!(rest.is_nil());
                            let (first_evaled, _, _, _) = self.eval_expr(first, store)?;
                            self.env = first_evaled;
                            None
                        }
                        _ => {
                            bail!(
                                "Unsupported command: {}",
                                car.fmt_to_string(store, &state.borrow())
                            );
                        }
                    }
                }
                _ => bail!(
                    "Unsupported command: {}",
                    car.fmt_to_string(store, &state.borrow())
                ),
            },
            _ => bail!(
                "Unsupported meta form: {}",
                expr_ptr.fmt_to_string(store, &state.borrow())
            ),
        };

        if let Some(expr) = res {
            let mut handle = io::stdout().lock();
            expr.fmt(store, &state.borrow(), &mut handle)?;

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
        store: &Store<F>,
        state: &State,
        expr_ptr: Ptr<F>,
    ) -> Result<(IO<F>, IO<F>, usize)> {
        match Evaluator::new(expr_ptr, self.env, store, self.limit, &self.lang).eval() {
            Ok((output, iterations, _emitted)) => {
                let IO {
                    expr: result,
                    env: _env,
                    cont: next_cont,
                } = output;
                {
                    print!("[{iterations} iterations] => ");

                    let input = IO {
                        expr: expr_ptr,
                        env: self.env,
                        cont: store.get_cont_outermost(),
                    };

                    match next_cont.tag {
                        ContTag::Outermost | ContTag::Terminal => {
                            let mut handle = io::stdout().lock();

                            result.fmt(store, state, &mut handle)?;

                            println!();
                        }
                        ContTag::Error => println!("ERROR!"),
                        _ => println!("Computation incomplete after limit: {}", self.limit),
                    }

                    Ok((input, output, iterations))
                }
            }

            Err(e) => {
                eprintln!("Evaluation error: {e}");
                Err(e.into())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use rustyline::DefaultEditor;
    use std::fs;
    use tempfile::Builder;

    #[test]
    fn test_file_history() {
        let input = "(+ 1 1)";
        let tmp_path = Builder::new().prefix("tmp").tempdir().unwrap().into_path();
        let tmp_file = tmp_path.join("lurk-history");

        let mut rl = DefaultEditor::new().unwrap();
        rl.add_history_entry(input).unwrap();
        rl.save_history(&tmp_file).unwrap();

        assert!(fs::read_to_string(&tmp_file).unwrap().contains(input));

        // Needed because the `into_path` tempfile function removes automatic deletion
        fs::remove_dir_all(tmp_path).unwrap();
    }
}
