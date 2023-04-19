use crate::coprocessor::Coprocessor;
use crate::error::LurkError;
use crate::eval::{empty_sym_env, lang::Lang, Evaluator, IO};
use crate::field::LurkField;
use crate::light_data::{Encodable, LightData, LightStore};
use crate::package::Package;
use crate::parser;
use crate::scalar_store::ScalarStore;
use crate::store::{ContPtr, Expression, Pointer, Ptr, Store};
use crate::sym::Sym;
use crate::tag::ContTag;
use crate::writer::Write;
use anyhow::{bail, Context, Result};
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
use std::marker::PhantomData;
use std::path::Path;
#[cfg(not(target_arch = "wasm32"))]
use std::path::PathBuf;
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

#[derive(Clone)]
pub struct ReplState<F: LurkField, C: Coprocessor<F>> {
    pub env: Ptr<F>,
    pub limit: usize,
    pub command: Option<Command>,
    pub lang: Lang<F, C>,
}

pub struct Repl<F: LurkField, T: ReplTrait<F, C>, C: Coprocessor<F>> {
    state: T,
    rl: Editor<InputValidator, DefaultHistory>,
    #[cfg(not(target_arch = "wasm32"))]
    history_path: PathBuf,
    _phantom: PhantomData<(F, C)>,
}

pub trait ReplTrait<F: LurkField, C: Coprocessor<F>> {
    fn new(s: &mut Store<F>, limit: usize, command: Option<Command>, lang: Lang<F, C>) -> Self;

    fn name() -> String;

    fn prompt(&mut self) -> String;

    fn process_line(&mut self, line: String) -> String;

    fn command() -> Command;

    fn handle_form<P: AsRef<Path> + Copy, T: Iterator<Item = char>>(
        &mut self,
        store: &mut Store<F>,
        chars: &mut peekmore::PeekMoreIterator<T>,
        package: &Package,
        pwd: P,
    ) -> Result<()> {
        let (ptr, is_meta) = store.read_maybe_meta(chars, package)?;

        if is_meta {
            let pwd: &Path = pwd.as_ref();
            self.handle_meta(store, ptr, package, pwd)
        } else {
            self.handle_non_meta(store, ptr).map(|_| ())
        }
    }

    fn handle_load<P: AsRef<Path>>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
    ) -> Result<()> {
        eprintln!("Loading from {}.", file_path.as_ref().to_str().unwrap());
        self.handle_file(store, file_path.as_ref(), package)
    }

    fn handle_file<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
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
    ) -> Result<(IO<F>, IO<F>, usize)>;
}

impl<F: LurkField, T: ReplTrait<F, C>, C: Coprocessor<F>> Repl<F, T, C> {
    pub fn new(
        s: &mut Store<F>,
        limit: usize,
        command: Option<Command>,
        lang: Lang<F, C>,
    ) -> Result<Self> {
        #[cfg(not(target_arch = "wasm32"))]
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

pub fn repl_cli<F: LurkField, T: ReplTrait<F, C>, C: Coprocessor<F>>(
    lang: Lang<F, C>,
) -> Result<()> {
    let command = T::command();
    let matches = command.clone().get_matches();

    let lurk_file = matches.get_one::<String>("lurk_file");
    let light_store = matches.get_one::<String>("lightstore");

    repl_aux::<_, F, T, C>(lurk_file, light_store, Some(command), lang)
}

pub fn repl<F: LurkField, T: ReplTrait<F, C>, P: AsRef<Path>, C: Coprocessor<F>>(
    lurk_file: Option<P>,
    lang: Lang<F, C>,
) -> Result<()> {
    repl_aux::<_, F, T, C>(lurk_file, None, None, lang)
}

fn repl_aux<P: AsRef<Path>, F: LurkField, T: ReplTrait<F, C>, C: Coprocessor<F>>(
    lurk_file: Option<P>,
    light_store: Option<P>,
    command: Option<Command>,
    lang: Lang<F, C>,
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
    let repl: Repl<F, T, C> = Repl::new(s_ref, limit, command, lang)?;

    run_repl(s_ref, repl, lurk_file)
}

// For the moment, input must be on a single line.
pub fn run_repl<P: AsRef<Path>, F: LurkField, T: ReplTrait<F, C>, C: Coprocessor<F>>(
    s: &mut Store<F>,
    mut repl: Repl<F, T, C>,
    lurk_file: Option<P>,
) -> Result<()> {
    let package = Package::lurk();

    if lurk_file.is_none() {
        let name = T::name();
        eprintln!("{name} welcomes you.");
    }

    {
        if let Some(lurk_file) = lurk_file {
            repl.state.handle_load(s, &lurk_file, &package).unwrap();
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
                #[cfg(not(target_arch = "wasm32"))]
                repl.save_history()?;

                let mut chars = line.chars().peekmore();

                match s.read_maybe_meta(&mut chars, &package) {
                    Ok((expr, is_meta)) => {
                        if is_meta {
                            if let Err(e) = repl.state.handle_meta(s, expr, &package, p) {
                                eprintln!("!Error: {e:?}");
                            };
                            continue;
                        } else {
                            if let Err(e) = repl.state.handle_non_meta(s, expr) {
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

impl<F: LurkField, C: Coprocessor<F>> ReplState<F, C> {
    pub fn new(s: &mut Store<F>, limit: usize, command: Option<Command>, lang: Lang<F, C>) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
            command,
            lang,
        }
    }
    pub fn eval_expr(
        &mut self,
        expr: Ptr<F>,
        store: &mut Store<F>,
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
    fn new(s: &mut Store<F>, limit: usize, command: Option<Command>, lang: Lang<F, C>) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
            command,
            lang,
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
                Expression::Sym(Sym::Sym(s)) => {
                    match s.name().as_str() {
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
                            let (first_evaled, _, _, _) = self.clone().eval_expr(first, store)?;
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
                                _ => bail!("Argument to LOAD must be a string."),
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
                            bail!("Unsupported command: {}", car.fmt_to_string(store));
                        }
                    }
                }
                _ => bail!("Unsupported command: {}", car.fmt_to_string(store)),
            },
            _ => bail!("Unsupported meta form: {}", expr_ptr.fmt_to_string(store)),
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

                    match next_cont.tag() {
                        ContTag::Outermost | ContTag::Terminal => {
                            let mut handle = io::stdout().lock();

                            result.fmt(store, &mut handle)?;

                            println!();
                        }
                        ContTag::Error => println!("ERROR!"),
                        _ => println!("Computation incomplete after limit: {}", self.limit),
                    }

                    Ok((input, output, iterations))
                }
            }

            Err(e) => {
                eprintln!("Evaluation error: {e:?}");
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
