use crate::error::ParserError;
use crate::eval::{empty_sym_env, Evaluator, IO};
use crate::field::LurkField;
use crate::package::Package;
use crate::store::{ContPtr, ContTag, Expression, Pointer, Ptr, Store, Tag};
use crate::writer::Write;
use anyhow::Result;
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
    env: Ptr<F>,
    limit: usize,
}

pub struct Repl<F: LurkField> {
    state: ReplState<F>,
    rl: Editor<InputValidator>,
    history_path: PathBuf,
}

impl<F: LurkField> Repl<F> {
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

        let state = ReplState::new(s, limit);
        Ok(Self {
            state,
            rl,
            history_path,
        })
    }
    pub fn save_history(&mut self) -> Result<()> {
        self.rl.save_history(&self.history_path)?;
        Ok(())
    }
}

// For the moment, input must be on a single line.
pub fn repl<P: AsRef<Path>, F: LurkField>(lurk_file: Option<P>) -> Result<()> {
    println!("Lurk REPL welcomes you.");

    let mut s = Store::<F>::default();
    let limit = 100_000_000;
    let mut repl = Repl::new(&mut s, limit)?;
    let package = Package::lurk();

    {
        if let Some(lurk_file) = lurk_file {
            repl.state.handle_run(&mut s, &lurk_file, &package).unwrap();
            return Ok(());
        }
    }

    let stdout = io::stdout();

    loop {
        match repl.rl.readline("> ") {
            Ok(line) => {
                repl.save_history()?;

                let result = repl.state.maybe_handle_command(&mut s, &line, &package);

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
                        println!("Error when handling {}: {:?}", line, e);
                        continue;
                    }
                };

                match s.read_in_package(&line, &package) {
                    Ok(expr) => match Evaluator::new(expr, repl.state.env, &mut s, limit).eval() {
                        Ok((
                            IO {
                                expr: result,
                                env: _env,
                                cont: next_cont,
                            },
                            iterations,
                            _emitted,
                        )) => {
                            print!("[{} iterations] => ", iterations);

                            match next_cont.tag() {
                                ContTag::Outermost | ContTag::Terminal => {
                                    let mut handle = stdout.lock();
                                    result.fmt(&s, &mut handle)?;
                                    println!();
                                }
                                ContTag::Error => println!("ERROR!"),
                                _ => println!("Computation incomplete after limit: {}", limit),
                            }
                        }
                        Err(e) => {
                            println!("Evaluation error: {:?}", e);
                            continue;
                        }
                    },
                    Err(ParserError::NoInput) => {
                        continue;
                    }
                    Err(e) => {
                        println!("Read error: {:?}", e)
                    }
                }
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                println!("Exiting...");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
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
    ) -> (Ptr<F>, usize, ContPtr<F>, Vec<Ptr<F>>) {
        let (
            IO {
                expr: result,
                env: _env,
                cont: next_cont,
            },
            limit,
            emitted,
        ) = Evaluator::new(expr, self.env, store, self.limit)
            .eval()
            .unwrap();

        (result, limit, next_cont, emitted)
    }

    /// Returns two bools.
    /// First bool is true if input is a command.
    /// Second bool is true if processing should continue.
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
                Tag::Sym => {
                    if let Some(key_string) = store
                        .fetch(maybe_command)
                        .unwrap()
                        .as_simple_keyword_string()
                    {
                        match key_string.as_str() {
                            "QUIT" => (true, false),
                            "LOAD" => match store.read_string(&mut chars) {
                                Ok(s) => match s.tag() {
                                    Tag::Str => {
                                        let path = store.fetch(&s).unwrap();
                                        let path = PathBuf::from(path.as_str().unwrap());
                                        self.handle_load(store, path, package)?;
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
                                    if s.tag() == Tag::Str {
                                        let path = store.fetch(&s).unwrap();
                                        let path = PathBuf::from(path.as_str().unwrap());
                                        self.handle_run(store, &path, package)?;
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
        path: P,
        package: &Package,
    ) -> Result<()> {
        println!("Loading from {}.", path.as_ref().to_str().unwrap());
        let input = read_to_string(path)?;
        let mut chars = input.chars().peekmore();

        while let Ok(expr) = store.read_next(&mut chars, package) {
            let (result, _limit, _next_cont, _) = self.eval_expr(expr, store);

            self.env = result;

            io::stdout().flush().unwrap();
        }
        println!("Read: {}", input);

        Ok(())
    }

    pub fn handle_run<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        path: P,
        package: &Package,
    ) -> Result<()> {
        println!("Running from {}.", path.as_ref().to_str().unwrap());
        let p = path;

        let input = read_to_string(path)?;
        println!("Read from {}: {}", path.as_ref().to_str().unwrap(), input);
        let mut chars = input.chars().peekmore();

        while let Ok((ptr, is_meta)) = store.read_maybe_meta(&mut chars, package) {
            let expr = store.fetch(&ptr).unwrap();
            if is_meta {
                match expr {
                    Expression::Cons(car, rest) => match &store.fetch(&car).unwrap() {
                        Expression::Sym(s) => {
                            if let Some(name) = s.simple_keyword_name() {
                                if &name == "LOAD" {
                                    match store.fetch(&store.car(&rest)).unwrap() {
                                        Expression::Str(path) => {
                                            let joined =
                                                p.as_ref().parent().unwrap().join(Path::new(&path));
                                            self.handle_load(store, &joined, package)?
                                        }
                                        _ => panic!("Argument to :LOAD must be a string."),
                                    }
                                    io::stdout().flush().unwrap();
                                } else if &name == "RUN" {
                                    match store.fetch(&store.car(&rest)).unwrap() {
                                        Expression::Str(path) => {
                                            let joined =
                                                p.as_ref().parent().unwrap().join(Path::new(&path));
                                            self.handle_run(store, &joined, package)?
                                        }
                                        _ => panic!("Argument to :RUN must be a string."),
                                    }
                                } else if &name == "ASSERT-EQ" {
                                    let (first, rest) = store.car_cdr(&rest);
                                    let (second, rest) = store.car_cdr(&rest);
                                    assert!(rest.is_nil());
                                    let (first_evaled, _, _, _) = self.eval_expr(first, store);
                                    let (second_evaled, _, _, _) = self.eval_expr(second, store);
                                    assert!(store.ptr_eq(&first_evaled, &second_evaled)?);
                                } else if &name == "ASSERT" {
                                    let (first, rest) = store.car_cdr(&rest);
                                    assert!(rest.is_nil());
                                    let (first_evaled, _, _, _) = self.eval_expr(first, store);
                                    assert!(!first_evaled.is_nil());
                                } else if &name == "CLEAR" {
                                    self.env = empty_sym_env(store);
                                } else if &name == "ASSERT-ERROR" {
                                    let (first, rest) = store.car_cdr(&rest);

                                    assert!(rest.is_nil());
                                    let (_, _, continuation, _) =
                                        self.clone().eval_expr(first, store);
                                    assert!(continuation.is_error());
                                    // FIXME: bring back catching, or solve otherwise
                                    // std::panic::catch_unwind(||
                                    // } else {
                                    //     // There was a panic, so this is okay.
                                    //     // FIXME: Never panic. Instead return Continuation::Error when evaluating.
                                    //     ()
                                    // }
                                } else if name == "ASSERT-EMITTED" {
                                    let (first, rest) = store.car_cdr(&rest);
                                    let (second, rest) = store.car_cdr(&rest);

                                    assert!(rest.is_nil());
                                    let (first_evaled, _, _, _) =
                                        self.clone().eval_expr(first, store);
                                    let (_, _, _, emitted) = self.eval_expr(second, store);
                                    let (mut first_emitted, mut rest_emitted) =
                                        store.car_cdr(&first_evaled);
                                    for (i, elem) in emitted.iter().enumerate() {
                                        if elem != &first_emitted {
                                            panic!(
                                            ":ASSERT-EMITTED failed at position {}. Expected {}, but found {}.",
                                            i,
                                            first_emitted.fmt_to_string(store),
                                            elem.fmt_to_string(store),
                                        );
                                        }
                                        (first_emitted, rest_emitted) =
                                            store.car_cdr(&rest_emitted);
                                    }
                                } else {
                                    panic!("!({} ...) is unsupported.", s.name());
                                }
                            } else {
                                panic!("!({} ...) is unsupported.", s.name());
                            }
                        }
                        _ => panic!("!(<COMMAND> ...) must be a (:keyword) symbol."),
                    },
                    _ => panic!("!<COMMAND> form is unsupported."),
                }
            } else {
                let (result, _limit, _next_cont, _) = self.eval_expr(ptr, store);

                println!("Evaled: {}", result.fmt_to_string(store));
                io::stdout().flush().unwrap();
            }
        }

        Ok(())
    }
}
