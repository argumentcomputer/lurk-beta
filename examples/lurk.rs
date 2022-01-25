use anyhow::Result;
use lurk::eval::{empty_sym_env, Evaluator};
use lurk::store::{ContPtr, ContTag, Expression, Pointer, Ptr, Store, Tag};
use lurk::writer::Write;
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
struct ReplState {
    env: Ptr,
    limit: usize,
}

struct Repl {
    state: ReplState,
    rl: Editor<InputValidator>,
    history_path: PathBuf,
}

impl Repl {
    fn new(s: &mut Store, limit: usize) -> Result<Self> {
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
    fn save_history(&mut self) -> Result<()> {
        self.rl.save_history(&self.history_path)?;
        Ok(())
    }
}

// For the moment, input must be on a single line.
fn main() -> Result<()> {
    println!("Lurk REPL welcomes you.");

    let mut s = Store::default();
    let limit = 1000_000_000;
    let mut repl = Repl::new(&mut s, limit)?;

    {
        // If an argument is passed, treat is as a Lurk file to run.
        let mut args = std::env::args();
        if args.len() > 1 {
            let lurk_file = args.nth(1).expect("Lurk file missing");
            repl.state.handle_run(&mut s, &lurk_file).unwrap();
            return Ok(());
        }
    }

    let stdout = io::stdout();

    loop {
        match repl.rl.readline("> ") {
            Ok(line) => {
                let result = repl.state.maybe_handle_command(&mut s, &line);

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

                if let Some(expr) = s.read(&line) {
                    let (result, _next_env, iterations, next_cont) =
                        Evaluator::new(expr, repl.state.env, &mut s, limit).eval();
                    print!("[{} iterations] => ", iterations);
                    let mut handle = stdout.lock();
                    result.fmt(&s, &mut handle)?;
                    println!();

                    match next_cont.tag() {
                        ContTag::Outermost | ContTag::Terminal => (),
                        _ => println!("Computation incomplete after limit: {}", limit),
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

    repl.save_history()?;

    Ok(())
}

impl ReplState {
    fn new(s: &mut Store, limit: usize) -> Self {
        Self {
            env: empty_sym_env(&s),
            limit,
        }
    }
    fn eval_expr(&mut self, expr: Ptr, store: &mut Store) -> (Ptr, usize, ContPtr) {
        let (result, _next_env, limit, next_cont) =
            Evaluator::new(expr, self.env.clone(), store, self.limit).eval();

        (result, limit, next_cont)
    }

    /// Returns two bools.
    /// First bool is true if input is a command.
    /// Second bool is true if processing should continue.
    fn maybe_handle_command(&mut self, store: &mut Store, line: &str) -> Result<(bool, bool)> {
        let mut chars = line.chars().peekable();
        let maybe_command = store.read_next(&mut chars);

        let result = match &maybe_command {
            Some(maybe_command) => match maybe_command.tag() {
                Tag::Sym => match store.fetch(&maybe_command).unwrap().as_sym_str().unwrap() {
                    ":QUIT" => (true, false),
                    ":LOAD" => match store.read_string(&mut chars) {
                        Some(s) => match s.tag() {
                            Tag::Str => {
                                let path = store.fetch(&s).unwrap();
                                let path = PathBuf::from(path.as_str().unwrap());
                                self.handle_load(store, path)?;
                                (true, true)
                            }
                            other => {
                                anyhow::bail!("No valid path found: {:?}", other);
                            }
                        },
                        None => {
                            anyhow::bail!("No path found");
                        }
                    },
                    ":RUN" => {
                        if let Some(s) = store.read_string(&mut chars) {
                            if s.tag() == Tag::Str {
                                let path = store.fetch(&s).unwrap();
                                let path = PathBuf::from(path.as_str().unwrap());
                                self.handle_run(store, &path)?;
                            }
                        }
                        (true, true)
                    }
                    ":CLEAR" => {
                        self.env = empty_sym_env(&store);
                        (true, true)
                    }
                    s => {
                        if s.starts_with(":") {
                            println!("Unkown command: {}", s);
                            (true, true)
                        } else {
                            (false, true)
                        }
                    }
                },
                _ => (false, true),
            },
            _ => (false, true),
        };

        Ok(result)
    }

    fn handle_load<P: AsRef<Path>>(&mut self, store: &mut Store, path: P) -> Result<()> {
        println!("Loading from {}.", path.as_ref().to_str().unwrap());
        let input = read_to_string(path)?;

        let expr = store.read(&input).unwrap();
        let (result, _limit, _next_cont) = self.eval_expr(expr, store);

        self.env = result;

        println!("Read: {}", input);
        io::stdout().flush().unwrap();
        Ok(())
    }

    fn handle_run<P: AsRef<Path> + Copy>(&mut self, store: &mut Store, path: P) -> Result<()> {
        println!("Running from {}.", path.as_ref().to_str().unwrap());
        let p = path;

        let input = read_to_string(path)?;
        let mut chars = input.chars().peekable();

        while let Some((ptr, is_meta)) = store.read_maybe_meta(&mut chars) {
            let expr = store.fetch(&ptr).unwrap();
            if is_meta {
                match expr {
                    Expression::Cons(car, rest) => match &store.fetch(&car).unwrap() {
                        Expression::Sym(s) => {
                            if s == &":LOAD" {
                                match store.fetch(&store.car(&rest)).unwrap() {
                                    Expression::Str(path) => {
                                        let joined =
                                            p.as_ref().parent().unwrap().join(Path::new(&path));
                                        self.handle_load(store, &joined)?
                                    }
                                    _ => panic!("Argument to :LOAD must be a string."),
                                }
                            } else if s == &":RUN" {
                                match store.fetch(&store.car(&rest)).unwrap() {
                                    Expression::Str(path) => {
                                        let joined =
                                            p.as_ref().parent().unwrap().join(Path::new(&path));
                                        self.handle_run(store, &joined)?
                                    }
                                    _ => panic!("Argument to :RUN must be a string."),
                                }
                            } else if s == &":ASSERT-EQ" {
                                let (first, rest) = store.car_cdr(&rest);
                                let (second, rest) = store.car_cdr(&rest);
                                assert!(rest.is_nil());
                                let (first_evaled, _, _) = self.eval_expr(first, store);
                                let (second_evaled, _, _) = self.eval_expr(second, store);
                                assert_eq!(first_evaled, second_evaled);
                            } else if s == &":ASSERT" {
                                let (first, rest) = store.car_cdr(&rest);
                                assert!(rest.is_nil());
                                let (first_evaled, _, _) = self.eval_expr(first, store);
                                assert!(!first_evaled.is_nil());
                            } else if s == &":CLEAR" {
                                self.env = empty_sym_env(&store);
                            } else if s == &":ASSERT-ERROR" {
                                let (first, rest) = store.car_cdr(&rest);

                                assert!(rest.is_nil());
                                let (_, _, continuation) = self.clone().eval_expr(first, store);
                                assert!(continuation.is_error());
                                // FIXME: bring back catching, or solve otherwise
                                // std::panic::catch_unwind(||
                                // } else {
                                //     // There was a panic, so this is okay.
                                //     // FIXME: Never panic. Instead return Continuation::Error when evaluating.
                                //     ()
                                // }
                            } else {
                                panic!("!({} ...) is unsupported.", s);
                            }
                        }
                        _ => panic!("!(<COMMAND> ...) must be a (:keyword) symbol."),
                    },
                    _ => panic!("!<COMMAND> form is unsupported."),
                }
            } else {
                let (result, _limit, _next_cont) = self.eval_expr(ptr, store);

                println!("Read: {}", input);
                println!("Evaled: {}", result.fmt_to_string(&store));
                io::stdout().flush().unwrap();
            }
        }

        Ok(())
    }
}
