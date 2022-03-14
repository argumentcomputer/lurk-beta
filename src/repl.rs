use crate::eval::{empty_sym_env, Evaluator, IO};
use crate::parser::Span;
use crate::store::{ContPtr, ContTag, Expression, Pointer, Ptr, Store, Tag};
use crate::writer::Write;
use anyhow::Result;
use blstrs::Scalar as Fr;
use rustyline::error::ReadlineError;
use rustyline::validate::{
    MatchingBracketValidator, ValidationContext, ValidationResult, Validator,
};
use rustyline::{Config, Editor};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};
use std::fs::read_to_string;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};

mod command;

use command::Command;

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
pub struct ReplState {
    env: Ptr<Fr>,
    limit: usize,
}

pub struct Repl {
    state: ReplState,
    rl: Editor<InputValidator>,
    history_path: PathBuf,
}

impl Repl {
    pub fn new(s: &mut Store<Fr>, limit: usize) -> Result<Self> {
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
pub fn repl<P: AsRef<Path>>(lurk_file: Option<P>) -> Result<()> {
    println!("Lurk REPL welcomes you.");

    let mut s = Store::default();
    let limit = 100_000_000;
    let mut repl = Repl::new(&mut s, limit)?;

    let stdout = io::stdout();

    loop {
        match repl.rl.readline("⥀> ") {
            Ok(line) => {
                let result = command::parse_command()(Span::new(&line));
                match result {
                    Ok((_, Command::Quit)) => {
                        println!("Goodbye.");
                        break;
                    }
                    Ok((_, Command::Clear)) => {
                        repl.state.env = empty_sym_env(&s);
                        println!("Environment cleared.");
                    }
                    Ok((_, Command::Load(path))) => {
                        let input = read_to_string(path)?;

                        match s.parse_term(&input) {
                            Ok(expr) => {
                                let (result, _limit, _next_cont) =
                                    repl.state.eval_expr(expr, &mut s);

                                repl.state.env = result;

                                println!("Read: {}", input);
                                io::stdout().flush().unwrap();
                            }
                            Err(e) => {
                                println!("Error: {}", e)
                            }
                        }
                    }
                    Ok((_, Command::Eval(trm))) => {
                        let expr = s.store_term(*trm);
                        let (
                            IO {
                                expr: result,
                                env: _env,
                                cont: next_cont,
                            },
                            iterations,
                        ) = Evaluator::new(expr, repl.state.env, &mut s, repl.state.limit).eval();

                        print!("[{} iterations] => ", iterations);

                        match next_cont.tag() {
                            ContTag::Outermost | ContTag::Terminal => {
                                let mut handle = stdout.lock();
                                result.fmt(&s, &mut handle)?;
                                println!();
                            }
                            ContTag::Error => println!("ERROR! cont-tag"),
                            _ => println!("Computation incomplete after limit: {}", limit),
                        }
                    }
                    Err(e) => match e {
                        nom::Err::Incomplete(_) => println!("Incomplete Input"),
                        nom::Err::Failure(e) => {
                            println!("Parse Failure:\n");
                            println!("{}", e);
                        }
                        nom::Err::Error(e) => {
                            println!("Parse Error:\n");
                            println!("{}", e);
                        }
                    },
                }
                //let result = repl.state.maybe_handle_command(&mut s, &line);

                //match result {
                //    Ok((handled_command, should_continue)) if handled_command => {
                //        if should_continue {
                //            continue;
                //        } else {
                //            break;
                //        };
                //    }
                //    Ok(_) => (),
                //    Err(e) => {
                //        println!("Error when handling {}: {:?}", line, e);
                //        continue;
                //    }
                //};

                //if let Some(expr) = s.read(&line) {
                //    let (
                //        IO {
                //            expr: result,
                //            env: _env,
                //            cont: next_cont,
                //        },
                //        iterations,
                //    ) = Evaluator::new(expr, repl.state.env, &mut s, limit).eval();

                //    print!("[{} iterations] => ", iterations);

                //    match next_cont.tag() {
                //        ContTag::Outermost | ContTag::Terminal => {
                //            let mut handle = stdout.lock();
                //            result.fmt(&s, &mut handle)?;
                //            println!();
                //        }
                //        ContTag::Error => println!("ERROR!"),
                //        _ => println!("Computation incomplete after limit: {}", limit),
                //    }
                //}
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
    pub fn new(s: &mut Store<Fr>, limit: usize) -> Self {
        Self {
            env: empty_sym_env(s),
            limit,
        }
    }

    pub fn eval_expr(
        &mut self,
        expr: Ptr<Fr>,
        store: &mut Store<Fr>,
    ) -> (Ptr<Fr>, usize, ContPtr<Fr>) {
        let (
            IO {
                expr: result,
                env: _env,
                cont: next_cont,
            },
            limit,
        ) = Evaluator::new(expr, self.env, store, self.limit).eval();

        (result, limit, next_cont)
    }
    //    pub fn handle_run<P: AsRef<Path> + Copy>(
    //        &mut self,
    //        store: &mut Store<Fr>,
    //        path: P,
    //    ) -> Result<()> {
    //        println!("Running from {}.", path.as_ref().to_str().unwrap());
    //        let p = path;
    //
    //        let input = read_to_string(path)?;
    //        println!("Read from {}: {}", path.as_ref().to_str().unwrap(), input);
    //        let mut chars = input.chars().peekable();
    //
    //        while let Some((ptr, is_meta)) = store.read_maybe_meta(&mut chars) {
    //            let expr = store.fetch(&ptr).unwrap();
    //            if is_meta {
    //                match expr {
    //                    Expression::Cons(car, rest) => match &store.fetch(&car).unwrap() {
    //                        Expression::Sym(s) => {
    //                            if s == &":LOAD" {
    //                                match store.fetch(&store.car(&rest)).unwrap() {
    //                                    Expression::Str(path) => {
    //                                        let joined =
    //                                            p.as_ref().parent().unwrap().join(Path::new(&path));
    //                                        self.handle_load(store, &joined)?
    //                                    }
    //                                    _ => panic!("Argument to :LOAD must be a string."),
    //                                }
    //                                io::stdout().flush().unwrap();
    //                            } else if s == &":RUN" {
    //                                match store.fetch(&store.car(&rest)).unwrap() {
    //                                    Expression::Str(path) => {
    //                                        let joined =
    //                                            p.as_ref().parent().unwrap().join(Path::new(&path));
    //                                        self.handle_run(store, &joined)?
    //                                    }
    //                                    _ => panic!("Argument to :RUN must be a string."),
    //                                }
    //                            } else if s == &":ASSERT-EQ" {
    //                                let (first, rest) = store.car_cdr(&rest);
    //                                let (second, rest) = store.car_cdr(&rest);
    //                                assert!(rest.is_nil());
    //                                let (first_evaled, _, _) = self.eval_expr(first, store);
    //                                let (second_evaled, _, _) = self.eval_expr(second, store);
    //                                assert_eq!(first_evaled, second_evaled);
    //                            } else if s == &":ASSERT" {
    //                                let (first, rest) = store.car_cdr(&rest);
    //                                assert!(rest.is_nil());
    //                                let (first_evaled, _, _) = self.eval_expr(first, store);
    //                                assert!(!first_evaled.is_nil());
    //                            } else if s == &":CLEAR" {
    //                                self.env = empty_sym_env(store);
    //                            } else if s == &":ASSERT-ERROR" {
    //                                let (first, rest) = store.car_cdr(&rest);
    //
    //                                assert!(rest.is_nil());
    //                                let (_, _, continuation) = self.clone().eval_expr(first, store);
    //                                assert!(continuation.is_error());
    //                                // FIXME: bring back catching, or solve otherwise
    //                                // std::panic::catch_unwind(||
    //                                // } else {
    //                                //     // There was a panic, so this is okay.
    //                                //     // FIXME: Never panic. Instead return Continuation::Error when evaluating.
    //                                //     ()
    //                                // }
    //                            } else {
    //                                panic!("!({} ...) is unsupported.", s);
    //                            }
    //                        }
    //                        _ => panic!("!(<COMMAND> ...) must be a (:keyword) symbol."),
    //                    },
    //                    _ => panic!("!<COMMAND> form is unsupported."),
    //                }
    //            } else {
    //                let (result, _limit, _next_cont) = self.eval_expr(ptr, store);
    //
    //                println!("Read: {}", input);
    //                println!("Evaled: {}", result.fmt_to_string(store));
    //                io::stdout().flush().unwrap();
    //            }
    //        }
    //
    //        Ok(())
    //    }
}
