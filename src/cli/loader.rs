use std::io;
use std::path::PathBuf;
use std::sync::Arc;

use anyhow::{bail, Result};

use lurk::eval::lang::Lang;
use lurk::eval::Evaluator;
use lurk::field::LurkField;
use lurk::parser;
use lurk::ptr::Ptr;
use lurk::public_parameters::Claim;
use lurk::store::Store;
use lurk::tag::ContTag;
use lurk::writer::Write;
use lurk::{coprocessor::Coprocessor, eval::IO};
use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

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
    pub store: Store<F>,
    pub env: Ptr<F>,
    pub limit: usize,
    pub lang: Arc<Lang<F, C>>,
    pub last_claim: Option<Claim<F>>,
}

impl<F: LurkField, C: Coprocessor<F>> Loader<F, C> {
    pub fn new(store: Store<F>, env: Ptr<F>, limit: usize) -> Loader<F, C> {
        Loader {
            store,
            env,
            limit,
            lang: Arc::new(Lang::<F, C>::new()),
            last_claim: None,
        }
    }

    fn handle_meta(&mut self, expr: Ptr<F>, pwd_path: &PathBuf) -> Result<()> {
        todo!()
    }

    fn handle_non_meta(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, IO<F>, usize)> {
        match Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang).eval() {
            Ok((output, iterations, _)) => {
                let IO {
                    expr: result,
                    env: _,
                    cont: next_cont,
                } = output;
                {
                    if iterations != 1 {
                        print!("[{iterations} iterations] => ");
                    } else {
                        print!("[1 iteration] => ");
                    }

                    let input = IO {
                        expr: expr_ptr,
                        env: self.env,
                        cont: self.store.get_cont_outermost(),
                    };

                    match next_cont.tag {
                        ContTag::Outermost | ContTag::Terminal => {
                            let mut handle = io::stdout().lock();

                            result.fmt(&self.store, &mut handle)?;

                            println!();
                        }
                        ContTag::Error => println!("ERROR!"),
                        _ => println!("Computation incomplete after limit: {}", self.limit),
                    }

                    Ok((input, output, iterations))
                }
            }
            Err(e) => {
                println!("Evaluation error: {e:?}");
                Err(e.into())
            }
        }
    }

    pub fn load_file(&mut self, path: &PathBuf) -> Result<()> {
        Ok(())
    }

    pub fn repl(&mut self) -> Result<()> {
        println!("Lurk REPL welcomes you.");

        let pwd_path = std::env::current_dir()?;

        let mut editor: Editor<InputValidator, DefaultHistory> = Editor::new()?;

        loop {
            match editor.readline("> ") {
                Ok(line) => {
                    let input = parser::Span::new(&line);
                    #[cfg(not(target_arch = "wasm32"))]
                    match self.store.read_maybe_meta(input) {
                        Ok((_, expr_ptr, is_meta)) => {
                            if is_meta {
                                if let Err(e) = self.handle_meta(expr_ptr, &pwd_path) {
                                    println!("!Error: {e:?}");
                                };
                                continue;
                            } else {
                                if let Err(e) = self.handle_non_meta(expr_ptr) {
                                    println!("REPL Error: {e:?}");
                                }
                                continue;
                            }
                        }
                        Err(parser::Error::NoInput) => {
                            continue;
                        }
                        Err(e) => {
                            println!("Read error: {e:?}")
                        }
                    }
                }
                Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                    println!("Exiting...");
                    break;
                }
                Err(err) => {
                    println!("Error: {err:?}");
                    break;
                }
            }
        }
        Ok(())
    }

    pub fn prove_last_claim(&mut self) -> Result<()> {
        match &self.last_claim {
            Some(claim) => {
                let _ = prove_claim(&claim);
                Ok(())
            }
            None => {
                bail!("No claim to prove");
            }
        }
    }
}
