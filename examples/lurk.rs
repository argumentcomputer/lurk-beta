use lurk::data::{Continuation, Expression, Store};
use lurk::eval::{empty_sym_env, outer_evaluate};
use std::fs::read_to_string;
use std::io::{self, BufRead, Error, Write};
use std::path::Path;

#[derive(Clone)]
struct ReplState {
    env: Expression,
    limit: usize,
}
impl ReplState {
    fn new(s: &mut Store, limit: usize) -> Self {
        Self {
            env: empty_sym_env(&s),
            limit,
        }
    }
}

// For the moment, input must be on a single line.
fn main() {
    println!("Lurk REPL welcomes you.");

    let mut s = Store::default();
    let prompt = "> ";
    let limit = 1000000;
    let mut state = ReplState::new(&mut s, limit);

    {
        // If an argument is passed, treat is as a Lurk file to run.
        let mut args = std::env::args();
        if args.len() > 1 {
            let lurk_file = args.nth(1).expect("Lurk file missing");
            handle_run(&mut state, &mut s, &lurk_file).unwrap();
            return;
        }
    }

    let stdin = io::stdin();
    let mut it = stdin.lock().lines();
    let mut stdout = io::stdout();

    loop {
        print!("{}", prompt);
        stdout.flush().unwrap();

        // TODO: We should be able to handle input with line breaks in it from the REPL,
        // not just in files we load/run.
        let line = it.next().unwrap().unwrap();

        let result = maybe_handle_command(&mut state, &mut s, &line);

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
                outer_evaluate(expr, state.env.clone(), &mut s, limit);
            print!("[{} iterations] => ", iterations);
            let mut handle = stdout.lock();
            s.print_expr(&result, &mut handle).unwrap();
            println!();

            match next_cont {
                Continuation::Outermost | Continuation::Terminal => (),
                _ => println!("Computation incomplete after limit: {}", limit),
            }
        }
    }
}

fn eval_expr(
    expr: Expression,
    state: &mut ReplState,
    store: &mut Store,
) -> (Expression, usize, Continuation) {
    let (result, _next_env, limit, next_cont) =
        outer_evaluate(expr, state.env.clone(), store, state.limit);

    (result, limit, next_cont)
}

/// Returns two bools.
/// First bool is true if input is a command.
/// Second bool is true if processing should continue.
fn maybe_handle_command(
    state: &mut ReplState,
    store: &mut Store,
    line: &str,
) -> Result<(bool, bool), Error> {
    let mut chars = line.chars().peekable();
    let maybe_command = store.read_next(&mut chars);

    let result = match &maybe_command {
        Some(Expression::Sym(s)) => {
            if s == &":QUIT" {
                (true, false)
            } else if s == &":LOAD" {
                if let Some(Expression::Str(path)) = store.read_string(&mut chars) {
                    handle_load(state, store, Path::new(&path))?;
                }
                (true, true)
            } else if s == &":RUN" {
                if let Some(Expression::Str(path)) = store.read_string(&mut chars) {
                    handle_run(state, store, &path)?;
                }
                (true, true)
            } else if s == &":CLEAR" {
                state.env = empty_sym_env(&store);
                (true, true)
            } else {
                (false, true)
            }
        }
        _ => (false, true),
    };

    Ok(result)
}

fn handle_load<P: AsRef<Path>>(
    state: &mut ReplState,
    store: &mut Store,
    path: P,
) -> Result<(), Error> {
    println!("Loading from {}.", path.as_ref().to_str().unwrap());
    let input = read_to_string(path)?;

    let expr = store.read(&input).unwrap();
    let (result, _limit, _next_cont) = eval_expr(expr, state, store);

    state.env = result;

    println!("Read: {}", input);
    io::stdout().flush().unwrap();
    Ok(())
}

fn handle_run<P: AsRef<Path> + Copy>(
    state: &mut ReplState,
    store: &mut Store,
    path: P,
) -> Result<(), Error> {
    println!("Running from {}.", path.as_ref().to_str().unwrap());
    let p = path;

    let input = read_to_string(path)?;
    let mut chars = input.chars().peekable();

    while let Some((expr, is_meta)) = store.read_maybe_meta(&mut chars) {
        if is_meta {
            match expr {
                Expression::Cons(car, rest) => match &store.fetch(car).unwrap() {
                    Expression::Sym(s) => {
                        if s == ":LOAD" {
                            match store.car(&store.fetch(rest).unwrap()) {
                                Expression::Str(path) => {
                                    let joined =
                                        p.as_ref().parent().unwrap().join(Path::new(&path));
                                    handle_load(state, store, &joined)?
                                }
                                _ => panic!("Argument to :LOAD must be a string."),
                            }
                        } else if s == ":RUN" {
                            match store.car(&store.fetch(rest).unwrap()) {
                                Expression::Str(path) => {
                                    let joined =
                                        p.as_ref().parent().unwrap().join(Path::new(&path));
                                    handle_run(state, store, &joined)?
                                }
                                _ => panic!("Argument to :RUN must be a string."),
                            }
                        } else if s == ":ASSERT-EQ" {
                            let (first, rest) = store.car_cdr(&store.fetch(rest).unwrap());
                            let (second, rest) = store.car_cdr(&rest);
                            assert_eq!(Expression::Nil, rest);
                            let (first_evaled, _, _) = eval_expr(first, state, store);
                            let (second_evaled, _, _) = eval_expr(second, state, store);
                            assert_eq!(first_evaled, second_evaled);
                        } else if s == ":ASSERT" {
                            let (first, rest) = store.car_cdr(&store.fetch(rest).unwrap());
                            assert_eq!(Expression::Nil, rest);
                            let (first_evaled, _, _) = eval_expr(first, state, store);
                            assert!(first_evaled != Expression::Nil);
                        } else if s == ":CLEAR" {
                            state.env = empty_sym_env(&store);
                        } else if s == ":ASSERT-ERROR" {
                            let (first, rest) = store.car_cdr(&store.fetch(rest).unwrap());

                            assert_eq!(Expression::Nil, rest);
                            if let Ok((_, _, continuation)) = std::panic::catch_unwind(|| {
                                eval_expr(first, &mut state.clone(), &mut store.clone())
                            }) {
                                assert_eq!(Continuation::Error, continuation);
                            } else {
                                // There was a panic, so this is okay.
                                // FIXME: Never panic. Instead return Continuation::Error when evaluating.
                                ()
                            }
                        } else {
                            panic!("!({} ...) is unsupported.", s);
                        }
                    }
                    _ => panic!("!(<COMMAND> ...) must be a (:keyword) symbol."),
                },
                _ => panic!("!<COMMAND> form is unsupported."),
            }
        } else {
            let (result, _limit, _next_cont) = eval_expr(expr, state, store);

            println!("Read: {}", input);
            println!("Evaled: {}", store.write_expr_str(&result));
            io::stdout().flush().unwrap();
        }
    }

    Ok(())
}
