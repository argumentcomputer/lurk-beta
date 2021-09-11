use lurk::data::{Continuation, Expression, Store};
use lurk::eval::{empty_sym_env, outer_evaluate};
use std::fs::read_to_string;
use std::io::{self, BufRead, Error, Write};

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

    let stdin = io::stdin();
    let mut it = stdin.lock().lines();

    loop {
        print!("{}", prompt);
        io::stdout().flush().unwrap();

        let line = it.next().unwrap().unwrap();

        let result = maybe_handle_command(&mut state, &mut s, &line);

        match result {
            Ok(x) if x => {
                continue;
            }
            Ok(_) => (),
            Err(e) => {
                println!("Error when handling {}: {:?}", line, e);
                continue;
            }
        };

        let expr = s.read(&line).unwrap();

        let (result, _next_env, limit, next_cont) =
            outer_evaluate(expr, state.env.clone(), &mut s, limit);
        println!("[{} iterations] => {}", limit, s.print_expr(&result));

        match next_cont {
            Continuation::Outermost | Continuation::Terminal => (),
            _ => println!("Computation incomplete after limit: {}", limit),
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

fn maybe_handle_command(
    state: &mut ReplState,
    store: &mut Store,
    line: &str,
) -> Result<bool, Error> {
    let split = line.split_whitespace().collect::<Vec<_>>();

    let words = if split.len() == 0 { vec![line] } else { split };

    let command = words[0].to_ascii_uppercase();

    let is_command = if command == ":LOAD" {
        if words.len() < 2 {
            return Ok(true);
        }
        let path = words[1];
        println!("Reading from {}.", path);

        let input = read_to_string(path)?;

        let expr = store.read(&input).unwrap();
        let (result, _limit, _next_cont) = eval_expr(expr, state, store);

        state.env = result;

        println!("Read: {}", input);
        io::stdout().flush().unwrap();
        true
    } else {
        false
    };

    Ok(is_command)
}
