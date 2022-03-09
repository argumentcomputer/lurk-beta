# Lurk

[![Build Status][build-image]][build-link]
![minimum rustc 1.56][msrv-image]

# Submodules

Lurk source files used in tests are in the [lurk-lib](https://github.com/lurk-lang/lurk-lib) submodule. You must
initialize and update submodules before test will pass.


## Nix

[Nix](https://nixos.org) provides a declarative, content addressed and deterministic build system.

### Loading the build environment with all dependencies

```
nix develop
# Or automatically with direnv
direnv allow
```

### Build the crate
```
nix build .
```

### Run the example 

```
nix run .#lurk-example
```

## Repl

```
cargo run --example lurk
```

Or use the wrapper script:

```
bin/lurkrs
```

Enable `info` log-level for a trace of reduction frames:
```
➜  lurk-rs ✗ bin/lurkrs
    Finished release [optimized] target(s) in 0.05s
     Running `target/release/examples/lurk`
Lurk REPL welcomes you.
> (let ((square (lambda (x) (* x x)))) (square 8))
INFO [lurk::eval] Frame: 0
	Expr: (LET ((SQUARE (LAMBDA (X) (* X X)))) (SQUARE Num(0x8)))
	Env: NIL
	Cont: Outermost
INFO [lurk::eval] Frame: 1
	Expr: (LAMBDA (X) (* X X))
	Env: NIL
	Cont: Let{ var: SQUARE, body: (SQUARE Num(0x8)), saved_env: NIL, continuation: Outermost }
INFO [lurk::eval] Frame: 2
	Expr: (SQUARE Num(0x8))
	Env: ((SQUARE . <FUNCTION (X) . ((* X X))>))
	Cont: Tail{ saved_env: NIL, continuation: Outermost }
INFO [lurk::eval] Frame: 3
	Expr: SQUARE
	Env: ((SQUARE . <FUNCTION (X) . ((* X X))>))
	Cont: Call{ unevaled_arg: Num(0x8), saved_env: ((SQUARE . <FUNCTION (X) . ((* X X))>)), continuation: Tail{ saved_env: NIL, continuation: Outermost } }
INFO [lurk::eval] Frame: 4
	Expr: Num(0x8)
	Env: ((SQUARE . <FUNCTION (X) . ((* X X))>))
	Cont: Call2{ function: <FUNCTION (X) . ((* X X))>, saved_env: ((SQUARE . <FUNCTION (X) . ((* X X))>)), continuation: Tail{ saved_env: NIL, continuation: Outermost } }
INFO [lurk::eval] Frame: 5
	Expr: (* X X)
	Env: ((X . Num(0x8)))
	Cont: Tail{ saved_env: NIL, continuation: Outermost }
INFO [lurk::eval] Frame: 6
	Expr: X
	Env: ((X . Num(0x8)))
	Cont: Binop{ operator: Product, saved_env: ((X . Num(0x8))), unevaled_args: (X), continuationTail{ saved_env: NIL, continuation: Outermost } }
INFO [lurk::eval] Frame: 7
	Expr: X
	Env: ((X . Num(0x8)))
	Cont: Binop2{ operator: Product, evaled_arg: Num(0x8), continuation: Tail{ saved_env: NIL, continuation: Outermost } }
INFO [lurk::eval] Frame: 8
	Expr: Thunk for cont Outermost with value: Num(0x40)
	Env: NIL
	Cont: Dummy
INFO [lurk::eval] Frame: 9
	Expr: Num(0x40)
	Env: NIL
	Cont: Terminal
INFO [lurk::eval] Frame: 10
	Expr: Num(0x40)
	Env: NIL
	Cont: Terminal
[src/eval.rs:145] self.frame.i = 9
[9 iterations] => Num(0x40)
```

[build-image]: https://github.com/lurk-lang/lurk-rs/workflows/CI/badge.svg
[build-link]: https://github.com/lurk-lang/lurk-rs/actions?query=workflow%3ACI+branch%3Amaster
[msrv-image]: https://img.shields.io/badge/rustc-1.56+-blue.svg

## License

MIT or Apache 2.0
