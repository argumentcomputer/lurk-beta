# Lurk

[build-image]: https://github.com/lurk-lang/lurk-rs/workflows/CI/badge.svg
[build-link]: https://github.com/lurk-lang/lurk-rs/actions?query=workflow%3ACI+branch%3Amaster
[msrv-image]: https://img.shields.io/badge/rustc-1.56+-blue.svg

# Disclaimer

**DISCLAIMER:** Lurk is an early research-stage language. Neither the cryptography nor the software has been audited, and there is currently no trusted setup for Groth16 circuits. Do not use Lurk in production environments or anywhere else that security is necessary.

# Overview

Lurk is a statically scoped dialect of Lisp, influenced by Scheme and Common Lisp. A language specification and reference implementation focused on describing and developing the core language can be found in the [`lurk` repo](https://github.com/lurk-lang/lurk).

- [Lurk Language Specification](https://github.com/lurk-lang/lurk/blob/master/spec/v0-1.md)

Evaluation of Lurk expressions can be proved in zk-SNARKs, and this is its distinguishing feature. Lurk data is content-addressable, using SNARK-friendly Poseidon hashes (provided by [Neptune](https://github.com/filecoin-project/neptune)) to construct compound data.

# Proofs

Integration with backend proving systems and tooling for proof generation are both still very early. Performance user experience are poor, but simple examples can be found in the [fcomm example directory](fcomm/README.md).

# Backends
- The `fcomm` example uses Groth16/SnarkPack+ to generate succinct (but somewhat large) proofs, using Bls12-381.
- The forthcoming Nova backend will use the [Nova proving system](https://github.com/microsoft/Nova) and the Pasta Curves.
- Future work may target Halo2 or other proving systems.

It is an explicit design goal that statements about the evaluation of Lurk programs have identical semantic meaning across backends, with the qualification that Lurk language instances are themselves paramterized on scalar field and hash function. When backends use the same scalar field and hash function, equivalent proofs can be generated across backends. This is because the concrete representation of content-addressed data is fixed.

# (WIP) Specs
- [Circuit Spec](spec/main.pdf)
- [Evaluation Spec](spec/eval.md)
- [Reduction Notes](spec/reduction-notes.md)

---
# Build

## Submodules

Lurk source files used in tests are in the [lurk-lib](https://github.com/lurk-lang/lurk-lib) submodule. You must
initialize and update submodules before test will pass.

## Repl

```
cargo run --example repl
```

Or use the wrapper script:

```
bin/lurkrs
```

```
➜  lurk-rs ✗ bin/lurkrs
    Finished release [optimized] target(s) in 0.06s
     Running `target/release/examples/repl`
Lurk REPL welcomes you.
> (let ((square (lambda (x) (* x x)))) (square 8))
[9 iterations] => 64
>
```

Or enable `info` log-level for a trace of reduction frames:
```
➜  lurk-rs ✗ RUST_LOG=info bin/lurkrs
    Finished release [optimized] target(s) in 0.05s
     Running `target/release/examples/repl`
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


## License

MIT or Apache 2.0
