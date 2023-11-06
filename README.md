# Lurk

![lurk-rs](https://github.com/lurk-lab/lurk-rs/actions/workflows/ci.yml/badge.svg)
![minimum rustc 1.70][msrv-image]
[![dependency status](https://deps.rs/repo/github/lurk-lab/lurk-rs/status.svg)](https://deps.rs/repo/github/lurk-lab/lurk-rs)
![crates.io][crates-image]

[msrv-image]: https://img.shields.io/badge/rustc-1.70+-blue.svg
[crates-image]: https://img.shields.io/crates/v/lurk.svg

# Status (Alpha)

Lurk is currently in Alpha. Code that runs in the Lurk Alpha release is expected to also run in Lurk Beta, and eventually Lurk 1.0. However, some low-level data representations are anticipated to change, and we will be refactoring the circuit implementation to increase auditability and further our confidence in Lurk's cryptographic security. Also note that since Lurk inherits some security properties from the underlying proving system, those who would rely on Lurk should investigate the security and status of Nova itself. We encourage early adopters to begin writing real applications taking advantage of Lurk so you can begin to familiarize yourself with the programming model. Likewise, we welcome your feedback -- which will help ensure ongoing development meets user need.

For support and discussions, please visit our [Zulip forum](https://zulip.lurk-lab.com/).

# Overview

Lurk is a statically scoped dialect of Lisp, influenced by Scheme and Common Lisp. A reference implementation focused on describing and developing the core language can be found in the [`lurk`](https://github.com/lurk-lab/lurk-lisp) repo.

Lurk's distinguishing feature relative to most programming languages is that correct execution of Lurk programs can be directly proved using zk-SNARKs. The resulting proofs are succinct: they are relatively small, can be verified quickly, and they reveal only the information explicitly contained in the statement to be proved.

For more detailed information, refer to the paper: [https://eprint.iacr.org/2023/369](https://eprint.iacr.org/2023/369)

Lurk's distinguishing feature relative to most zk-SNARK authoring languages is that Lurk is Turing complete, so arbitrary computational claims can be made and proved (subject to resource limitations, obviously). Because Lurk is a Lisp, its code is simply Lurk data, and any Lurk data can be directly evaluated as a Lurk program. Lurk constructs compound data using SNARK-friendly Poseidon hashes (provided by [Neptune](https://github.com/lurk-lab/neptune)), so its data is naturally content-addressable.

# Proofs

Integration with backend proving systems and tooling for proof generation are both still very early. Performance and user experience still have room for significant optimization and improvement, but simple examples can be found in the [fcomm example directory](fcomm/README.md).

# Backends
- Nova is Lurk's officially-supported IVC backend. It uses Lurk Lab's Arecibo fork of the [Nova proving system](https://github.com/lurk-lab/arecibo) and the Pasta Curves.
- SuperNova is Lurk's in-development NIVC backend. It uses Arecibo's [SuperNova extension ot the Nova proving system](https://github.com/lurk-lab/arecibo/tree/dev/src/supernova) and the Pasta Curves.
- Future work may target Halo2 or other proving systems.

It is an explicit design goal that statements about the evaluation of Lurk programs have identical semantic meaning across backends, with the qualification that Lurk language instances are themselves parameterized on scalar field and hash function. When backends use the same scalar field and hash function, they can be used to generate equivalent proofs. This is because the concrete representation of content-addressed data is fixed.

# Performance

Lurk backend integration is still immature, so current performance is not representative. As a rough approximation, we estimate that for entirely general computation using Lurk's universal circuit, Nova proving throughput will be on the order of 1,000 iterations per second per GPU. We expect that most compute-heavy applications will use optimized 'coprocessor' circuits, which will  dramatically improve performance. Planned improvements to Nova will allow for smaller inner circuits, further improving throughput -- and for full parallelization of reduction proofs.

# Specs
- [Lurk Spec](https://blog.lurk-lang.org/posts/circuit-spec)
- [Evaluation Spec](notes/eval.md)
- [Reduction Notes](notes/reduction-notes.md)

# Security Audit
Lurk's Alpha release has undergone a [security audit](https://blog.lurk-lang.org/posts/alpha-audit/inference-security-assessment-3-2023.pdf) as of 03/29/2023, performed by [Inference](https://inference.ag/company/).

# Versioning

Please note that the Lurk language and spec will be versioned independently from the crates that implement the spec. This is necessary semantic versioning implies different requirements for the language and its implementation. For example, Lurk Alpha is released as crate `lurk 0.2.0`. It is our intention for these two versioning systems to coincide at 1.0. The next major Lurk release will be Lurk Beta, but there may be multiple minor-version crate releases before then.

---

# Build

## Submodules

Lurk source files used in tests are in the [lurk-lib](https://github.com/lurk-lab/lurk-lib) submodule. You must
initialize and update submodules before test will pass:

```ignore
git submodule update --init --recursive
```

## Wasm

### Prerequisites
- [clang](https://clang.llvm.org/get_started.html)

Lurk can be compiled to Wasm with
```ignore
cargo build --target wasm32-unknown-unknown
```

If using Nix without a system-wide `clang` install (e.g. NixOS):
```ignore
CC=clang cargo build --target wasm32-unknown-unknown
```

## Repl

```ignore
cargo run --release
```

Or use the wrapper script:

```ignore
bin/lurk
```

Set the environment variable `LURK_FIELD` to specify the scalar field of the Lurk language instance:
- `LURK_FIELD=PALLAS` (default): scalar field of Pallas
- `LURK_FIELD=VESTA`: scalar field of Vesta

```ignore
➜  lurk-rs ✗ bin/lurk
    Finished release [optimized] target(s) in 0.06s
     Running `target/release/lurk`
Lurk REPL welcomes you.
> (let ((square (lambda (x) (* x x)))) (square 8))
[9 iterations] => 64
>
```

Or enable `info` log-level for a trace of reduction frames:
```ignore
➜  lurk-rs ✗ RUST_LOG=info bin/lurk
    Finished release [optimized] target(s) in 0.05s
     Running `target/release/lurk`
Lurk REPL welcomes you.
> (let ((square (lambda (x) (* x x)))) (square 8))
 INFO  lurk::eval > Frame: 0
	Expr: (let ((square (lambda (x) (* x x)))) (square 8))
	Env: nil
	Cont: Outermost
 INFO  lurk::eval > Frame: 1
	Expr: (lambda (x) (* x x))
	Env: nil
	Cont: Let{ var: square, body: (square 8), saved_env: nil, continuation: Outermost }
 INFO  lurk::eval > Frame: 2
	Expr: (square 8)
	Env: ((square . <FUNCTION (x) (* x x)>))
	Cont: Tail{ saved_env: nil, continuation: Outermost }
 INFO  lurk::eval > Frame: 3
	Expr: square
	Env: ((square . <FUNCTION (x) (* x x)>))
	Cont: Call{ unevaled_arg: 8, saved_env: ((square . <FUNCTION (x) (* x x)>)), continuation: Tail{ saved_env: nil, continuation: Outermost } }
 INFO  lurk::eval > Frame: 4
	Expr: 8
	Env: ((square . <FUNCTION (x) (* x x)>))
	Cont: Call2{ function: <FUNCTION (x) (* x x)>, saved_env: ((square . <FUNCTION (x) (* x x)>)), continuation: Tail{ saved_env: nil, continuation: Outermost } }
 INFO  lurk::eval > Frame: 5
	Expr: (* x x)
	Env: ((x . 8))
	Cont: Tail{ saved_env: nil, continuation: Outermost }
 INFO  lurk::eval > Frame: 6
	Expr: x
	Env: ((x . 8))
	Cont: Binop{ operator: product#, unevaled_args: (x), saved_env: ((x . 8)), continuation: Tail{ saved_env: nil, continuation: Outermost } }
 INFO  lurk::eval > Frame: 7
	Expr: x
	Env: ((x . 8))
	Cont: Binop2{ operator: product#, evaled_arg: 8, continuation: Tail{ saved_env: nil, continuation: Outermost } }
 INFO  lurk::eval > Frame: 8
	Expr: Thunk{ value: 64 => cont: Outermost}
	Env: nil
	Cont: Dummy
 INFO  lurk::eval > Frame: 9
	Expr: 64
	Env: nil
	Cont: Terminal
[9 iterations] => 64
> 
```

## Install

You can install the `lurk` Repl on your machine with
```ignore
$ cargo install --path .
```

## Nix

Install [Nix](https://nixos.org) and [enable Nix flakes](https://nixos.wiki/wiki/Flakes). Then, you can enter into a Nix devshell with the appropriate dependencies for Lurk with

```ignore
$ nix develop
```
or

```ignore
$ direnv allow
```

And then build with Cargo as usual:

```ignore
$ cargo build
```

## License

MIT or Apache 2.0
