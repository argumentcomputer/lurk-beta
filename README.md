# Lurk

![lurk-rs](https://github.com/lurk-lab/lurk-rs/actions/workflows/ci.yml/badge.svg)
![minimum rustc 1.70][msrv-image]
[![dependency status](https://deps.rs/repo/github/lurk-lab/lurk-rs/status.svg)](https://deps.rs/repo/github/lurk-lab/lurk-rs)
![crates.io][crates-image]

[msrv-image]: https://img.shields.io/badge/rustc-1.70+-blue.svg
[crates-image]: https://img.shields.io/crates/v/lurk.svg

# Status (Beta)

Lurk is currently in [Beta](https://blog.lurk-lang.org/posts/lurk-beta/), which is backwards compatible with code that ran in Lurk Alpha and is expected to be compatible with Lurk 1.0. However, some low-level data representations are anticipated to change, and we will be refactoring the evaluation model (and consequently its circuit) for efficiency purposes. Also note that since Lurk inherits some security properties from the underlying proving system, those who would rely on Lurk should investigate the security and status of Nova/SuperNova itself. We encourage early adopters to begin writing real applications taking advantage of Lurk so you can begin to familiarize yourself with the programming model. Likewise, we welcome your feedback -- which will help ensure ongoing development meets user need.

For support and discussions, please visit our [Zulip forum](https://zulip.lurk-lab.com/).

# Overview

Lurk is a statically scoped dialect of Lisp, influenced by Scheme and Common Lisp. A reference implementation focused on describing and developing the core language can be found in the [`lurk`](https://github.com/lurk-lab/lurk-lisp) repo.

Lurk's distinguishing feature relative to most programming languages is that correct execution of Lurk programs can be directly proved using zk-SNARKs. The resulting proofs are succinct: they are relatively small, can be verified quickly, and they reveal only the information explicitly contained in the statement to be proved.

For more detailed information, refer to the paper: [https://eprint.iacr.org/2023/369](https://eprint.iacr.org/2023/369)

Lurk's distinguishing feature relative to most zk-SNARK authoring languages is that Lurk is Turing complete, so arbitrary computational claims can be made and proved (subject to resource limitations, obviously). Because Lurk is a Lisp, its code is simply Lurk data, and any Lurk data can be directly evaluated as a Lurk program. Lurk constructs compound data using SNARK-friendly Poseidon hashes (provided by [Neptune](https://github.com/lurk-lab/neptune)), so its data is naturally content-addressable.

# Proofs

Integration with backend proving systems and tooling for proof generation are both still very early. Performance and user experience still have room for significant optimization and improvement, but simple examples can be found in the [demo example directory](demo/).

# Backends
- Nova is Lurk's officially-supported IVC backend. It uses Lurk Lab's Arecibo fork of the [Nova proving system](https://github.com/lurk-lab/arecibo) and the Pasta Curves.
- SuperNova is Lurk's in-development NIVC backend. It uses Arecibo's [SuperNova extension to the Nova proving system](https://github.com/lurk-lab/arecibo/tree/dev/src/supernova) and the Pasta Curves.
- Future work may target Halo2 or other proving systems.

It is an explicit design goal that statements about the evaluation of Lurk programs have identical semantic meaning across backends, with the qualification that Lurk language instances are themselves parameterized on scalar field and hash function. When backends use the same scalar field and hash function, they can be used to generate equivalent proofs. This is because the concrete representation of content-addressed data is fixed.

# Performance

Lurk backend integration is still immature, so current performance is not representative. As a rough approximation, we estimate that for entirely general computation using Lurk's universal circuit, Nova proving throughput will be on the order of 1,000 iterations per second per GPU. We expect that most compute-heavy applications will use optimized 'coprocessor' circuits, which will  dramatically improve performance. Planned improvements to Nova will allow for smaller inner circuits, further improving throughput -- and for full parallelization of reduction proofs.

# Specs
- [Lurk Spec](https://blog.lurk-lang.org/posts/circuit-spec)
- [Evaluation Spec](notes/eval.md)
- [Reduction Notes](notes/reduction-notes.md)

# Security Audit
Lurk's Alpha release has undergone a [security audit](https://blog.lurk-lang.org/posts/alpha-audit/inference-security-assessment-3-2023.pdf) as of 03/29/2023, performed by [Inference](https://inference.ag/about-us/).

# Versioning

Please note that the Lurk language and spec will be versioned independently from the crates that implement the spec. This is necessary because semantic versioning implies different requirements for the language and its implementation. For example, Lurk Alpha is released as crate `lurk 0.2.0` and Lurk Beta is released as crate `lurk 0.3.0`. It is our intention for these two versioning systems to coincide at 1.0.

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
➜  lurk-rs ✗ RUST_LOG=lurk::lem::eval=info bin/lurk
    Finished release [optimized] target(s) in 0.05s
     Running `target/release/lurk`
Lurk REPL welcomes you.
user> (let ((square (lambda (x) (* x x)))) (square 8))
  2023-12-10T15:58:21.902414Z  INFO lurk::lem::eval: Frame: 0
	Expr: (let ((.lurk.user.square (lambda (.lurk.user.x) (* .lurk.user.x .lurk.user.x)))) (.lurk.user.square 8))
	Env:  nil
	Cont: Outermost
    at src/lem/eval.rs:99

  2023-12-10T15:58:21.902943Z  INFO lurk::lem::eval: Frame: 1
	Expr: (lambda (.lurk.user.x) (* .lurk.user.x .lurk.user.x))
	Env:  nil
	Cont: Let{ var: .lurk.user.square, saved_env: nil, body: (.lurk.user.square 8), continuation: Outermost }
    at src/lem/eval.rs:107

  2023-12-10T15:58:21.903170Z  INFO lurk::lem::eval: Frame: 2
	Expr: (.lurk.user.square 8)
	Env:  ((.lurk.user.square . <FUNCTION (.lurk.user.x) (* .lurk.user.x .lurk.user.x)>))
	Cont: Tail{ saved_env: nil, continuation: Outermost }
    at src/lem/eval.rs:107

  2023-12-10T15:58:21.903649Z  INFO lurk::lem::eval: Frame: 3
	Expr: .lurk.user.square
	Env:  ((.lurk.user.square . <FUNCTION (.lurk.user.x) (* .lurk.user.x .lurk.user.x)>))
	Cont: Call{ unevaled_arg: 8, saved_env: ((.lurk.user.square . <FUNCTION (.lurk.user.x) (* .lurk.user.x .lurk.user.x)>)), continuation: Tail{ saved_env: nil, continuation: Outermost } }
    at src/lem/eval.rs:107

  2023-12-10T15:58:21.903678Z  INFO lurk::lem::eval: Frame: 4
	Expr: 8
	Env:  ((.lurk.user.square . <FUNCTION (.lurk.user.x) (* .lurk.user.x .lurk.user.x)>))
	Cont: Call2{ function: <FUNCTION (.lurk.user.x) (* .lurk.user.x .lurk.user.x)>, saved_env: ((.lurk.user.square . <FUNCTION (.lurk.user.x) (* .lurk.user.x .lurk.user.x)>)), continuation: Tail{ saved_env: nil, continuation: Outermost } }
    at src/lem/eval.rs:107

  2023-12-10T15:58:21.903696Z  INFO lurk::lem::eval: Frame: 5
	Expr: (* .lurk.user.x .lurk.user.x)
	Env:  ((.lurk.user.x . 8))
	Cont: Tail{ saved_env: nil, continuation: Outermost }
    at src/lem/eval.rs:107

  2023-12-10T15:58:21.903772Z  INFO lurk::lem::eval: Frame: 6
	Expr: .lurk.user.x
	Env:  ((.lurk.user.x . 8))
	Cont: Binop{ operator: product#, saved_env: ((.lurk.user.x . 8)), unevaled_args: (.lurk.user.x), continuation: Tail{ saved_env: nil, continuation: Outermost } }
    at src/lem/eval.rs:107

  2023-12-10T15:58:21.903844Z  INFO lurk::lem::eval: Frame: 7
	Expr: .lurk.user.x
	Env:  ((.lurk.user.x . 8))
	Cont: Binop2{ operator: product#, evaled_arg: 8, continuation: Tail{ saved_env: nil, continuation: Outermost } }
    at src/lem/eval.rs:107

  2023-12-10T15:58:21.903866Z  INFO lurk::lem::eval: Frame: 8
	Expr: Thunk{ value: 64 => cont: Outermost }
	Env:  nil
	Cont: Dummy
    at src/lem/eval.rs:107

  2023-12-10T15:58:21.903878Z  INFO lurk::lem::eval: Frame: 9
	Expr: 64
	Env:  nil
	Cont: Terminal
    at src/lem/eval.rs:107

[9 iterations] => 64
user> 
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
