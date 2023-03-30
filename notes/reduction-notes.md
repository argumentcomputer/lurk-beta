# Reduction Notes

This document contains general notes about the design, rationale, and implementation of the Lurk reduction step. For a
more normalized (but still WIP) specification, see the [Eval Spec](eval.md)

The [Lurk Language Specification](https://github.com/lurk-lab/lurk/blob/master/spec/v0-1.md) defines evaluation
semantics without specifying the internal data structures or computational steps which an implementation must use to
calculate an evaluation. `lurk-rs` implements a concrete instance of the Lurk language for which proofs of correct
evaluation can be generated. `lurk-rs` generates zk-SNARK proofs for multiple backends, and verification of these
proofs requires reference to a verification key whose identity is derived from the computation encoded in the
corresponding arithmetic circuit. The initial Lurk circuit implementation is specified as a Rank-1 Constraint System
(R1CS), from which Groth16 or Nova proofs are created.

Because the circuit must check the computation to be proved, many aspects of the implementation itself must be fully
specified. The reference implementation of Lurk expression evaluation in
[`eval.rs`](https://github.com/lurk-lab/lurk-rs/blob/master/src/eval.rs) provides an intermediate step between the
high-level specification and the low-level circuit. Not every aspect of the implementation is essential, but every part
which directly corresponds to the layout of the constraint system is.

`eval.rs` provides an `Evaluator` structure, which supports (relatively) fast evaluation of Lurk expressions. This is
valuable when proofs are not required (e.g. if Lurk is being used for its output, or while interactively developing program
code). It also provides an important aid to the circuit-synthesis step. Circuit synthesis does not always
directly mirror a deterministic specification of evaluation. Sometimes it is useful to know 'in advance' what values
will be computed as the result of a step.

This is true in three distinct ways:
1. When preimages for hashes must be non-deterministically supplied.
2. When the immediate result of a 'subroutine' is constrained depending on its inputs, without being directly calculated.
3. When parallelizing synthesis (not currently implemented) of many logically sequential steps.

Taking these one at a time:
1. Because the SNARK-friendly Poseidon hashes (provided by the [Neptune](https://github.com/lurk-lab/neptune)
   library) are relatively expensive, and because Lurk does not provide explicit access to the hash values, we avoid
   computing them during evaluation -- instead relying on the
   [Store](https://github.com/lurk-lab/lurk-rs/blob/master/src/store.rs) to manage cheaper expression pointers in a way
   that preserves equality. All such pointers are resolved to content-addressable tagged hashes before circuit
   synthesis. The Store is used during synthesis when the preimage of a hash known at synthesis needs to be 'looked
   up'.
2. The Witness struct is populated during evaluation and holds values allowing circuit synthesis to 'look ahead' in ways
   that simplify assembling the constraint system.
3. Because evaluation without circuit synthesis and with expensive hashing deferred can be performed quickly, we can
   generate the input/output/Witness values for many reduction steps at once. Synthesis (and proving, if backend allows)
   can then be fully parallelized as desired.


As a matter of interest, we note that the `lurk-rs` evaluator runs about 7x faster than the one implemented in [Common
Lisp](https://github.com/lurk-lab/lurk/blob/master/api/api.lisp). The latter's design does not target speed, and we
make this observation only to support our suggestion that the `lurk-rs` evaluator performs well relative to the cost of
proving. It makes sense to evaluate many frames at a time before proving because doing so is cheap.


## `lurk` (Common Lisp), `(fib 5400)`
```
➜  lurk git:(master) ✗ time bin/lurk lurk-lib/example/fib.lurk
Read from lurk-lib/example/fib.lurk: (LETREC
                                      ((NEXT
                                        (LAMBDA (A B N TARGET)
                                         (IF (EQ N TARGET) A
                                          (NEXT B (+ A B) (+ 1 N) TARGET))))
                                       (FIB (NEXT 0 1 0)))
                                      (FIB 5400))
12830014450854701790553380223424071639959627994639628877157030037091896200381

bin/lurk lurk-lib/example/fib.lurk  2.02s user 0.32s system 98% cpu 2.366 total
```

## `lurk-rs` (Rust), `(fib 5400)`
```
➜  lurk-rs git:(spec) ✗ time bin/lurkrs ../lurk/lurk-lib/example/fib.lurk
    Finished release [optimized] target(s) in 0.06s
     Running `target/release/examples/lurk ../lurk/lurk-lib/example/fib.lurk`
Lurk REPL welcomes you.
Running from ../lurk/lurk-lib/example/fib.lurk.
Read from ../lurk/lurk-lib/example/fib.lurk: ;; (FIB TARGET) computes the element of the Fibonacci sequence at TARGET (zero-indexed).
(letrec ((next (lambda (a b n target)
                 (if (eq n target)
                     a
                     (next b
                           (+ a b)
                           (+ 1 n)
                           target))))
         (fib (next 0 1 0)))
        (fib 5400))

Evaled: 0x1c5d87e5252b038cb7badf6ba7618014c7c16b1541ebece39ab9a40d4f030cbd
bin/lurkrs ../lurk/lurk-lib/example/fib.lurk  0.21s user 0.04s system 74% cpu 0.335 total
```

Because it also highlights an important detail of the formal reduction algorithm, we note that `lurk-rs` evaluation
automatically performs tail-call elimination, which the Common Lisp implementation currently does not. For that reason,
the CL implementation encounters a stack overflow by `(fib 5500)`.


```
➜  lurk git:(master) ✗ time bin/lurk lurk-lib/example/fib.lurk
Read from lurk-lib/example/fib.lurk: (LETREC
                                      ((NEXT
                                        (LAMBDA (A B N TARGET)
                                         (IF (EQ N TARGET) A
                                          (NEXT B (+ A B) (+ 1 N) TARGET))))
                                       (FIB (NEXT 0 1 0)))
                                      (FIB 5500))
INFO: Control stack guard page unprotected
Control stack guard page temporarily disabled: proceed with caution
Fatal condition:
Control stack exhausted (no more space for function call frames).
This is probably due to heavily nested or infinitely recursive function
calls, or a tail call that SBCL cannot or has not optimized away.
```

Meanwhile, `lurk-rs` happily computes `(fib 500000)` in 12 seconds.

```
➜  lurk-rs git:(spec) ✗ time bin/lurkrs ../lurk/lurk-lib/example/fib.lurk
    Finished release [optimized] target(s) in 0.06s
     Running `target/release/examples/lurk ../lurk/lurk-lib/example/fib.lurk`
Lurk REPL welcomes you.
Running from ../lurk/lurk-lib/example/fib.lurk.
Read from ../lurk/lurk-lib/example/fib.lurk: ;; (FIB TARGET) computes the element of the Fibonacci sequence at TARGET (zero-indexed).
(letrec ((next (lambda (a b n target)
                 (if (eq n target)
                     a
                     (next b
                           (+ a b)
                           (+ 1 n)
                           target))))
         (fib (next 0 1 0)))
        (fib 500000))

Evaled: 0x14b327ebbbdfbed3d6f26b3937196b3a7020b2e98c583832fe5fdb33e316aabb
bin/lurkrs ../lurk/lurk-lib/example/fib.lurk  12.14s user 0.40s system 99% cpu 12.656 total
```

This example reveals the general structure of the canonical Lurk expression evaluation algorithm:

- Evaluation takes place through an iterated 'reduction step'.
- Each reduction is either:
  - an identity transformation.
  - a mapping of input to 'more reduced' output.
- Given that Lurk is Turing complete, this does not guarantee termination.
- The reduction step performs a fixed computation, with no recursion. This is necessary so it can be proved in a circuit.
- The reduction is performed in continuation-passing style, which is what allows a complete evaluation to be sliced into
  as many reductions as needed.
- Any Lurk expression whose evaluation *does* terminate will eventually lead to a fixed point of reduction (when the continuation is considered as an input/output of reduction).
- This leads naturally to the tail-call elimination observed above.

