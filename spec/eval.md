Spec for `eval.rs`
-----------------

The Evaluator consists of an expression, an environment, a store and an iteration limit.

The `eval` function evaluates the expression in the environment, growing the store, for a number of reduction steps at most stopping at the iteration limit.

The environment provides bindings between variables and values in lexical scope.

The store keeps track of all objects created. This is where `cons` becomes `hash-cons`.
The store is mutable.

Inputs and outputs (IO) consist of an expression, an environment and a continuation, all represented as pointers to the store.

The continuation represents the rest of the computation.
Continuations are defunctionalized, so there is one continuation per possible rest of computation.
Initially, the continuation is outermost.

A frame consists of an input, an output, a sequence index and a witness.

The witness consists of output expression, environment and continuation, and extended closure, and a continuation continuation (which is redundant, but only present if the control was tagged with continuation).
The witness remembers results that can be used in proofs.

In one reduction step, a frame steps to the next frame, threading the store.

The reduction rules specify the semantics of taking a step.
A step takes an input and a store to an output and a witness.

To simplify the translation to circuits, the implementation of reduction wraps the output in a `Control`, tagging it with `Return`, `MakeThunk` or `ApplyContinuation`.
In reduction:
- The tag `Return` is used in most cases, in particular where a new continuation is formed.
- The tag `MakeThunk` is used for unary and binary operations. When a thunk is not used, this allows for some optimizations with respect to tail and outermost continuations.
- The tag `ApplyContinuation` is used to return immediately with the input continuation.

To understand the detailed semantics, we defer to the case analyses in `reduce_with_witness` and `apply_continuation`.
