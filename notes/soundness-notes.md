# Soundness Notes

## Functional Commitment Example
This document contains general notes about the soundness of Lurk proofs.

We choose a somewhat elaborate functional commitment code example (lightly modified from [A Programmer's Introduction to
Lurk](https://blog.lurk-lang.org/posts/prog-intro/)) because it exercises many language features.

```
> (letrec ((reduce (lambda (acc f list)
                     (if (eq list nil)
                         acc
                         (reduce (f acc (car list))
                                 f
                                 (cdr list)))))
           (map (lambda (f list)
                  (if (eq list nil)
                      nil
                      (cons (f (car list))
                            (map f (cdr list))))))
           (map-reduce (lambda (map-fn reduce-fn initial list)
                         (reduce initial reduce-fn (map map-fn list))))
           (plus (lambda (a b) (+ a b)))
           (square (lambda (x) (* x x)))
           (secret-function (lambda (data)
                              (map-reduce square plus 0 data))))
    (hide 12345 secret-function))

=> (comm 0x15f813972bc643451de5e87119c272d1f32a4492a7fdc12033c2e6ef29e47e35)
```

The code above first defines two recursive functions (`reduce` and `map`) then uses them in a third function
(`map-reduce`). Then two simple non-recursive functions (`'plus` and `square`) are defined. Then, `secret-function` is
defined as a function which maps `square` over its input, reducing the result with `plus`. That is, `secret-function`
computes the sum of the squares of its input, which must be a list of numbers.

Finally, the entire expression above evaluates to a *hiding commitment* to `secret-function`. That is what makes the
function secret. In this example, `12345` acts as a blinding factor. As long as this value is sampled randomly from the
scalar field, even if an attacker is able to guess the function itself from a tractable set of candidates, she still
will be unable to demonstrate an opening of the commitment.


NOTE: the notation used when displaying a Lurk commitment is `(comm <field-element>)`, but the actual value represented
is just a field element tagged with the `Comm` type -- not a list begining with the symbol `comm`. This representation
is chosen because the `comm` built-in creates commitments from numbers.

```
> (comm 0x15f813972bc643451de5e87119c272d1f32a4492a7fdc12033c2e6ef29e47e35)

=> (comm 0x15f813972bc643451de5e87119c272d1f32a4492a7fdc12033c2e6ef29e47e35)
```

A commitment can be *opened*, returning the original value to which the commitment was made. For this to be possible,
the prover must know the original secret (as well as the original value).

```
> ((open 0x15f813972bc643451de5e87119c272d1f32a4492a7fdc12033c2e6ef29e47e35) '(2 4 7 10))

=> 169
```

Here, we see that the output is exactly as expected when calling the secret funcion. 169 is the sum of the squares (4,
16, 49, 100) of the input. However, we learn nothing *else* about the secret function even when we can fully inspect the
input and output of evaluation.

## Completeness

Although the topic of this document is Lurk's soundness, we note in passing that Lurk proofs are also (claimed to be)
*complete*. By this we mean that for any well-formed Lurk expression, there exists at-most one unique evaluation (which
might be an error). Expressions whose evaluation never terminates cannot be proved, but whenever evaluation *does*
terminate (even if the result is an error), a proof that the result was correctly derived can be obtained.

It follows from the above that Lurk programs are deterministic. For every terminating input there is one and only one
correct eventual output. Future versions of Lurk will introduce a non-deterministic option -- in which a single input
may evaluate to more than one correct output.

In either event, whenever `x` evalutes to `y` (whether `y` is unique or otherwise), it is possible to construct a proof
that convinces a verifier that this is true. We claim that the circuit for the Lurk [reduction
step](reduction-notes.md) is complete in this sense, but will not otherwise address the claim in this document.

## Soundness

Our concern here is that even if it is true that we can prove that `x` evalutes to `y` whenever this is true, it might
also be the case that we can generate a proof that `x` evaluates to `z` when Lurk's evaluation rules do *not* specify
that this is true. In the case of the deterministic subset of Lurk (which is all that is implemented in the
current/initial release), it *cannot* be the case that `x` evalutes to both `y` and `z` -- so any instance of such a
proof would constitute *ipso facto* proof that Lurk proofs are unsound. This would be a show-stopping bug that needs to
be addressed. We frame the discussion in this way to make clear that Lurk auditors must be satisfied that no two such
'contradictory proofs' are obtainable if Lurk is to be declared sound (as we claim).

### Explicit Commitments

In order to trust that `0x15f813972bc643451de5e87119c272d1f32a4492a7fdc12033c2e6ef29e47e35` (we have omitted the `comm`
for brevity, as Lurk allows) really is a binding commitment, we must believe that at most one value can be known to the
prover such that when combined with the secret (`12345`) a preimage hashing to the commitment
(`0x15f813972bc643451de5e87119c272d1f32a4492a7fdc12033c2e6ef29e47e35`) is formed. This means the hash used to construct
the commitment must be proved soundly in the circuit -- and must also be collision resistant. If it is computationally
infeasible to discover a collision, then *at most one* preimage for any given digest can be known. When the digest is
the result of a previous commitment, then the committed value is already known. If it is not, then we assume it is not
possible to find another such value-secret pair. In other words, if a proof of commitment opening can be created at all,
then we claim that the private input used in the proof *must* have been one initially produced via `commit`.

We delegate this claim to [neptune](https://github.com/lurk-lab/neptune) -- Lurk's underlying Poseidon
implementation. Poseidon's cryptographic security is described in [the paper](https://eprint.iacr.org/2019/458.pdf), and
`neptune`'s implementation has been
[audited](https://github.com/lurk-lab/neptune/blob/master/poseidon-in-filecoin-final-report.pdf).

### Implicit Commitments (expressions)

In addition to the explicit commitments described above, Lurk pervasively uses neptune/Poseidon hashes as binding
commitments to compound data. All the same considerations apply to the implicit commitments produced by Lurk's native
hashing.

One important further consideration is that the hash digests produced by implicit commitments provide no blinding
mechanism, so strict hiding is not possible. If an attacker knows a given hash digest corresponds to (for example) one
of just three possible Lurk expressions, it is cheap and easy to hash all three and check the result against the given
digest. This has no effect on soundness, only on data privacy -- but it is still worth noting.

A second consideration which *does* relate directly to soundness is that because Lurk is dynamically typed, any given
'value' could be of any type. If explicit type information were not a part of every expression's concrete
representation, then soundness could be violated. Lurk resolves this problem by representing every datum as *two* field
elements -- one that uniquely specifies the expression's *type* and one that specifies the value. Note that the data
element for some types is 'immediate', and that for others is a hash digest.

What this means is that interpretation of a 'data element' requires a 'type tag element'. An example will make this
clearer. Since the example includes counter-factual representation different from those Lurk actually uses, we will
use a notional hash function whose hash digests we will simply declare here for example purposes.

Suppose Lurk had only two expression types, Number (field element) and Cons (pair). We might imagine we could then
represent Numbers literally, and use binary hashes to produce pairs -- using a single field element for values of either
type. We certainly could produce such data. For example the pair `(1 . 2)` might be produced by computing `H(1, 2)` where
`H` is our hash function. For sake of example, assume `H(1, 2) = 98765`. We could then produce a new value resulting
from consing 3 onto the head of the resulting pair: `H(3, 98765)` would then represent `(3 2 . 1)`. For sake of example,
assume `H(3, 98765)` is `34567`.

Now we have (simplistically) accomplished the goal. We have a value (`34567`) that results from `H(3, H(1, 2))`. We can
use these leaf values as preimages and *prove* (in zero-knowledge) that the final value was correctly calculated.
Furthermore, we can construct the root hash of any such binary Merkle tree in the same way. In that sense, this
serialization would be complete. However, such an approach introduces a soundness problem because of the second preimage
attack on the Merkle tree itself. Even if the underlying hash is secure, we have no way of distinguishing the *shape* of
the tree based on the hashes. In this concrete example, there is no way to distinguish between `H(3, H(1, 2))` and `H(3,
98765)`. This means that a prover could treat the content-address `34567` as corresponding to either the expression `(3
1 . 2)` *or* the expression `(3 98765)` at her whim.

At the risk of overexplaining, this would violate Lurk soundness because we would then be able to prove both
 - `(cdr <34567>) => (1 . 2)` *and*
 - `(cdr <34567>) => 98765`

But `(1 . 2)` is *not* equivalent to `98765`. One is a cons and the other is a number. Therefore, a prover's ability to
interpret the expression's content address as a type of her choosing is the underlying problem. Lurk addresses this
problem by specifying that every expression be represented by *two* field elements: a type tag and a value. When the
expression's type is one which represents compound data (as in the case of a cons, for example), the value is a poseidon
hash digest. When the expression's type is immediate data (as in the case of a number, i.e. field element), the value is
simply the data.

Another way to think of this is that the type tag uniquely identifies the function used to derive the content-address
from the expression. Immediate values are derived with the identity function, and compound values are derived by hashing
their constituents (both type and value elements) using a hash of appropriate arity and a type-specific preimage layout.

For example, an actual Lurk cons has type tag
[`0x01`](https://github.com/lurk-lab/lurk-rs/blob/a1242270a1285c15b7edb0ab1440f2247f950ead/src/store.rs#L2790), and its
value is `P4(t0, v0, t1, v1)` -- where `P4` is a 4-ary Poseidon hash, `t0` is the type tag of the first paired
expression, `v0` is the value element of the first paired expression, `t1` is the type tag of the second paired
expression, and `v1` is the value element of the second paired expression.

### Implicit Commitments (continuations)

In addition to first-class Lurk expressions, an equivalent tag and value hashing approach is used for the compound data
representing continuations. We make this distinction because in the current version of Lurk, continuations are not first
class. That is, they cannot be used as expressions or subexpressions. They do appear as input/output to Lurk's
evaluation and reduction functions, though. In the future continuations *may* be treated as first class, and their type
tags are disjoint from those of expressions for that reason.

Note that all continuations use the same underlying hash, but different continuation types (each with its own tag) lay
out the preimage differently. Continuations, in this sense, act somewhat like a tagged union (e.g. Rust's enum).

## Mutually-exclusive Case

Throughout the circuit implementation, we make use of a `case` gadget, along with a more elaborate `multicase` built from
the simple `case`. The former allows selection of a single value from multiple alternatives, based on the identity of a
tested key (a field element). The latter allows association of multiple values with each key. Both gadgets include a
default to be selected if the key does not match any of the candidates.

Soundness requires that for any given key, *only one* value can be produced. This means that correct use of the `case`
and `multicase` gadgets requires that duplicate keys not be provided. In general, these components should be audited
carefully to ensure that multiple contradictory proofs cannot be obtained for a single key. One example of how this
might happen if the implementation were flawed is that it might be possible for the prover to select the default value
even when the key does in fact match one of the specified candidates. A correct `case` gadget must prevent this
possibility.

## Other possibilities

The circuit is tested against a set of Lurk programs, such that we ensure the circuit output corresponds to the expected
output. One generic way to satisfy this requirement, but without soundness, is to compute the expected output outside of 
the circuit, and allocate variables in the circuit containing this information that, from the circuit's perspective, came from 
nowhere. Although the set of tests is going to pass, the circuit is not sound, because the intermediate steps to calculate the 
output where not completely constrained. Hence, along the audit process, it is important to verify if all the intermediate 
steps are indeed implemented inside the circuit, using subcircuits and other gadgets that fully computes their expected results, 
without leaving unconstrained intermediate steps. 

## Conclusion

The above is not exhaustive, but it is a good starting point for reasoning about what Lurk proofs claim and how those
claims might prove unsound if the implementation or design are flawed.
