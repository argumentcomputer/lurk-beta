# fcomm: Functional Commitments

## This example is a work in progress, for demonstration purposes only, and subject to change.

The `fcomm` CLI exposes an interface for creating and verifying Lurk proofs, and for manipulating functional commitments.

# Functional Commitments
TODO: Explanation of functional commitment interface.

# Creating and Verifying Evaluation Proofs

To see how proofs work, first navigate to the `fcomm/examples` directory. From the `lurk-rs` project root,
```bash
➜  lurk-rs git:(master) ✗ cd fcomm/examples
➜  examples git:(master) ✗
```

To generate a very simple proof, type the following command (this will be surprisingly slow):

```bash
> make fibonacci-proof
```

To see the program whose evaluation was proved, see its [source](examples/fibonacci.lurk).

To see what the generated proof object claim's to attest, see the claim section of the generated json. This can be viewed more legibly if you have a JSON formatter like `jq` installed:

```bash
➜  examples ✗ cat fibonacci-proof.json| jq | more
```

Yielding something like:
```json
{
  "claim": {
    "Evaluation": {
      "expr": "(LETREC ((NEXT (LAMBDA (A B N TARGET) (IF (EQ N TARGET) A (NEXT B (+ A B) (+ 1 N) TARGET)))) (FIB (NEXT 0 1 0))) (FIB 1))",
      "env": "NIL",
      "cont": "Outermost",
      "expr_out": "1",
      "env_out": "NIL",
      "cont_out": "Terminal",
      "status": "Terminal",
      "iterations": null
    }
  },
  "proof": {
    "Recursive": {
      ...
    }
  }
}


To verify the generated proof:

```bash
> make verify-fibonacci-proof
```

Please note the following limitations:
- Proof as serialized here are not optimized for size.
- The Groth16 and SnarkPack+ parameters used here were not the result of a trusted setup so are insecure.
- To simplify reproducibility in development and for example purposes, these parameters are deterministically generated on-demand.
- The parameters are currently uncached.
- This adds time to both proof and verification.
- For larger values of the `ReductionCount` option (see: [lib.rs](src/lib.rs)), this can be significant.
- Even for the smallest circuits used in the default examples, this leads to deceptively slow verification.

To see the commands that were used, see the [Makefile](examples/Makefile).
