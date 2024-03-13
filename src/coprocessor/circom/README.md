# Circom Coprocessor

The [Circom](https://github.com/iden3/circom) Coprocessor is a special Coprocessor that is included in our library. It 
allows users to use Circom-based circuits in a folding step, alongside the Lurk reduction process. This feature
pushes forward the flexibility of our stack and opens it up to a myriad of developer and researchers already familiar
with this particular programing language.

## Overview

There are two key components to have in mind when thinking about the Circom Coprocessor:
- `CircomCoprocessor`: The shim that exposes a Circom gadget as a Lurk Coprocessor. It leverages [`circom-scotia`](https://github.com/lurk-lab/circom-scotia)
to compile Circom-based circuits to [Bellpepper](https://github.com/lurk-lab/bellpepper), thus making them usable in our stack.
- `CircomGadget`: The Circom gadget proper. Refers to the r1cs and wasm files compiled from the targeted
circom circuit that will be used in our proving flow. Those compiled files can live either locally or in a Github release.

## Circom Gadgets

A `CircomGadget` is an interface that allows our `CircomCoprocessor` to prepare everything needed to use `circom-scotia`.
It has 3 main purposes:
1. Redirect to Circom assets: The compiled r1cs and wasm files from Circom can currently live either on the local file 
system or on a remote Github release. We will detail later on how this works.
2. Input conversion: A defined way to take a list of Lurk input pointers and turn them into a Circom input. We do not 
enforce the shapes of either the Lurk end or the Circom end, so users should take care to define what shape they expect.
3. Evaluation logic: A defined way *Lurk* should evaluate what this gadget does. This is then the implementation used in
the `Coprocessor` trait.

### Compiled Circom files location

The r1cs and wasm files can live either directly on the local file system or on a remote Github 
repository.

For local import of Circom circuits the Lurk CLI can be used. In short, it will directly compile the pointed Circom circuit
and make the files available to the `CircomCoprocessor` if they are correctly referenced by its inner `CircomGadget`.

For remote gadgets, the `CircomCoprocessor` will use the _reference_  of the `CircomGadget` to search a corresponding 
Github repository. In this case, there are a few constraints that needs to be followed:
1. _reference_ format:  **must** be formatted as `<AUTHOR>/<NAME>` as would a Github repository
2. Compiled Circom files available in a release: the compiled circom files, r1cs and wasm, **must** be made available in an release
in the repository. To help fulfill this constraint, we provide [a template of a Gadget repository](https://github.com/lurk-lab/template-circom-gadget).
3. Compiled Circom files names: The name of the compiled circom files **must** be the same as the repository (e.g.: `lurk-lab/keccak` -> `keccak.wasm` & `keccak.r1cs`).
This effectively limits the number of circuit available per repository to one.
4. _version_ specification: As we are looking for file in a specific release the `CircomGadget` **must** be specified with
a correct release version.
If all these constraints are passed, the `CircomCoprocessor` will import the circuit in the local file system to use it 
later on.

In the computation flow of the `CircomCoprocessor`, it will by default look first in the local file system to check if the
specified gadget already exists. This allows us to skip any cumbersome interaction with a remote host.
