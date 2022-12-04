# LDON: Lurk Data Object Notation

The Lurk Data Object Notation, or LDON (pronounced
"[Ladon](https://en.wikipedia.org/wiki/Ladon_(mythology)"), is a
content-addressable linked data format designed for zero knowledge contexts,
such as the Lurk zkSNARK language.

LDON is a simple syntax sugar over Lurk expressions, and is compatible with JSON and IPLD.

The primary distinction between LDON and Lurk proper is that LDON makes no
assumptions about reserved symbols or reduction rules. 

For example, the ldon expression `(:lambda (x) x)` corresponds to the Lurk
expression `(lambda (x) x)`, but in Lurk this will evaluate to a function
object, whereas `ldon` considers expressions to be static. Furthermore, `ldon`
is agnostic to what is built on top of it. One could define a language with
evaluation rules totally different from lurk, where functions are built out of
expressions that look like the `ldon` expression `(:fun x :=> x)`.

