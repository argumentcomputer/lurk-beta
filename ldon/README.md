# LDON: Lurk Data Object Notation

The Lurk Data Object Notation, or LDON (pronounced "[Ladon](https://en.wikipedia.org/wiki/Ladon_(mythology)"), is a content-addressable linked data format designed for zero knowledge contexts, such as the Lurk zkSNARK language.

LDON is a simple syntax over Lurk expressions, and is compatible with JSON and IPLD.

The primary distinction between LDON and Lurk proper is that LDON makes no assumptions about reserved symbols or reduction rules. 

For example, the ldon expression `(:lambda (x) x)` corresponds to the Lurk expression `(lambda (x) x)`, but in Lurk this will evaluate to a function object, whereas `ldon` considers expressions to be static. Furthermore, `ldon` is agnostic to what is built on top of it. One could define a language with evaluation rules totally different from lurk, where functions are built out of expressions that look like the `ldon` expression `(:fun x :=> x)`.

LDON syntax is defined as follows:

```rust
pub enum Syn<F: LurkField> {
  // A field element: 1, 0xff
  Num(Pos, F),
  // A u64 integer: 1u64, 0xffu64
  U64(Pos, u64),
  // A hierarchical symbol: foo, foo.bar.baz
  Symbol(Pos, Vec<String>),
  // A hierarchical keyword: :lambda, :lurk:lambda
  Keyword(Pos, Vec<String>),
  // A string literal: "foobar", "foo\nbar"
  String(Pos, String),
  // A character literal: 'a', 'b', '\n'
  Char(Pos, char),
  // A cons-list of expressions, which can be terminated by nil: (1 2 3)
  // or can be terminated with the right-most expression (1, 2, 3)
  List(Pos, Vec<Syn<F>>, Option<Box<Syn<F>>>), 
  // A map of expressions to expressions: { foo = 1, blue = true, 3 = 4 }
  Map(Pos, Vec<(Syn<F>, Syn<F>)>),
  // A contextual link or descriptor of some piece of foreign data:
  // [sha256 0xffff_ffff_ffff_ffff 0xffff_ffff_ffff_ffff 0xffff_ffff_ffff_ffff 0xffff_ffff_ffff_ffff]
  Link(Pos, Box<Syn<F>>, Vec<u64>),
}
```
