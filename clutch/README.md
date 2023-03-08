# Lurk Clutch

Clutch is a hatchery where nascent Lurk abstractions incubate. Clutch manages the friction point allowing seamless shifting
of loosely-coupled gears.

Clutch depends on both Lurk and fcomm. It provides a REPL that is a superset of `lurkrs`, and makes some of `fcomm`
available from the REPL.

In the future, it will likely also included expanded CLI features. It is expected that code will migrate between these
(and other) crates as eventual structure is concretized.

Ideally, the `clutch` binary will eventually converge on being the most useful tool for using Lurk. Along the way, it
should be viewed as a fast-moving prototype where ideas can be implemented and evolve quickly.
