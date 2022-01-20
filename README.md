# Lurk

[![Build Status][build-image]][build-link]
![minimum rustc 1.56][msrv-image]

## Nix

[Nix](https://nixos.org) provides a declarative, content addressed and deterministic build system.

### Loading the build environment with all dependencies

```
nix develop
# Or automatically with direnv
direnv allow
```

### Build the crate
```
nix build .
```

### Run the example 

```
nix run .#lurk-example
```

## Repl

```
cargo run --example lurk
```

Or, especially if you have `rlwrap` installed for a better command-line interface:

```
bin/lurkrs
```

[build-image]: https://github.com/lurk-lang/lurk-rs/workflows/CI/badge.svg
[build-link]: https://github.com/lurk-lang/lurk-rs/actions?query=workflow%3ACI+branch%3Amaster
[msrv-image]: https://img.shields.io/badge/rustc-1.56+-blue.svg
