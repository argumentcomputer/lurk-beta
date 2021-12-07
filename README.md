# Lurk

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
