# chain-server

A server for proving chained calls built on top of Lurk.

### Initiating the server with a functional commitment

Go to Lurk's REPL and persist the commitment to the chaining function:

```lisp
!(commit (letrec ((add (lambda (counter x)
                          (let ((counter (+ counter x)))
                            (cons counter (commit (add counter)))))))
            (add 0)))
```

Initiate the server with

```
$ cargo run --release --bin server --\
  init 0x2b444b40b27bac0dff8416c0f3c708a505a636d86ba66bdbe86497c515afb651 --comm --port 50051
```

Where `0x2b444b40b27bac0dff8416c0f3c708a505a636d86ba66bdbe86497c515afb651` is the hash of the functional commitment.

### Initiating the server with a regular function as the callable state

Go to Lurk's REPL and persist a the chaining function as Lurk data:

```lisp
!(dump-data (letrec ((add (lambda (counter x)
                          (let ((counter (+ counter x)))
                            (cons counter (add counter))))))
              (add 0))
            "my-function")
```

Initiate the server with

```
$ cargo run --release --bin server -- init my-function --port 50051
```

### Initiating the demo client

Once the server is alive, run

```
cargo run --release --bin client -- 50051
```