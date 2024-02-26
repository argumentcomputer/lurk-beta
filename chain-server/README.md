# chain-server

A server for proving chained calls built on top of Lurk.

### Initiating the server with a functional commitment

Go to Lurk's REPL and persist the commitment to the chaining function:

```lisp
!(commit
  (letrec
      ((sum (lambda (xs acc)
              (if (eq xs nil) acc (sum (cdr xs) (+ acc (car xs))))))
       (add (lambda (counter xs)
              (let ((counter (+ counter (sum xs 0))))
                (cons counter (commit (add counter)))))))
    (add 0)))
```

Initiate the server with

```
$ cargo run --release --bin server --\
  init 0x1653706ed881366619d2334fc2175c28e1a74b8ae6a8b9cc230026371e187bd6 --comm --port 50051
```

Where `0x1653706ed881366619d2334fc2175c28e1a74b8ae6a8b9cc230026371e187bd6` is the hash of the functional commitment.

### Initiating the server with a regular function as the callable state

Go to Lurk's REPL and persist a the chaining function as Lurk data:

```lisp
!(dump-data
  (letrec
      ((sum (lambda (xs acc)
              (if (eq xs nil) acc (sum (cdr xs) (+ acc (car xs))))))
       (add (lambda (counter xs)
              (let ((counter (+ counter (sum xs 0))))
                (cons counter (commit (add counter)))))))
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

Here is the output of a short interaction with it:

```
> '(2 5)
(<Opaque Comm 0x1653706ed881366619d2334fc2175c28e1a74b8ae6a8b9cc230026371e187bd6> (quote (2 5)))
↳ (7 . <Opaque Comm 0x0ce3e1327f55140ca254cbdbe3309c500ed00e59b37c5020a626ad69c2eec0c8>) ✓
> '(13 17)
(<Opaque Comm 0x0ce3e1327f55140ca254cbdbe3309c500ed00e59b37c5020a626ad69c2eec0c8> (quote (13 17)))
↳ (37 . <Opaque Comm 0x2d2db778abf5454a4b49e3ac7608d3d9ad579dfe420e17ddc569e6cb9123f1c0>) ✓
```
