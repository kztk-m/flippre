# flippre: FliPpr, embedded 

This is an embedded implementation of FliPpr, an invertible pretty-printing system. The library provides functions and the datatypes so that one can write their pretty-printers that are akin to the usual functional programming style as possible, and invertible to produce CFG parsers. (The current implementation uses `Earley` for parsing.)

This repository consists of four packages:

* [`flippre`](./flippre) The embedded FliPpr system.
* [`flippre-examples`](./flippre-examples) Some invertible pretty-printers defined in the system.
* [`flippre-grammar-backend`](./flippre-backend-grammar) Internally used for grammar-processing in FliPpr.
* [`mutual-def-class`](./mutual-def-class) Internally used for observable mutually-recursive definitions.

## Build Instruction

You can use `stack` or `cabal`.

### Stack

```console
stack build
```

### Cabal

```console
cabal build all
```

## Examples

Some examples can be found in the `flippre-examples` directory. For example, [Arith.hs](./flippre-examples/Arith.hs) implements an invertible pretty-printer for simple arithmetic expressions. One can play with such examples by loading it in REPL, by

```console
stack repl flippre-examples:exe:arith 
```

or

```console
cabal repl arith
```

## Publications

* Kazutaka Matsuda, Meng Wang: [Embedding invertible languages with binders: a case of the FliPpr language](https://doi.org/10.1145/3242744.3242758). Haskell Symposium 2018: 158-171
* Kazutaka Matsuda, Meng Wang: [FliPpr: A System for Deriving Parsers from Pretty-Printers](https://doi.org/10.1007/s00354-018-0033-7). New Generation Computing 36(3): 173-202 (2018)
* Kazutaka Matsuda, Meng Wang: [FliPpr: A Prettier Invertible Printing System](https://doi.org/10.1007/978-3-642-37036-6_6). ESOP 2013: 101-120

