# flippre: FliPpr, embedded 

`flippre` is an embedded implementation of FliPpr, an invertible pretty-printing system. The library provides functions and datatypes that enable you to define pretty-printers in a functional programming style while ensuring they remain invertible to produce context-free grammar (CFG) parsers. (The current implementation relies on the `Earley` library for parsing.)

This repository consists of four packages:

* [`flippre`](./flippre): The embedded FliPpr system.
* [`flippre-examples`](./flippre-examples): Examples of invertible pretty-printers defined using FliPpr.
* [`flippre-grammar-backend`](./flippre-backend-grammar): Internally used for grammar processing within FliPpr.
* [`mutual-def-class`](./mutual-def-class): Internally used for observable mutually recursive definitions.

## Build Instructions

You can build the project using either `stack` or `cabal`.

Using `stack`:

```console
stack build
```

Using `cabal`

```console
cabal build all
```

## Examples

You can find examples in the `flippre-examples` directory. For instance, For instance, [Arith.hs](./flippre-examples/Arith.hs) demonstrates an invertible pretty-printer for simple arithmetic expressions. You can experiment with these examples in a REPL as follows:

Using `stack`:

```console
stack repl flippre-examples:exe:arith 
```

Using `cabal`:

```console
cabal repl arith
```

## Publications

* Kazutaka Matsuda, Meng Wang: [Embedding invertible languages with binders: a case of the FliPpr language](https://doi.org/10.1145/3242744.3242758). Haskell Symposium 2018: 158-171
* Kazutaka Matsuda, Meng Wang: [FliPpr: A System for Deriving Parsers from Pretty-Printers](https://doi.org/10.1007/s00354-018-0033-7). New Generation Computing 36(3): 173-202 (2018)
* Kazutaka Matsuda, Meng Wang: [FliPpr: A Prettier Invertible Printing System](https://doi.org/10.1007/978-3-642-37036-6_6). ESOP 2013: 101-120
