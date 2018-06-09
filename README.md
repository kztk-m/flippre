# flippre: FliPpr, embedded 

This is an embedded implementation of FliPpr, an invertible
pretty-printing system. The library provides functions and the
datatypes so that one can write their pretty-printers that are akin to
the usual functional programming style as possible, and invertible to
produce CFG parsers. The current implementation uses `Earley` for
parsing.

## Build Instruction 

This haskell package is managed via stack. So just type

    stack build
    
to build the library. Some, examples are given under `bench`
directory. For example, to access arithmetic expressions, type: 

    stack repl flippre:bench:arith
    
    

