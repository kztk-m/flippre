# Discussion about `mustNotFollow`

author: Kazutaka Matsuda 
date: 2024-12-10

In parsing, we sometimes expect lexical analysis should perform greedy matching, and it is well-known that such kind of matching can be mimicked by using negative look-ahead. 

For example, consider a regular expression `[a-zA-Z][a-zA-Z0-9]*`, which is supposed to be used to match identifiers. However, as we assume full CFG recognizer, we cannot assume greedy behavior. A remedy is to use negative look-ahead.

```text
ident = [a-zA-Z][a-zA-Z0-9]* ?![a-zA-Z0-9]
```

In general, if a lexical element is recognized by an DFA `A = (q0, F, tr)`, We will use the following grammar to mimic the greedy matching.

```text
  (q0, q1, tr) ?! (q1, F, tr)
| (q0, q2, tr) ?! (q2, F, tr)
...
| (q0, qn, tr) ?! (qn, F, tr)
```

with `F = {q1,...,qn}`. Intuitively, it says, after matching, it cannot return to the final state again. 

A technical issue is that, if we extend FliPpr with `mustNotFollow`, we need to incorporate it with pretty-printer and grammar processing.

## Pretty-Printing

Looking at the code of `prettyprinter`, `FlatAlt` will be used to determine the behavior of `group`. The core layout algorithm `layoutWadlerLeijen` only uses `x` of `FlatAlt x y`. This suggests the approach to that once we freeze `mustNotFollow` and then thaw it after the whole `Doc` is built.

So, the easiest would be to represent it as `ann` for a while and then thaw it afterwards, believing that it will not break the assumption of `Union`.

## Parsing

The current space processing algorithm does not work well is `mustNotFollow`. For example, while we can merge `sp* <> sp*` into `sp*`, where `sp*` stands for zero-or-more spaces, it is hard to merge two `sp*` of `sp* <> mustNotFollow a <> sp*` into one, because the current algorithm does not assume concrete representation of `sp`. 
