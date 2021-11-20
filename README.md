# Rupicola: Relational Compilation for Performance-Critical Applications

To compile, run `make` in this directory.
The only dependency is Coq (we use version 8.13, but 8.12 and 8.14 should work as well).

Rupicola's core and standard library are in `src/Rupicola/Lib/`.
Examples and benchmarks are in `src/Rupicola/Examples/`.

The `IPChecksum` example is in `src/Rupicola/Examples/Net/IPChecksum`; see esp. the `Spec.v`, `Impl.v`, and `IPChecksum.v` files.

The relational compiler for expressions is mostly self-contained and rather readable; see `src/Rupicola/Lib/ExprCompiler.v` and contrast it with `src/Rupicola/Lib/ExprReflection.v` (the former, reflection-based compiler).
