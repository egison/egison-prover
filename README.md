# Egison Prover

Egison with a dependent type system

## Design and implementation status

The proposed language lets theorem statements describe structures with patterns,
and uses the same patterns to extract witnesses in proofs.
See the [design overview](design/overview.md) and the
[current design review](design/review.md).
Examples using patterns inside equality proofs and induction are described in
[fixed-point-free involutions](design/pwl-involution.md) and
[patterns within proofs](design/pwl-proof-steps.md).

The Haskell implementation is a dependent-type-checking prototype using
the syntax in `sample/*.pegi`. The examples in `sample/pmop/*.pmop` are design
sketches; `matches`, `exhaustive by`, and the proposed matchers are not implemented
by the current parser and checker.

## How to test

```
cabal build
cabal exec egison-prover -- sample/test.pegi
```
