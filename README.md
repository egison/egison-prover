# Egison Prover

A proof language for describing structural selections and decompositions with patterns.

## Design and implementation status

The proposed language uses patterns both in theorem statements and within proofs.
Matching extracts values together with evidence of their relations, for use in
equality reasoning, induction, and applications of other theorems.
See the [design overview](design/overview.md) and the
[current design review](design/review.md).
Examples using patterns inside equality proofs and induction are described in
[fixed-point-free involutions](design/pwl-involution.md) and
[patterns within proofs](design/pwl-proof-steps.md).
[Conditions for shorter proofs](design/proof-brevity.md) examines nested selections
that retain evidence in their results, with checked examples of inverse-pair
deletion and induction over the number of selected pairs.

The Haskell implementation is a dependent-type-checking prototype using
the syntax in `sample/*.pegi`. The examples in `sample/pmop/*.pmop` are design
sketches; `matches`, `exhaustive by`, evidence-carrying `matchAll`, and the proposed
matchers are not implemented by the current parser and checker.

## How to test

```
cabal build
cabal exec egison-prover -- sample/test.pegi
```
