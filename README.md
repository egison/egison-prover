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
[Clarity and proof size](design/proof-brevity.md) uses Ramsey as a reference for
making selected structures, their relations, and subsequent reasoning visible.
It also examines proof size, with checked examples of inverse-pair deletion and
induction over the number of selected pairs.
[Further examples](design/pwl-readable-proofs.md) show complementary literals in
resolution proofs and a shared vertex when inserting a closed walk into another walk.
The [complete examples](design/examples/README.md) also include both presentations
of Cauchy–Binet, weighted LGV, and the Euler-circuit criterion, with all helper proofs.
Their Lean proofs and manual expansions of the proposed patterns are checked;
the `.pmop` parser and its translation into proof terms remain to be implemented.
The adapted LGV sources retain their upstream
[CC BY-NC 4.0 license](design/examples/LICENSE-AlgebraicCombinatorics), separately
from the rest of the repository.

The Haskell implementation is a dependent-type-checking prototype using
the syntax in `sample/*.pegi`. The examples in `sample/pmop/*.pmop` are design
sketches; `matches`, `exhaustive by`, evidence-carrying `matchAll`, and the proposed
matchers are not implemented by the current parser and checker.

## How to test

```
cabal build
cabal exec egison-prover -- sample/test.pegi
```
