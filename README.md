# Egison Prover

A proof language for describing structural selections and decompositions with patterns.

## Design and implementation status

The proposed language uses the same patterns in theorem statements and proofs.
A matcher defines a decomposition relation; a successful match supplies selected
values and evidence of that relation. The current mathematical example is
**Ramsey's theorem R(3,3)=6**, including the six-vertex upper bound and the
five-vertex counterexample.

- [Design overview](design/overview.md)
- [Ramsey comparison](design/pwl-ramsey.md)
- [Conditions for concise proofs](design/proof-brevity.md)
- [Implicit pattern conditions](design/implicit-conditions.md)
- [Implementation review and remaining work](design/review.md)
- [Complete sources and verification](design/examples/README.md)

Proposed proofs retain pattern conditions implicitly and supply binding values
when proving a matching proposition. Obtaining conditions from matcher
definitions, combining them, and constructing proof terms remains to be designed.
The ordinary Lean proofs and manual expansions of the patterns check the
mathematical arguments; they do not implement translation of the proposed syntax.
The comparison must include helper definitions, coverage proofs, and the same
automation on both sides before drawing conclusions about proof size.

The Haskell implementation is a dependent-type-checking prototype using
`sample/*.pegi`. The entry points in `sample/pmop/` refer to the proposed Ramsey
sources; `matches`, `exhaustive by`, and the proposed matchers are not implemented
by the current parser and checker.

## How to test

```sh
cabal build
cabal exec egison-prover -- sample/test.pegi
```

For the mathematical example, run from `design/examples/lean/`:

```sh
lake build
lake env lean Audit.lean
```
