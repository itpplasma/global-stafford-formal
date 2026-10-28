# Global Stafford formalization

A Lean 4 and Mathlib proof of Stafford's same-divisor identity in the ring of
differential operators of a smooth affine variety. It extends the Weyl-algebra
case (Stafford's Conjecture 3.8, formalized in
[stafford38-formal](https://github.com/itpplasma/stafford38-formal)) to every
smooth integral affine variety over a field of characteristic zero.

Status: the formal proof is complete; independent human review of the
mathematics is pending.

## The theorem

Let `k` be a field of characteristic zero, `A` a smooth integral finitely
generated `k`-algebra, and `D_k(A)` the ring of `k`-linear finite-order
(Grothendieck) differential operators on `A`, with composition as product.
For every nonzero `d ∈ D_k(A)` there are `F, R, S ∈ D_k(A)` with

```text
1 = d R + F d S.
```

The written order is kept. For `A = k[x₁, …, xₙ]`, `D_k(A)` is the Weyl
algebra and the statement is Stafford's Conjecture 3.8. The proof here is a
local-to-global argument over étale charts that reduces to the Weyl case.

## What is formalized

- `GlobalStafford.universalStatement` (`GlobalStafford/Assembly/Closure.lean`):
  the theorem for the intrinsic algebra of finite-order differential
  operators.
- `GlobalStaffordChallenge.universalStatement`: the same statement written
  with Mathlib-only definitions in `GlobalStaffordChallenge.lean` (identical
  copy in `Challenge.lean`), proved in `GlobalStaffordSolution.lean` /
  `Solution.lean` by transport, without importing the challenge.

The project declares no axioms. The only `sorry`s are the intentional
placeholders in `Challenge.lean` and `GlobalStaffordChallenge.lean`, which
state the theorem for comparison against the solution. `scripts/verify.sh`
checks that both endpoints in `docs/endpoints.txt` depend only on `propext`,
`Classical.choice` and `Quot.sound`, including through the dependencies.

## Building and checking

Requires [elan](https://github.com/leanprover/elan). The pins are Lean
`leanprover/lean4:v4.33.0` (`lean-toolchain`) and, in `lakefile.toml`,
Mathlib, [AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis)
and [stafford38-formal](https://github.com/itpplasma/stafford38-formal);
Lake fetches them into `.lake/packages/`.

```sh
lake exe cache get
lake build
scripts/verify.sh
```

Do not run `lake update`; it would move the pins. More detail, including the
Phase I verifier mode and the TeX dossier build, is in
[docs/building.md](docs/building.md).

## Documentation

- [Paper/Lean correspondence](docs/paper-lean-specification.md).
- [Literature and proof index](docs/literature.md): citations, their role in
  the proof, and the Lean modules that use them.
- [Provenance, prior art and novelty](docs/provenance-literature-novelty.md).
- [Building and verification](docs/building.md) and the
  [verification record](docs/verification.md).
- [TeX dossier](docs/dossier/global-stafford-dossier.tex)
  ([PDF](docs/dossier/global-stafford-dossier.pdf)): proof map and the
  challenge/solution comparison.
- [Release notes](docs/release-notes.md).

The theorem is registered in the Palomar registry as
[PALOMAR-2026-09-09-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-09-09-000001&version=2).

## Related projects

- [stafford38-formal](https://github.com/itpplasma/stafford38-formal): the
  Weyl-algebra case, a dependency.
- [algebraic-analysis](https://github.com/itpplasma/algebraic-analysis):
  reusable Lean library, a dependency.

## Citing and license

Citation metadata is in [CITATION.cff](CITATION.cff). Christopher Albert is
the author and maintainer; AI systems assisted under his direction, as
recorded in `formalization.yaml`. Licensed under Apache-2.0 ([LICENSE](LICENSE),
[NOTICE](NOTICE)).
