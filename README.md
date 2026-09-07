# Global Stafford for rings of differential operators: Lean 4 formalization

For every field `k` of characteristic zero, every smooth integral finitely
generated `k`-algebra `A`, and every nonzero `k`-linear finite-order
differential operator `d` on `A`, there exist differential operators
`F, R, S` on `A` with

```text
1 = d R + F d S.
```

Products are compositions and the written order is kept. Over a polynomial
ring `A = k[x_1, …, x_n]` the ring of differential operators is the Weyl
algebra and the statement is Stafford's Conjecture 3.8, whose Lean proof is
the separate public repository
[stafford38-formal](https://github.com/itpplasma/stafford38-formal); this
repository extends it to every smooth integral affine variety by a
source-changing local-to-global argument.

## Status

Formalization in progress. [`PLAN.md`](PLAN.md) is the live plan: Phase I
proves every project-owned step over the intrinsic differential-operator
carrier with the literature inputs as explicit hypotheses; Phase II
discharges those hypotheses from Mathlib and the pinned dependencies;
Phase III packages the Palomar Challenge/Solution pair and the independent
verification. Nothing is verified yet, and no release, registration or
publication is claimed.

[`Challenge.lean`](Challenge.lean) states the theorem with Mathlib only
(`GlobalStaffordChallenge.universalStatement`, one deliberate `sorry`).
`Solution.lean` will transport the proved theorem to it.

| Dependency | Exact version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| [AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) | `faa64814d5a310dc925e330af58e000f129f1098` |
| [Stafford38 formal](https://github.com/itpplasma/stafford38-formal) | `784b59925beb9a480519142336bd6434f6eeef16` |

```sh
lake exe cache get
lake build
scripts/verify.sh
```

## Ownership

| Artifact | Home |
| --- | --- |
| Reusable mathematics | [algebraic-analysis](https://github.com/itpplasma/algebraic-analysis) |
| Weyl-algebra theorem | [stafford38-formal](https://github.com/itpplasma/stafford38-formal) |
| This formalization and its Palomar interface | this repository |
| Paper proof, research history, superseded routes | private research repository |

Christopher Albert is the human author and maintainer; AI systems assist
under human direction, as recorded in `formalization.yaml`. Code and
documentation are Apache-2.0 (`LICENSE`, `NOTICE`).
