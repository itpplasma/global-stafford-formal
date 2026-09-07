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

The formalization is complete through Phase II: `GlobalStafford.universalStatement`
(`GlobalStafford/Assembly/Closure.lean`) proves the theorem for the intrinsic
algebra of finite-order differential operators, and `Solution.lean` transports
it to the Mathlib-only statement `GlobalStaffordChallenge.universalStatement`
of [`Challenge.lean`](Challenge.lean). Both depend only on `propext`,
`Classical.choice`, and `Quot.sound`; `scripts/verify.sh` (build, pins,
source audit, endpoint axioms, Challenge/Solution import closures) passes.
Phase III (Comparator, NanoDa and Lean-kernel replay in an isolated clone,
verification record, release metadata) is in progress; see [`PLAN.md`](PLAN.md)
and [`docs/verification.md`](docs/verification.md). No release, registration,
or publication is claimed, and human expert review of the paper proof and of
the statement correspondence remains open.

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
