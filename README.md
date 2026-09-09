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
repository proves its smooth-affine extension by a source-changing
local-to-global argument.

The proof was developed in this research project; the accompanying informal
exposition and internal working notes preserve the project chronology. That
chronology is **not** asserted to certify external first-presentation or
publication priority. A broad literature audit dated 2026-09-09 found no prior
proof of the exact same-divisor theorem and found strong contemporary evidence
of novelty: Bellamy's 2026 survey still records Björk's weaker two-generator
question for `D(X)` on smooth affine varieties as open, while the classical
general result of Coutinho--Holland gives three generators. Absolute priority
is therefore left unasserted. See the
[provenance, prior-art and novelty assessment](docs/provenance-literature-novelty.md)
and the [paper/Lean correspondence](docs/paper-lean-specification.md).

## Status and provenance

The formalization is complete through Phase II: `GlobalStafford.universalStatement`
(`GlobalStafford/Assembly/Closure.lean`) proves the theorem for the intrinsic
algebra of finite-order differential operators, and `GlobalStaffordSolution.lean`
transports it to the Mathlib-only statement
`GlobalStaffordChallenge.universalStatement` of
[`GlobalStaffordChallenge.lean`](GlobalStaffordChallenge.lean). Both depend
only on `propext`, `Classical.choice`, and `Quot.sound`;
`scripts/verify.sh` (build, pins, source audit, endpoint axioms,
Challenge/Solution import closures) passes.

Source `b21883a5b3d8f46922713049c3b060523ea3a771` passed an isolated-clone
Phase I/full replay and Comparator with NanoDa and Lean kernel acceptance. A
second comparison using Palomar's independently compiled canonical Challenge
also passed. The [machine-readable verification record](docs/verification-results.json)
fixes the checked source and the actually consumed dependency pins.

Palomar registry record:

- ID: `PALOMAR-2026-09-05-000007`
- version: `2`
- <https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2>

The latest published GitHub release at the time of this provenance correction
is `v1.0.4`. This `main`-branch correction supersedes the unqualified
"first presentation" wording in that release's historical notes; it changes
provenance/literature documentation, not Lean proof bytes.

| Dependency | Exact consumed version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| [AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) | `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8` |
| [Stafford38 formal](https://github.com/itpplasma/stafford38-formal) | `e77e176c381ca2d6b20c030f9227f1b031415d2e` |

The older Stafford38 revision
`784b59925beb9a480519142336bd6434f6eeef16` appears in dated research records
only as a **historical inspection pin**. It is not the dependency consumed by
the reviewed Global Stafford replay. See
[the provenance audit](docs/provenance-literature-novelty.md) for the exact
relationship.

```sh
lake exe cache get
lake build
scripts/verify.sh
```

## Companion document

The [TeX dossier](docs/dossier/global-stafford-dossier.tex) includes a clickable
proof map, a comparison of the theorem with `GlobalStaffordChallenge.lean`, the
main proof mechanisms, and the actual Challenge/Solution files. Build the PDF
and its source-hash manifest with `docs/dossier/build.sh` (LuaLaTeX, latexmk,
TikZ, DejaVu fonts). The output is
`docs/dossier/global-stafford-dossier.pdf`.
[Release notes](docs/release-notes.md) and the
[release runbook](docs/release-runbook.md) describe the prepared artifacts.

## Continuing work

Read [`PLAN.md`](PLAN.md) for live status, then the
[paper correspondence](docs/paper-lean-specification.md), the
[literature/provenance audit](docs/provenance-literature-novelty.md), and the
[verifier](scripts/verify.sh). Phase I and II are complete for the current
paper revision recorded in the plan. Run the commands above to prepare a fresh
checkout; Lake fetches both mathematics dependencies at their exact pins into
`.lake/packages/algebraicAnalysis` and `.lake/packages/stafford38Formal`.
Separate sibling clones are unnecessary.

For a paper correction, identify its mapped Lean declarations and downstream
consumers, make the smallest correction, and rerun `scripts/verify.sh`.
For Phase I endpoint reports, use `scripts/verify.sh --phase-i` as well; both
modes write logs under `.lake/verification`, so run them sequentially and
retain logs before the next run. A changed proof requires a new independent
replay before extending the Phase III verification claim.

Keep the current dependency pins while maintaining this proof. Optional
AA-2–AA-4 extractions have proofs here already; moving them upstream requires
an explicit work package, axiom-clean library proofs, downstream rewiring, and
a shared-pin compatibility build of the Stafford38 endpoints. Never run
`lake update` as routine setup.

## Ownership

| Artifact | Home |
| --- | --- |
| Reusable mathematics | [algebraic-analysis](https://github.com/itpplasma/algebraic-analysis) |
| Weyl-algebra theorem | [stafford38-formal](https://github.com/itpplasma/stafford38-formal) |
| This formalization and its Palomar interface | this repository |
| Internal informal exposition, research history, superseded routes | internal research repository |

Christopher Albert is the human author and maintainer; AI systems assist under
human direction, as recorded in `formalization.yaml`. Code and documentation
are Apache-2.0 (`LICENSE`, `NOTICE`).
