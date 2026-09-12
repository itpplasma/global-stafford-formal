# Global Stafford formalization — current release record

Latest documentation release: [v1.0.6](releases/v1.0.6.md).

Current release: **v1.0.6** (documentation release; 9 September 2026).

The v1.0.5 entry below is the preceding mathematical/provenance release; v1.0.6
updates the documentation index without changing declarations or dependency pins.

The formalization proves that for every characteristic-zero field `k`, every
smooth integral finitely generated `k`-algebra `A`, and every nonzero
finite-order operator `d` in `D_k(A)`, there exist `F, R, S` in that same
algebra with

```text
1 = d * R + F * d * S.
```

Products are compositions in the written order. The proof extends the
formalized Weyl case through fixed étale charts, source corrections whose order
stays bounded while coefficient precision grows, preservation of earlier chart
certificates, and finite-cover descent. Phase II constructs all structural
inputs from Mathlib and the pinned AlgebraicAnalysis and Stafford38
developments. Both terminal endpoints use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Verified mathematical snapshot

The mechanically reviewed source is

`b21883a5b3d8f46922713049c3b060523ea3a771`.

It passed the isolated Phase I/full replay and Comparator/NanoDa/Lean checks
recorded in `docs/verification-results.json`, whose SHA-256 is

`08b8dcd152806c5033316100a624d8c61a67f9e069c18ac649f3c6612779db67`.

Exact consumed pins:

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| AlgebraicAnalysis | `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8` |
| Stafford38 formal | `e77e176c381ca2d6b20c030f9227f1b031415d2e` |

The older Stafford38 revision
`784b59925beb9a480519142336bd6434f6eeef16` is a historical inspection pin
from the dated informal proof development, not the dependency revision
consumed by the reviewed build.

The older `d76051ce...` verification report is retained under
`docs/verification/history/` as historical evidence only; it is not the
current reproduction record.

## Provenance and literature correction

Release `v1.0.5` packages the corrected provenance account, exact consumed
dependency revisions, Palomar registry metadata, and the dated literature
audit. The audit is `docs/provenance-literature-novelty.md`.

The audit searched the classical and modern Stafford/D(X) literature, including
Stafford's simple-Noetherian and Weyl papers, Björk, Coutinho--Holland,
Smith--Stafford, Leykin, Cannings--Holland, Bavula, Caro--Levcovitz,
Berest--Chalykh, Quadrat--Robertz, Caro-Tuesta--Levcovitz, a 2001 USP thesis,
and Bellamy's 2026 survey. No prior proof of the exact universal same-divisor
theorem was located. Bellamy 2026 still records Björk's weaker smooth-affine
right-ideal two-generator question as open and identifies
Coutinho--Holland's three-generator theorem as the general result.

This is recorded as **strong evidence of novelty**, not an absolute
first-discovery/first-publication certificate. Earlier unqualified
"first presentation" wording is superseded by this evidence-graded statement.

## Palomar and release metadata

Palomar registry record:

- ID: `PALOMAR-2026-09-05-000007`
- version: `2`
- <https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2>

Release `v1.0.5` was published from commit
`deb5a12d79de58bc00214db12d99e882ce797d47` and includes the overview PDF and
the unchanged mathematical verification report. The release itself states
that it does not create a new Palomar registry version.

Mechanical verification, Palomar/editorial status, literature novelty,
human expert review, and journal publication are separate evidence layers.
Human expert review of the paper remains open.
