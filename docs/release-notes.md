# Global Stafford formalization

This release package proves that for every characteristic-zero field `k`, every
smooth integral finitely generated `k`-algebra `A`, and every nonzero finite-order
operator `d` in `D_k(A)`, there exist `F, R, S` in that same algebra with
`1 = d * R + F * d * S`. Products are compositions in the written order.

The proof extends the Weyl case through fixed étale charts, source corrections
whose order stays bounded while coefficient precision grows, preservation of
all earlier chart certificates, and finite-cover descent. Phase II constructs
all structural inputs from Mathlib and the pinned AlgebraicAnalysis and
Stafford38 developments. Both terminal endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`.

The companion PDF includes a clickable proof map, the theorem stated in TeX,
a comparison with the actual Mathlib-only Challenge, the principal proof
mechanisms, and the Challenge/Solution listings. Its authoritative paper source
is the reviewed Markdown note at the revision recorded in `PLAN.md`.

The historical independently verified proof snapshot is
`d76051ce227f41c0fb21f114ffd61890f3b6b99b`; the machine-readable report and hashes
are in `docs/verification-results.json`. Lean is `v4.33.0`, Mathlib is pinned at
`db584cd6d46c92f209a44c0f1c829460d327499d`, AlgebraicAnalysis at
`4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`, and Stafford38 formal at
`e77e176c381ca2d6b20c030f9227f1b031415d2e`.

The dependency pins above describe this release; the historical report used older pins. Replay with the new pins is pending. The author explicitly requested this release now for Palomar submission.

The source archive is Apache-2.0 and records its exact dependencies without
vendoring them. The attached PDF, build provenance and checksums identify the
companion artifact. Human expert review of the mathematics and the statement
correspondence remains open. This is release v1.0.0; no Palomar acceptance is claimed.
