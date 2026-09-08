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

The independently verified proof snapshot is
`d76051ce227f41c0fb21f114ffd61890f3b6b99b`; the machine-readable report and hashes
are in `docs/verification-results.json`. Lean is `v4.33.0`, Mathlib is pinned at
`db584cd6d46c92f209a44c0f1c829460d327499d`, AlgebraicAnalysis at
`faa64814d5a310dc925e330af58e000f129f1098`, and Stafford38 formal at
`784b59925beb9a480519142336bd6434f6eeef16`.

The source archive is Apache-2.0 and records its exact dependencies without
vendoring them. The attached PDF, build provenance and checksums identify the
companion artifact. Human expert review of the mathematics and the statement
correspondence remains open. This prepared description assigns no release tag,
Zenodo DOI or Palomar registration.
