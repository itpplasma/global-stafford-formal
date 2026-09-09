# Paper and Lean specification

This document maps the Global Stafford proof developed in this project to the
Lean declarations. The informal exposition and internal working notes are
records of the same project development. Their dated chronology establishes
project provenance; it does **not** establish external first-presentation or
publication priority. The 2026-09-09 literature assessment is recorded in
[`provenance-literature-novelty.md`](provenance-literature-novelty.md).

The informal argument preceded parts of the Lean implementation. Its dated
record is retained: `itpplasma/global-stafford`,
`notes/source-changing-descent-2026-09-07.md`, revision of 7 September 2026
with Remark 4.2, commit `9a096dc9f6c990bdfb3e8a24110989648c70b3f3`,
SHA-256 `22f047887464d268c1def305e697232826799bc112cec812e31e2cb8f8172d03`.
The tables below preserve that internal paper-to-Lean correspondence.

The Stafford38 dependency supplies the Weyl-algebra theorem. Two revisions
must be distinguished precisely:

- `784b59925beb9a480519142336bd6434f6eeef16` is the **historical inspection
  pin** cited by the 7 September informal proof development;
- `e77e176c381ca2d6b20c030f9227f1b031415d2e` is the Stafford38 revision
  actually consumed by the mechanically reviewed Global Stafford build and is
  the pin in `lake-manifest.json` and `docs/verification-results.json`.

`Stafford38/FoundationClosure.lean`, including
`Stafford38.universalStatement`, has the same source text at those two
Stafford38 revisions, but current reproduction and provenance use the consumed
`e77e176...` revision. This distinction resolves the stale-revision ambiguity
without rewriting the historical research record.

Palomar registry provenance: entry `PALOMAR-2026-09-05-000007`, version `2`,
<https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2>.

## Statement

| Paper | Lean | Note |
| --- | --- | --- |
| `D_k(A)`, finite-order operators, composition product | `AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A)`; in `GlobalStaffordChallenge.lean` the predicate `IsDifferentialOperator` on `Module.End k A` | Same inductive definition; `GlobalStaffordSolution.lean` proves `IsOrderLE n P ↔ P ∈ order n` |
| smooth integral affine `A/k`, char 0 | `[Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]` | Mathlib smooth = formally smooth + finite presentation |
| `1 = dR + FdS` | `(1 : _) = d * R + F * d * S` | order preserved; both `k`-linear compositions |
| GS-DX (Theorem 6.3) | `GlobalStafford.universalStatement`; `GlobalStaffordChallenge.universalStatement` | proved; only `propext`, `Classical.choice`, `Quot.sound` |

## Proof steps

| Paper | Lean | WP | Status |
| --- | --- | --- | --- |
| (1.1) left binomial formula | `GlobalStafford.Operators.mul_multiplication_pow` | 1 | done |
| (4.10) right binomial formula | `GlobalStafford.Operators.multiplication_pow_mul` | 1 | done |
| (1.2) | `GlobalStafford.Operators.exists_mul_multiplication_pow_eq` | 1 | done |
| Lemma 1.1 | `GlobalStafford.Operators.pow_eq_multiplication_pow_mul` | 1 | done |
| Lemma 1.2 | `GlobalStafford.Certificate.protect_old_chart` | 3 | done |
| Section 3 identity (3.3) | `GlobalStafford.Certificate.certificate_of_square` | 2 | done |
| Ore choice (3.1) | `GlobalStafford.Certificate.OreData.of_rightOre` | 2 | done |
| `ρ_t`, `ρ_N(P) = f^N P f^{-N}` | `GlobalStafford.Conjugation.rho`, `evalNat_rho` | 4 | done |
| (4.11) `e_N^2 = E'(N) f^{2N}` | `GlobalStafford.Conjugation.evalNat_squaredInput` | 4 | done |
| `E'(0) ≠ 0` | `GlobalStafford.Conjugation.squaredInput_ne_zero` | 4 | done |
| S38_poly | `GlobalStafford.Chart.S38Poly` | 4 | done |
| Theorem 4.1 | `GlobalStafford.Descent.exists_bounded_order_sources` | 5 | done |
| Theorem 5.1 | `GlobalStafford.Descent.twoGeneratorIdentity_of_charts` | 6 | done |
| Lemma 6.1 | `GlobalStafford.Chart.twoGeneratorIdentity_of_finiteRightSpan`, `finiteRightSpan_weylAction` | 7 | done |
| Lemma 6.2 (rank) | `GlobalStafford.Chart.twoGeneratorIdentity_chart`, `twoGeneratorIdentity_chart_of_weyl` | 8 | done |
| Lemma 6.2 over `k(t)` | `GlobalStafford.Chart.s38Poly_of_scalarExtension`, `GlobalStafford.PhaseI.s38Poly_of_chartData` | 9, 10 | done |
| Theorem 6.3 cover | `GlobalStafford.Chart.exists_finite_etale_cover`, `EtaleCoordinateChart` | 17 | done |
| Weyl S38 import | `Stafford38.universalStatement` at consumed pin `e77e176c381ca2d6b20c030f9227f1b031415d2e` | — | imported, axiom-clean; `784b5992...` is historical inspection pin only |
| Phase I assembly | `GlobalStafford.PhaseI.twoGeneratorIdentity_of_inputs`, `universalStatement_of_inputs` | 10 | done |
| Operator localization and clearance (Section 1, Section 8 inputs) | `GlobalStafford.Localization.localizationInterface` | 11 | done |
| Étale lifting, Weyl relations, coordinate rigidity (Lemma 6.2) | `GlobalStafford.Chart.liftDerivation`, `liftDerivation_comm`, `coordinateRigidity` | 12 | done |
| Finite generic fibre and `B → C` injective (Lemma 6.2) | `GlobalStafford.Chart.finiteGenericFibre_of_etale`, `algebraMap_injective_of_etale` | 13 | done |
| `D_k(C)` is a domain (Section 8 input) | `GlobalStafford.Chart.noZeroDivisors_algebra_of_etale` | 14 | done |
| Weyl algebra domain and right Ore (Section 8 input) | `GlobalStafford.Weyl.OreDomain` instances, `weyl_rightOre` | 15 | done |
| Scalar extension to `k(t)` (Lemma 6.2) | `GlobalStafford.Chart.scalarExtensionInterface`, `etaleChartDataK`, `s38Poly_chart` | 16, 18b | done |
| `T → S` injective (Lemma 6.2) | `GlobalStafford.Chart.weylAction_injective` | 18a | done |
| GS-DX (Theorem 6.3) | `GlobalStafford.universalStatement`; `GlobalStaffordChallenge.universalStatement` (`GlobalStaffordSolution.lean`) | 18, 19 | done; independent replay recorded in `verification-results.json` |

## Literature inputs, prior art, and their discharge

See `PLAN.md` Section 7 for the standard facts used as Phase I interfaces and
proved/discharged in Phase II. For external novelty context, see
[`provenance-literature-novelty.md`](provenance-literature-novelty.md).
That audit covers Stafford 1978, Björk 1981, Coutinho--Holland 1988,
Smith--Stafford 1988, Cannings--Holland 1994, Berest--Chalykh 2012,
Quadrat--Robertz 2014, Caro-Tuesta--Levcovitz 2020, and Bellamy 2026.

The literature conclusion is deliberately evidence-graded: no prior proof of
the exact universal same-divisor theorem was located, and Bellamy 2026 still
records the weaker two-generator question for smooth-affine `D(X)` as open;
this is strong novelty evidence, not a claim that a search can certify absolute
historical priority.

## Fidelity notes

- The formal development uses the right-moved conjugation of Remark 4.2
  (`ρ_t`) instead of `τ_t` and its inverse; the produced sources and the
  quantifier order are identical.
- `S38_poly` replaces the ring `R_f ⊗_k k(t)`: only polynomial identities
  with scalar denominators are used, which is what Theorem 4.1 consumes.
- The chart hypothesis is produced from `D_{k(t)}(C ⊗_k k(t))` through an
  explicit scalar-extension map rather than an identification of rings.
- Lemma 6.1 is stated with a "finite right span up to denominators"
  hypothesis instead of finite rank of `S ⊗_T Q(T)`; the two are equivalent
  for domains and the former is what coordinate generation gives directly.
