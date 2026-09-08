# Paper and Lean specification

Maps the paper proof (`itpplasma/global-stafford`,
`notes/source-changing-descent-2026-09-07.md`, revision of 7 September
2026 with Remark 4.2, commit `9a096dc9f6c990bdfb3e8a24110989648c70b3f3`,
SHA-256 `22f047887464d268c1def305e697232826799bc112cec812e31e2cb8f8172d03`)
to the Lean declarations of this repository. Names
in the Lean column are the required names; the status column is updated as
work packages close.

## Statement

| Paper | Lean | Note |
| --- | --- | --- |
| `D_k(A)`, finite-order operators, composition product | `AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A)`; in `Challenge.lean` the predicate `IsDifferentialOperator` on `Module.End k A` | Same inductive definition; `Solution.lean` proves `IsOrderLE n P ↔ P ∈ order n` |
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
| Weyl S38 import | `Stafford38.universalStatement` at pin `784b5992` | — | imported, axiom-clean |
| Phase I assembly | `GlobalStafford.PhaseI.twoGeneratorIdentity_of_inputs`, `universalStatement_of_inputs` | 10 | done |
| Operator localization and clearance (Section 1, Section 8 inputs) | `GlobalStafford.Localization.localizationInterface` | 11 | done |
| Étale lifting, Weyl relations, coordinate rigidity (Lemma 6.2) | `GlobalStafford.Chart.liftDerivation`, `liftDerivation_comm`, `coordinateRigidity` | 12 | done |
| Finite generic fibre and `B → C` injective (Lemma 6.2) | `GlobalStafford.Chart.finiteGenericFibre_of_etale`, `algebraMap_injective_of_etale` | 13 | done |
| `D_k(C)` is a domain (Section 8 input) | `GlobalStafford.Chart.noZeroDivisors_algebra_of_etale` | 14 | done |
| Weyl algebra domain and right Ore (Section 8 input) | `GlobalStafford.Weyl.OreDomain` instances, `weyl_rightOre` | 15 | done |
| Scalar extension to `k(t)` (Lemma 6.2) | `GlobalStafford.Chart.scalarExtensionInterface`, `etaleChartDataK`, `s38Poly_chart` | 16, 18b | done |
| `T → S` injective (Lemma 6.2) | `GlobalStafford.Chart.weylAction_injective` | 18a | done |
| GS-DX (Theorem 6.3) | `GlobalStafford.universalStatement`; `GlobalStaffordChallenge.universalStatement` (`Solution.lean`) | 18, 19 | done; independent replay recorded in `verification-results.json` |

## Literature inputs and their discharge

See `PLAN.md` Section 7. Each Phase I structure field corresponds to one
standard fact; each Phase II work package proves exactly that field.

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
