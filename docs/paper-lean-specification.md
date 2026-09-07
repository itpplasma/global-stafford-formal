# Paper and Lean specification

Maps the paper proof (`itpplasma/global-stafford`,
`notes/source-changing-descent-2026-09-07.md`, revision of 7 September
2026 with Remark 4.2) to the Lean declarations of this repository. Names
in the Lean column are the required names; the status column is updated as
work packages close.

## Statement

| Paper | Lean | Note |
| --- | --- | --- |
| `D_k(A)`, finite-order operators, composition product | `AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A)`; in `Challenge.lean` the predicate `IsDifferentialOperator` on `Module.End k A` | Same inductive definition; `Solution.lean` proves `IsOrderLE n P ↔ P ∈ order n` |
| smooth integral affine `A/k`, char 0 | `[Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]` | Mathlib smooth = formally smooth + finite presentation |
| `1 = dR + FdS` | `(1 : _) = d * R + F * d * S` | order preserved; both `k`-linear compositions |
| GS-DX (Theorem 6.3) | `GlobalStafford.universalStatement`; `GlobalStaffordChallenge.universalStatement` | Phase II / Phase III |

## Proof steps

| Paper | Lean | WP | Status |
| --- | --- | --- | --- |
| (1.1) left binomial formula | `GlobalStafford.Operators.mul_multiplication_pow` | 1 | todo |
| (4.10) right binomial formula | `GlobalStafford.Operators.multiplication_pow_mul` | 1 | todo |
| (1.2) | `GlobalStafford.Operators.exists_mul_multiplication_pow_eq` | 1 | todo |
| Lemma 1.1 | `GlobalStafford.Operators.pow_eq_multiplication_pow_mul` | 1 | todo |
| Lemma 1.2 | `GlobalStafford.Certificate.protect_old_chart` | 3 | todo |
| Section 3 identity (3.3) | `GlobalStafford.Certificate.certificate_of_square` | 2 | todo |
| Ore choice (3.1) | `GlobalStafford.Certificate.OreData.of_rightOre` | 2 | todo |
| `ρ_t`, `ρ_N(P) = f^N P f^{-N}` | `GlobalStafford.Conjugation.rho`, `evalNat_rho` | 4 | todo |
| (4.11) `e_N^2 = E'(N) f^{2N}` | `GlobalStafford.Conjugation.evalNat_squaredInput` | 4 | todo |
| `E'(0) ≠ 0` | `GlobalStafford.Conjugation.squaredInput_ne_zero` | 4 | todo |
| S38_poly | `GlobalStafford.Chart.S38Poly` | 4 | todo |
| Theorem 4.1 | `GlobalStafford.Descent.exists_bounded_order_sources` | 5 | todo |
| Theorem 5.1 | `GlobalStafford.Descent.twoGeneratorIdentity_of_charts` | 6 | todo |
| Lemma 6.1 | `GlobalStafford.Chart.twoGeneratorIdentity_of_finiteRightSpan` | 7 | todo |
| Lemma 6.2 (rank) | `GlobalStafford.Chart.finiteRightSpan_weylAction`, `twoGeneratorIdentity_chart` | 8 | todo |
| Lemma 6.2 over `k(t)` | `GlobalStafford.Chart.s38Poly_of_scalarExtension`, `s38Poly_of_chartData` | 9, 10 | todo |
| Theorem 6.3 cover | `GlobalStafford.Chart.SmoothCover` | 17 | todo |
| Weyl S38 import | `Stafford38.universalStatement` at pin `784b5992` | — | imported, axiom-clean |

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
