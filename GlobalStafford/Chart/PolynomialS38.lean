import GlobalStafford.Conjugation.PolynomialEvaluation

/-!
# `S38_poly` and admissible evaluation bounds

Generic part of WP-4 (`PLAN.md`, Section 3, "WP-4 Polynomial evaluation and the
right-moved conjugation"). `S38Poly` packages the hypothesis `S38_poly(R_f)` used
in Section 4 of the paper proof: every nonzero polynomial `E` over a `k`-algebra
`D` admits a same-divisor certificate `h = E u' + w' E v'`, scaled by a nonzero
polynomial `h` over the base field `k`. `exists_admissible_bound` records that
the nonzero scalar polynomial `h` produced by such a certificate is eventually
nonzero at natural-number arguments, which is what lets Theorem 4.1 choose a
sufficiently large `N` at which the certificate specializes.
-/

namespace GlobalStafford.Chart

open Polynomial GlobalStafford.Conjugation

section S38PolyDef

variable (k : Type*) [CommRing k] (D : Type*) [Ring D] [Algebra k D]

/-- `S38_poly(D)`: every nonzero polynomial `E` over `D` admits a same-divisor
certificate `scalarPoly h = E * u + w * E * v` scaled by some nonzero `h : Polynomial k`.
Paper Section 4, hypothesis `S38_poly`. -/
def S38Poly : Prop :=
  ∀ E : Polynomial D, E ≠ 0 → ∃ h : Polynomial k, h ≠ 0 ∧
    ∃ u w v : Polynomial D, GlobalStafford.Conjugation.scalarPoly h = E * u + w * E * v

end S38PolyDef

section AdmissibleBound

variable {k : Type*} [Field k] [CharZero k]

/-- A nonzero polynomial `h` over a characteristic-zero field `k` is nonzero at every
sufficiently large natural number: its root set is finite (`Polynomial.finite_setOfPred_isRoot`),
so its preimage under the injective map `ℕ → k` is a finite, hence bounded above, set of
naturals. Paper Section 4: this supplies the admissible `N` at which the `S38_poly`
certificate for `E'` specializes to a concrete identity. -/
theorem exists_admissible_bound {h : Polynomial k} (hh : h ≠ 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → h.eval (N : k) ≠ 0 := by
  have hfin : Set.Finite { x : k | h.IsRoot x } := Polynomial.finite_setOfPred_isRoot hh
  have hfin' : Set.Finite ((Nat.cast : ℕ → k) ⁻¹' { x : k | h.IsRoot x }) :=
    hfin.preimage Nat.cast_injective.injOn
  obtain ⟨N₀, hN₀⟩ := hfin'.bddAbove
  refine ⟨N₀ + 1, fun N _ hroot => ?_⟩
  have hmem : N ∈ (Nat.cast : ℕ → k) ⁻¹' { x : k | h.IsRoot x } := hroot
  have hle : N ≤ N₀ := hN₀ hmem
  omega

end AdmissibleBound

end GlobalStafford.Chart

#print axioms GlobalStafford.Chart.exists_admissible_bound
