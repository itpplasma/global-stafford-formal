import GlobalStafford.Descent.FiniteCoverPatching
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Oracle test for `twoGeneratorIdentity_of_charts` (Theorem 5.1)

`PLAN.md` WP-6 acceptance test. Literal consumer of
`GlobalStafford.Descent.twoGeneratorIdentity_of_charts` instantiated for
`A = Polynomial ℚ` and a one-chart cover `f 0 = 1` (so `Ideal.span {1} = ⊤`
holds outright, not as a hypothesis), with the chart's `LocalizationInterface`
and `BoundedSourceProducer` (the WP-5 conclusion, unavailable on this branch)
taken as assumptions. This checks that `ChartCover` and
`twoGeneratorIdentity_of_charts` are usable at a concrete carrier without any
unforeseen typeclass obstruction, independently of the proof of
`twoGeneratorIdentity_of_charts` itself: it only needs to typecheck and print
a clean axiom report.
-/

namespace GlobalStafford.FiniteCoverPatchingOracle

open GlobalStafford.Descent GlobalStafford.Localization
  GlobalStafford.Localization.LocalizationInterface
open AlgebraicAnalysis.DifferentialOperators

/-- One-chart cover of `A = Polynomial ℚ` at `f 0 = 1`, generates the unit ideal outright. -/
theorem oracle
    (Af0 : Type) [CommRing Af0] [Algebra ℚ Af0] [Algebra (Polynomial ℚ) Af0]
    [IsScalarTower ℚ (Polynomial ℚ) Af0] [IsLocalization.Away (1 : Polynomial ℚ) Af0]
    (loc0 : LocalizationInterface (k := ℚ) (A := Polynomial ℚ) (Af := Af0) 1)
    (producer0 : BoundedSourceProducer (1 : Polynomial ℚ) Af0 loc0)
    [NoZeroDivisors (algebra (k := ℚ) (R := Polynomial ℚ))]
    (hOre : ∀ x y : algebra (k := ℚ) (R := Polynomial ℚ), x ≠ 0 → y ≠ 0 →
      ∃ a b : algebra (k := ℚ) (R := Polynomial ℚ), a ≠ 0 ∧ x * a = y * b) :
    AlgebraicAnalysis.TwoGeneratorIdentity (algebra (k := ℚ) (R := Polynomial ℚ)) := by
  have hcover : Ideal.span (Set.range (fun _ : Fin 1 => (1 : Polynomial ℚ))) = ⊤ := by
    have hrange : Set.range (fun _ : Fin 1 => (1 : Polynomial ℚ)) = {1} := by
      ext x
      simp
    rw [hrange, Ideal.span_singleton_one]
  exact twoGeneratorIdentity_of_charts
    { s := 1
      f := fun _ => (1 : Polynomial ℚ)
      cover := hcover
      Af := fun _ => Af0
      loc := fun _ => loc0
      producer := fun _ => producer0 } hOre

end GlobalStafford.FiniteCoverPatchingOracle

#print axioms GlobalStafford.FiniteCoverPatchingOracle.oracle
