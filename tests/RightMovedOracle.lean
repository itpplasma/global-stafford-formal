import GlobalStafford.Conjugation.RightMoved
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Oracle test for the right-moved conjugation (`PLAN.md` WP-4b)

Instantiates `GlobalStafford.Conjugation.evalNat_squaredInput` (paper
(4.11)) concretely at `k = ℚ`, `A = ℚ[X]`, `Af = ℚ[X]_X` (the localization
of `ℚ[X]` away from `X`), as a literal consumer of the general theorem, with
the order hypotheses on `d * c` and `d` kept as explicit assumptions. This
checks that the general statement specializes without further hypotheses,
using genuine `Algebra ℚ Af` / `IsScalarTower ℚ (Polynomial ℚ) Af`
instances built from the canonical localization algebra map, rather than
restating the proof. The `Algebra ℚ Af` and `IsScalarTower ℚ (Polynomial ℚ) Af`
instances needed for this instantiation are found automatically (via
`OreLocalization.instAlgebra`, generic over any `Algebra R₀ R` with
`R₀` commutative) once `Mathlib.Algebra.Polynomial.AlgebraMap` is imported,
so no manual instance is declared here.
-/

namespace GlobalStafford.RightMovedOracle

open AlgebraicAnalysis.DifferentialOperators
open GlobalStafford.Operators GlobalStafford.Localization GlobalStafford.Conjugation

/-- Oracle: `evalNat_squaredInput` (paper (4.11)) instantiated at
`A = ℚ[X]`, `Af = ℚ[X]_X`. -/
theorem evalNat_squaredInput_oracle
    {c d : algebra (k := ℚ) (R := Localization.Away (Polynomial.X : Polynomial ℚ))}
    {r₁ r₂ : ℕ}
    (h₁ : ((d * c :
          algebra (k := ℚ) (R := Localization.Away (Polynomial.X : Polynomial ℚ))) :
        Module.End ℚ (Localization.Away (Polynomial.X : Polynomial ℚ))) ∈ order r₁)
    (h₂ : (d : Module.End ℚ (Localization.Away (Polynomial.X : Polynomial ℚ))) ∈ order r₂)
    (N : ℕ) :
    evalNat N (squaredInput (Polynomial.X : Polynomial ℚ) c d r₁ r₂) =
      (c *
          multiplicationD (k := ℚ) (A := Localization.Away (Polynomial.X : Polynomial ℚ))
              (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))
                (Polynomial.X : Polynomial ℚ)) ^
            N *
          d) *
        (c *
            multiplicationD (k := ℚ) (A := Localization.Away (Polynomial.X : Polynomial ℚ))
                (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))
                  (Polynomial.X : Polynomial ℚ)) ^
              N *
            d) *
        LocalizationInterface.fInv (k := ℚ) (Polynomial.X : Polynomial ℚ) ^ (2 * N) :=
  evalNat_squaredInput (Polynomial.X : Polynomial ℚ) h₁ h₂ N

end GlobalStafford.RightMovedOracle

#print axioms GlobalStafford.RightMovedOracle.evalNat_squaredInput_oracle
