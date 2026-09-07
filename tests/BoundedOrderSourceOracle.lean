import GlobalStafford.Descent.BoundedOrderSource
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Oracle test for `exists_bounded_order_sources` (Theorem 4.1, WP-5)

`PLAN.md` WP-5 acceptance test. Literal consumer of
`GlobalStafford.Descent.exists_bounded_order_sources` instantiated for
`A = Polynomial ℚ` and `Af = Localization.Away (X : Polynomial ℚ)`, with
every hypothesis of the theorem (the localization interface, the Ore data,
`d ≠ 0`, and `S38_poly (D_ℚ(A_f))`) taken as an assumption. This checks that
the statement of Theorem 4.1 elaborates and specializes without further
hypotheses at a concrete carrier, independently of the internal proof of
`exists_bounded_order_sources` itself.
-/

namespace GlobalStafford.BoundedOrderSourceOracle

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators GlobalStafford.Localization
  GlobalStafford.Certificate GlobalStafford.Chart GlobalStafford.Descent
open Polynomial

noncomputable abbrev Af := Localization.Away (Polynomial.X : Polynomial ℚ)

/-- Oracle: `exists_bounded_order_sources` (Theorem 4.1) instantiated at
`A = ℚ[X]`, `A_f = ℚ[X]_X`. -/
theorem oracle
    (L : LocalizationInterface (k := ℚ) (A := Polynomial ℚ) (Af := Af) Polynomial.X)
    [Nontrivial Af] [NoZeroDivisors (algebra (k := ℚ) (R := Af))]
    (hS : S38Poly ℚ (algebra (k := ℚ) (R := Af)))
    (d B : algebra (k := ℚ) (R := Polynomial ℚ)) (od : OreData d B) (hd : d ≠ 0) :
    ∃ (M l : ℕ) (H : Polynomial ℚ), H ≠ 0 ∧
      ∀ N : ℕ, l + M ≤ N → H.eval (N : ℚ) ≠ 0 →
        ∃ T : algebra (k := ℚ) (R := Polynomial ℚ), (T : Module.End ℚ (Polynomial ℚ)) ∈ order M ∧
          ∃ U V : algebra (k := ℚ) (R := Af),
            (1 : algebra (k := ℚ) (R := Af)) =
              L.ι d * U +
                L.ι (B + multiplicationD (Polynomial.X : Polynomial ℚ) ^ (N - l - M) * T) *
                  L.ι d * V :=
  exists_bounded_order_sources Polynomial.X L hS d B od hd

end GlobalStafford.BoundedOrderSourceOracle

#print axioms GlobalStafford.BoundedOrderSourceOracle.oracle
