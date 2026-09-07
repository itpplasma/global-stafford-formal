import GlobalStafford.Certificate.OldChartProtection
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Oracle test for `protect_old_chart` (Lemma 1.2)

`PLAN.md` WP-3 acceptance test. Literal consumer of
`GlobalStafford.Certificate.protect_old_chart` instantiated for
`A = Polynomial ℚ` and `Ag = Localization.Away (X : Polynomial ℚ)`, with
every hypothesis of the theorem as an assumption. This checks that the
`protect_old_chart` statement is usable at a concrete carrier without any
unforeseen typeclass obstruction, independently of the proof of
`protect_old_chart` itself: it only needs to typecheck and print a clean
axiom report.
-/

namespace GlobalStafford.OldChartProtectionOracle

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators GlobalStafford.Localization
  GlobalStafford.Localization.LocalizationInterface GlobalStafford.Certificate
open Polynomial

noncomputable abbrev Ag := Localization.Away (Polynomial.X : Polynomial ℚ)

/-- Literal consumer of `protect_old_chart` at a concrete carrier: every
hypothesis is taken as an assumption, so this only checks that the
statement of Lemma 1.2 elaborates and is usable at `A = ℚ[X]`,
`A_g = ℚ[X]_X`. -/
theorem oracle
    (Lg : LocalizationInterface (k := ℚ) (A := Polynomial ℚ) (Af := Ag) Polynomial.X)
    (f : Polynomial ℚ)
    {d B T A₀ B₀ : algebra (k := ℚ) (R := Polynomial ℚ)}
    {U V : algebra (k := ℚ) (R := Ag)}
    {rd M rV L m : ℕ}
    (hd : (d : Module.End ℚ (Polynomial ℚ)) ∈ order rd)
    (hT : (T : Module.End ℚ (Polynomial ℚ)) ∈ order M)
    (hV : (V : Module.End ℚ Ag) ∈ order rV)
    (hL : M + rd + rV < L)
    (hold : (1 : algebra (k := ℚ) (R := Ag)) = Lg.ι d * U + Lg.ι B * Lg.ι d * V)
    (hclear : multiplicationD (k := ℚ) (A := Polynomial ℚ) f ^ m =
      d * A₀ + (B + multiplicationD (k := ℚ) (A := Polynomial ℚ) f ^ L * T) * d * B₀) :
    ∃ U' V' : algebra (k := ℚ) (R := Ag),
      (1 : algebra (k := ℚ) (R := Ag)) =
        Lg.ι d * U' +
          Lg.ι (B + multiplicationD (k := ℚ) (A := Polynomial ℚ) f ^ L * T) * Lg.ι d * V' :=
  protect_old_chart Lg f hd hT hV hL hold hclear

end GlobalStafford.OldChartProtectionOracle

#print axioms GlobalStafford.OldChartProtectionOracle.oracle
