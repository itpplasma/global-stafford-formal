import GlobalStafford.Chart.EtaleChartData

/-!
# Oracle test for étale chart data and chart S38 (WP-8)

`PLAN.md` WP-8 acceptance test. A literal consumer of
`GlobalStafford.Chart.twoGeneratorIdentity_chart_of_weyl`: specializes it at
`k = ℚ`, `n = 1`, `C = MvPolynomial (Fin 1) ℚ` over itself
(`Algebra (MvPolynomial (Fin 1) ℚ) (MvPolynomial (Fin 1) ℚ) := inferInstance`,
the reflexive `Algebra.id` instance), taking the chart data `E` and the Ore /
domain instances on `PresentedWeyl ℚ 1` as hypotheses rather than constructing
them (their construction is Phase II, WP-12/13/14/15). This checks that the
abstract theorem specializes to a genuine instance of the two-generator
identity for `D_ℚ(C)` without any further axioms, independent of the internal
proof of `twoGeneratorIdentity_chart_of_weyl` itself.
-/

namespace GlobalStafford.EtaleChartDataOracle

open GlobalStafford.Chart AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators
open Stafford38.WeylIteratedEquivalence
open scoped nonZeroDivisors

/-- Independent oracle: specializing `twoGeneratorIdentity_chart_of_weyl` (WP-8
item 7) at `k = ℚ`, `n = 1`, `C = MvPolynomial (Fin 1) ℚ` over itself, with the
chart data `E` and the Ore / domain instances on `PresentedWeyl ℚ 1` as
hypotheses, reproduces the two-generator identity for `D_ℚ(C)`. -/
theorem twoGeneratorIdentity_chart_of_weyl_oracle
    (E : EtaleChartData ℚ 1 (MvPolynomial (Fin 1) ℚ))
    [OreLocalization.OreSet ((PresentedWeyl ℚ 1)ᵐᵒᵖ)⁰]
    [NoZeroDivisors (PresentedWeyl ℚ 1)] :
    TwoGeneratorIdentity (algebra (k := ℚ) (R := MvPolynomial (Fin 1) ℚ)) :=
  twoGeneratorIdentity_chart_of_weyl E

end GlobalStafford.EtaleChartDataOracle

#print axioms GlobalStafford.EtaleChartDataOracle.twoGeneratorIdentity_chart_of_weyl_oracle
