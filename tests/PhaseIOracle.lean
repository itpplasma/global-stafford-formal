import GlobalStafford.Assembly.PhaseI
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Oracle test for `twoGeneratorIdentity_of_inputs` (Phase I assembly)

`PLAN.md` WP-10 acceptance test. Literal consumer of
`GlobalStafford.PhaseI.twoGeneratorIdentity_of_inputs` instantiated for
`A = Polynomial ℚ`, taking an `Inputs ℚ (Polynomial ℚ)` value as a
hypothesis. This checks that `Inputs` and `twoGeneratorIdentity_of_inputs`
are usable at a concrete carrier without any unforeseen typeclass
obstruction, independently of the proof itself: it only needs to typecheck
and print a clean axiom report.
-/

namespace GlobalStafford.PhaseIOracle

open GlobalStafford.PhaseI GlobalStafford.Assembly
open AlgebraicAnalysis.DifferentialOperators

/-- Given any `Inputs ℚ (Polynomial ℚ)`, `D_ℚ(Polynomial ℚ)` satisfies the
same-divisor identity. -/
theorem oracle (I : Inputs ℚ (Polynomial ℚ)) :
    AlgebraicAnalysis.TwoGeneratorIdentity (algebra (k := ℚ) (R := Polynomial ℚ)) :=
  twoGeneratorIdentity_of_inputs I

end GlobalStafford.PhaseIOracle

#print axioms GlobalStafford.PhaseIOracle.oracle
