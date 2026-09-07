import GlobalStafford.Assembly.Closure

/-!
# Oracle test for the WP-18 terminal declaration `GlobalStafford.universalStatement`

A literal consumer of `GlobalStafford.universalStatement`: specializes it at
`k = ℚ`, `A = MvPolynomial (Fin 2) ℚ` (smooth, integral, affine over `ℚ`), and
checks the resulting `AlgebraicAnalysis.TwoGeneratorIdentity` proposition
type-checks independently of the internal proof.
-/

namespace GlobalStafford.ClosureOracle

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators

/-- `MvPolynomial (Fin 2) ℚ` is a smooth `ℚ`-algebra: formal smoothness comes from
`Algebra.instFormallySmoothMvPolynomial`, finite presentation from the `FinitePresentation`
instances for `ℚ` over itself and for `MvPolynomial` over a finitely presented base. -/
instance instSmoothRatMvPolynomialFin2 : Algebra.Smooth ℚ (MvPolynomial (Fin 2) ℚ) where

/-- Independent oracle: `GlobalStafford.universalStatement`, specialized at `k = ℚ`,
`A = MvPolynomial (Fin 2) ℚ`, reproduces the two-generator identity for
`D_ℚ(MvPolynomial (Fin 2) ℚ)`. -/
theorem closure_oracle : AlgebraicAnalysis.TwoGeneratorIdentity
    (algebra (k := ℚ) (R := MvPolynomial (Fin 2) ℚ)) :=
  GlobalStafford.universalStatement ℚ (MvPolynomial (Fin 2) ℚ)

end GlobalStafford.ClosureOracle

#print axioms GlobalStafford.ClosureOracle.instSmoothRatMvPolynomialFin2
#print axioms GlobalStafford.ClosureOracle.closure_oracle
