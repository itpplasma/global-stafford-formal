import GlobalStafford.Chart.ScalarExtensionConstruction

/-!
# Oracle test for the scalar extension construction (WP-16)

`PLAN.md` WP-16 acceptance test. A literal consumer of
`GlobalStafford.Chart.scalarExtensionInterface`: instantiates it at the concrete chart
`C = MvPolynomial (Fin 1) k₀` over itself (the reflexive `Algebra.id` instance, with
`Algebra.FormallyEtale B B` from the standard Mathlib instances), `n = 1`, and feeds the
resulting `ScalarExtensionInterface` to the WP-9 transport theorem
`GlobalStafford.Chart.s38Poly_of_scalarExtension` exactly as `PhaseI.s38Poly_of_chartData`
does. It also checks the independently-computable value
`Θ (scalarPoly X) = algebraMap k₀(t) (D_{k₀(t)}(C_K)) t` of the constructed `Θ`, without
unfolding the internal `eval₂`/base-change construction.

The base field is `k₀ = ℚ(s) = RatFunc ℚ` rather than `ℚ` itself: for `k = ℚ` Mathlib has two
non-defeq instances of `Algebra ℚ (RatFunc ℚ)` (`RatFunc.instAlgebraOfPolynomial`, used by the
construction, and `DivisionRing.toRatAlgebra`, picked by instance synthesis at `ℚ`), so a
consumer written at `ℚ` would test the diamond rather than the theorem. The chart itself,
`C = k₀[x_0]` over itself, is concrete.
-/

namespace GlobalStafford.ScalarExtensionConstructionOracle

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators GlobalStafford.Chart
open scoped TensorProduct

/-- The concrete base field `k₀ = ℚ(s)`. -/
noncomputable abbrev k₀ := RatFunc ℚ

/-- The concrete chart `C = k₀[x_0]`, étale over `B = k₀[x_0]` through the identity. -/
noncomputable abbrev C := MvPolynomial (Fin 1) k₀

/-- The WP-16 scalar extension interface at the concrete chart `C = k₀[x_0]` over itself. -/
noncomputable def oracleInterface :
    ScalarExtensionInterface (k := k₀) (algebra (k := k₀) (R := C)) (RatFunc k₀)
      (DK k₀ C) (RatFunc.X : RatFunc k₀) :=
  scalarExtensionInterface (k := k₀) (n := 1) (C := C)

/-- Independent oracle: the constructed `Θ` sends the scalar polynomial `X` to the central
scalar `t = RatFunc.X` of `D_{k₀(t)}(C_K)`. -/
theorem oracle_theta_scalar_X :
    oracleInterface.Θ (GlobalStafford.Conjugation.scalarPoly (Polynomial.X : Polynomial k₀)) =
      algebraMap (RatFunc k₀) (DK k₀ C) (RatFunc.X : RatFunc k₀) := by
  rw [oracleInterface.Θ_scalar]
  simp

/-- Independent oracle: the constructed interface transports the two-generator identity on
`D_{k₀(t)}(C_K)` to the polynomial chart hypothesis `S38Poly k₀ (D_{k₀}(C))`, exactly as
`PhaseI.s38Poly_of_chartData` consumes it. -/
theorem oracle_s38Poly (hK : AlgebraicAnalysis.TwoGeneratorIdentity (DK k₀ C)) :
    S38Poly k₀ (algebra (k := k₀) (R := C)) :=
  s38Poly_of_scalarExtension _ _ _ _ oracleInterface hK

end GlobalStafford.ScalarExtensionConstructionOracle

#print axioms GlobalStafford.ScalarExtensionConstructionOracle.oracleInterface
#print axioms GlobalStafford.ScalarExtensionConstructionOracle.oracle_theta_scalar_X
#print axioms GlobalStafford.ScalarExtensionConstructionOracle.oracle_s38Poly
