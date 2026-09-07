import GlobalStafford.Chart.ScalarExtension
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Oracle test for `s38Poly_of_scalarExtension` (WP-9)

`PLAN.md` WP-9 acceptance test. A literal consumer of
`GlobalStafford.Chart.s38Poly_of_scalarExtension`: instantiates it at the concrete
scalar extension `D := ℚ`, `K := RatFunc ℚ`, `DK := RatFunc ℚ`, `t := RatFunc.X`
(a `ℚ`-algebra `D` extended to its own field of fractions of rational functions,
with the scalar-extension map `Θ` taken to be the identity-shaped inclusion
`Polynomial ℚ →+* RatFunc ℚ`). This checks that the abstract theorem specializes
to a genuine instance without any further axioms, independent of the internal
proof of `s38Poly_of_scalarExtension` itself.
-/

namespace GlobalStafford.ScalarExtensionOracle

open GlobalStafford.Chart AlgebraicAnalysis Polynomial

/-- Instantiation of `s38Poly_of_scalarExtension` at `D = K = DK = ℚ`-algebra data
`(ℚ, RatFunc ℚ, RatFunc ℚ, RatFunc.X)`: given any `ScalarExtensionInterface` for this
data and `TwoGeneratorIdentity (RatFunc ℚ)`, we get `S38Poly ℚ ℚ`. A literal consumer
of the WP-9 theorem, not a restatement of its proof. -/
theorem s38Poly_rat_ratFunc
    (I : ScalarExtensionInterface (k := ℚ) ℚ (RatFunc ℚ) (RatFunc ℚ) RatFunc.X)
    (hK : TwoGeneratorIdentity (RatFunc ℚ)) : S38Poly ℚ ℚ :=
  s38Poly_of_scalarExtension ℚ (RatFunc ℚ) (RatFunc ℚ) RatFunc.X I hK

#print axioms s38Poly_rat_ratFunc

end GlobalStafford.ScalarExtensionOracle
