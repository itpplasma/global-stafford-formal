import GlobalStafford.Chart.ChartDataOverK

/-!
# Oracle test for `s38Poly_chart` (WP-18b)

`PLAN.md` WP-18b acceptance test. A literal consumer of
`GlobalStafford.Chart.s38Poly_chart`: instantiates it at the concrete self-étale chart
`k := ℚ`, `n := 1`, `C := MvPolynomial (Fin 1) ℚ` (the polynomial ring `B = k[x_0]` viewed
as an étale `B`-algebra over itself, via the generic `Algebra.Etale.self` instance), with
`hdom : NoZeroDivisors (algebra ℚ C)` hypothesized (the WP-14 leaf this file does not
discharge). This checks that the abstract WP-18b theorem specializes to a genuine instance
without any further axioms, independent of the internal proof of `s38Poly_chart` itself.
-/

namespace GlobalStafford.ChartDataOverKOracle

open GlobalStafford.Chart

/-- Instantiation of `s38Poly_chart` at the self-étale chart `C = B = MvPolynomial (Fin 1) ℚ`.
A literal consumer of the WP-18b theorem, not a restatement of its proof. -/
theorem s38Poly_chart_rat_self
    (hdom : NoZeroDivisors
      (AlgebraicAnalysis.DifferentialOperators.algebra
        (k := ℚ) (R := MvPolynomial (Fin 1) ℚ))) :
    S38Poly ℚ
      (AlgebraicAnalysis.DifferentialOperators.algebra (k := ℚ) (R := MvPolynomial (Fin 1) ℚ)) :=
  s38Poly_chart (k := ℚ) (n := 1) (C := MvPolynomial (Fin 1) ℚ) hdom

#print axioms s38Poly_chart_rat_self

end GlobalStafford.ChartDataOverKOracle
