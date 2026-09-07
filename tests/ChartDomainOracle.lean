import GlobalStafford.Chart.ChartDomain
import GlobalStafford.Chart.GenericFibre

/-!
# Oracle test for `noZeroDivisors_algebra_of_etale` (WP-14)

`PLAN.md` WP-14 acceptance test. A literal consumer of
`GlobalStafford.Chart.noZeroDivisors_algebra_of_etale`: instantiates it at the concrete
self-étale chart `k := ℚ`, `n := 1`, `C := MvPolynomial (Fin 1) ℚ` (the polynomial ring
`B = k[x_0]` viewed as an étale `B`-algebra over itself, via the generic `Algebra.Etale.self`
instance), and then *uses* the resulting `NoZeroDivisors` class to derive a statement that the
WP-14 file never proves (`mul_ne_zero` on the chart operator ring, and the assembly of the full
`EtaleChartData` record together with the WP-12/WP-13 fields). Independent of the internal
symbol argument of `noZeroDivisors_algebra_of_etale`.
-/

namespace GlobalStafford.ChartDomainOracle

open GlobalStafford.Chart
open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators

noncomputable abbrev C := MvPolynomial (Fin 1) ℚ

/-- The WP-13 hypothesis of `noZeroDivisors_algebra_of_etale`, at the self-étale chart. -/
theorem algebraMap_injective_rat_self :
    Function.Injective (algebraMap (MvPolynomial (Fin 1) ℚ) C) :=
  algebraMap_injective_of_etale (k := ℚ) (n := 1) (C := C)

/-- Instantiation of the WP-14 theorem at the self-étale chart `C = B = MvPolynomial (Fin 1) ℚ`.
A literal consumer, not a restatement of the proof. -/
theorem noZeroDivisors_rat_self : NoZeroDivisors (algebra (k := ℚ) (R := C)) :=
  noZeroDivisors_algebra_of_etale (k := ℚ) (n := 1) (C := C) algebraMap_injective_rat_self

/-- A genuine consumer of the class instance: in `D_ℚ(ℚ[x_0])` no nonzero operator squares to
zero. This is not available from any declaration of `Chart/ChartDomain*.lean` alone. -/
theorem mul_ne_zero_rat_self (P Q : algebra (k := ℚ) (R := C)) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    P * Q ≠ 0 :=
  haveI := noZeroDivisors_rat_self
  mul_ne_zero hP hQ

/-- End-to-end consumer: with the WP-12 derivation fields and the WP-13 geometric fields, the
WP-14 output completes an `EtaleChartData` record for the self-étale chart. -/
theorem etaleChartData_rat_self : Nonempty (EtaleChartData ℚ 1 C) :=
  etaleChartData_of_fields (k := ℚ) (n := 1) (C := C)
    (finiteGenericFibre_of_etale (k := ℚ) (n := 1) (C := C))
    (algebraMap_ne_zero_of_etale (k := ℚ) (n := 1) (C := C))
    noZeroDivisors_rat_self

#print axioms algebraMap_injective_rat_self
#print axioms noZeroDivisors_rat_self
#print axioms mul_ne_zero_rat_self
#print axioms etaleChartData_rat_self

end GlobalStafford.ChartDomainOracle
