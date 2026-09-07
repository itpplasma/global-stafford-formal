import GlobalStafford.Operators.Commutator
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Oracle test for the binomial formula (1.1)

`PLAN.md` WP-1 acceptance test. Instantiates `GlobalStafford.Operators.
mul_multiplication_pow` on `Polynomial ℚ` with `f = X` and
`P = Polynomial.derivative` (order `1`), then independently verifies the
resulting concrete polynomial identity by direct computation, without
appealing to `mul_multiplication_pow` itself, as a behavioral oracle.
-/

namespace GlobalStafford.OperatorsOracle

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators
open Polynomial

/-- `Polynomial.derivative`, as a `k`-linear endomorphism of `ℚ[X]`, has
order `1`: `[derivative, a] = multiplication (derivative a)`. -/
theorem derivative_mem_order_one :
    (Polynomial.derivative : Module.End ℚ (Polynomial ℚ)) ∈
      order (k := ℚ) (R := Polynomial ℚ) 1 := by
  rw [mem_order_succ_iff]
  intro a
  have hcomm : commutator (Polynomial.derivative : Module.End ℚ (Polynomial ℚ)) a =
      multiplication (k := ℚ) (Polynomial.derivative a) := by
    refine LinearMap.ext fun x => ?_
    show Polynomial.derivative (a * x) - a * Polynomial.derivative x =
        Polynomial.derivative a * x
    rw [Polynomial.derivative_mul]
    ring
  rw [hcomm]
  refine (mem_order_zero_iff_eq_multiplication _).2 ?_
  refine LinearMap.ext fun x => ?_
  show Polynomial.derivative a * x = Polynomial.derivative a * 1 * x
  ring

/-- Instantiation of the left binomial formula (1.1) at `n = 2`, truncated
using `derivative_mem_order_one` (the `j = 2` term vanishes since
`derivative` has order `1`): `P f^2 = f^2 P + 2 (f (ad f P))`. -/
theorem derivative_mul_X_sq :
    (Polynomial.derivative : Module.End ℚ (Polynomial ℚ)) * multiplication (k := ℚ) X ^ 2 =
      multiplication (k := ℚ) X ^ 2 * Polynomial.derivative +
        2 • (multiplication (k := ℚ) X *
          ad (k := ℚ) (A := Polynomial ℚ) X
            (Polynomial.derivative : Module.End ℚ (Polynomial ℚ))) := by
  have htrunc := mul_multiplication_pow_truncate (k := ℚ) (A := Polynomial ℚ)
      (f := X) derivative_mem_order_one 2
  rw [htrunc, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Independent oracle: the same identity, checked at a concrete input
`X^3`, computed directly from the definitions of `multiplication`, `ad`,
and `Polynomial.derivative` — without appealing to `mul_multiplication_pow`
or `mul_multiplication_pow_truncate`. -/
theorem derivative_mul_X_sq_apply_oracle :
    (Polynomial.derivative : Module.End ℚ (Polynomial ℚ))
        ((multiplication (k := ℚ) X ^ 2) (X ^ 3)) =
      (multiplication (k := ℚ) X ^ 2) (Polynomial.derivative (X ^ 3 : Polynomial ℚ)) +
        2 • ((multiplication (k := ℚ) X)
          ((ad (k := ℚ) (A := Polynomial ℚ) X
              (Polynomial.derivative : Module.End ℚ (Polynomial ℚ))) (X ^ 3))) := by
  simp only [multiplication_apply, ad, commutator_apply, Module.End.mul_apply, pow_succ,
    pow_zero, Module.End.one_apply, nsmul_eq_mul, Polynomial.derivative_mul,
    Polynomial.derivative_X]
  ring

end GlobalStafford.OperatorsOracle

#print axioms GlobalStafford.OperatorsOracle.derivative_mem_order_one
#print axioms GlobalStafford.OperatorsOracle.derivative_mul_X_sq
#print axioms GlobalStafford.OperatorsOracle.derivative_mul_X_sq_apply_oracle
