import AlgebraicAnalysis.DifferentialOperators.Basic

/-!
# Multiplication operators in the subalgebra of differential operators

`PLAN.md` Section 3, work package WP-1 (`Operators/Basic.lean`). Wraps
`AlgebraicAnalysis.DifferentialOperators.multiplication a` as an element of
the subalgebra `AlgebraicAnalysis.DifferentialOperators.algebra k A` of
finite-order differential operators, and records the basic algebraic and
order-filtration facts about it and about the order filtration itself,
mirroring `Stafford38.LocalizedDifferentialCorollaries.multiplicationD`.
-/

namespace GlobalStafford.Operators

open AlgebraicAnalysis.DifferentialOperators

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Multiplication by `a`, as an element of the subalgebra of finite-order
differential operators. -/
def multiplicationD (a : A) : algebra (k := k) (R := A) :=
  ⟨multiplication (k := k) a,
    ⟨0, (mem_order_zero_iff_eq_multiplication _).2 (by
      ext x
      simp [multiplication_apply])⟩⟩

@[simp] theorem coe_multiplicationD (a : A) :
    (multiplicationD (k := k) (A := A) a : Module.End k A) = multiplication (k := k) a := rfl

/-- `multiplicationD` is multiplicative. -/
theorem multiplicationD_mul (a b : A) :
    multiplicationD (k := k) (A := A) a * multiplicationD (k := k) (A := A) b =
      multiplicationD (k := k) (A := A) (a * b) := by
  apply Subtype.ext
  ext x
  simp [multiplicationD, multiplication_apply, mul_assoc]

/-- `multiplicationD` sends `1` to `1`. -/
theorem multiplicationD_one : multiplicationD (k := k) (A := A) (1 : A) = 1 := by
  apply Subtype.ext
  ext x
  simp [multiplicationD, multiplication_apply]

/-- `multiplicationD` is additive. -/
theorem multiplicationD_add (a b : A) :
    multiplicationD (k := k) (A := A) (a + b) =
      multiplicationD (k := k) (A := A) a + multiplicationD (k := k) (A := A) b := by
  apply Subtype.ext
  ext x
  simp [multiplicationD, multiplication_apply, add_mul]

theorem multiplicationD_zero : multiplicationD (k := k) (A := A) (0 : A) = 0 := by
  apply Subtype.ext
  ext x
  simp [multiplicationD, multiplication_apply]

/-- `multiplicationD` commutes with finite sums. -/
theorem multiplicationD_sum {ι : Type*} (s : Finset ι) (a : ι → A) :
    multiplicationD (k := k) (A := A) (∑ i ∈ s, a i) =
      ∑ i ∈ s, multiplicationD (k := k) (A := A) (a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [multiplicationD_zero]
  | insert a s hx ih => simp [Finset.sum_insert hx, multiplicationD_add, ih]

/-- `multiplicationD` commutes with powers. -/
theorem multiplicationD_pow (a : A) (n : ℕ) :
    multiplicationD (k := k) (A := A) a ^ n = multiplicationD (k := k) (A := A) (a ^ n) := by
  induction n with
  | zero => simp [multiplicationD_one]
  | succ n ih => rw [pow_succ, pow_succ, ih, multiplicationD_mul]

/-- `multiplicationD` sends units to units. -/
theorem multiplicationD_isUnit {a : A} (h : IsUnit a) :
    IsUnit (multiplicationD (k := k) (A := A) a) := by
  rcases h with ⟨u, hu⟩
  refine ⟨⟨multiplicationD (k := k) (A := A) a,
      multiplicationD (k := k) (A := A) u.inv, ?_, ?_⟩, rfl⟩
  · have h : a * u.inv = 1 := by rw [← hu]; exact u.val_inv
    show multiplicationD (k := k) (A := A) a * multiplicationD (k := k) (A := A) u.inv = 1
    rw [multiplicationD_mul, h, multiplicationD_one]
  · have h : u.inv * a = 1 := by rw [← hu]; exact u.inv_val
    show multiplicationD (k := k) (A := A) u.inv * multiplicationD (k := k) (A := A) a = 1
    rw [multiplicationD_mul, h, multiplicationD_one]

/-- Every element of `algebra k A` has finite order. -/
theorem exists_order (P : algebra (k := k) (R := A)) :
    ∃ r, (P : Module.End k A) ∈ order r :=
  (mem_algebra_iff _).1 P.2

/-- Orders add under multiplication in the subalgebra. -/
theorem mul_mem_orderD {P Q : algebra (k := k) (R := A)} {m n : ℕ}
    (hP : (P : Module.End k A) ∈ order m) (hQ : (Q : Module.End k A) ∈ order n) :
    ((P * Q : algebra (k := k) (R := A)) : Module.End k A) ∈ order (m + n) := by
  rw [Subalgebra.coe_mul]
  exact mul_mem_order hP hQ

/-- `multiplicationD a` has order `0`. -/
theorem multiplicationD_mem_order_zero (a : A) :
    (multiplicationD (k := k) (A := A) a : Module.End k A) ∈ order 0 := by
  rw [coe_multiplicationD]
  exact (mem_order_zero_iff_eq_multiplication _).2 (by ext x; simp [multiplication_apply])

/-- The order filtration is stable under `k`-scalar multiplication in the
subalgebra. -/
theorem smul_mem_order {P : algebra (k := k) (R := A)} {r : ℕ} (c : k)
    (hP : (P : Module.End k A) ∈ order r) :
    ((c • P : algebra (k := k) (R := A)) : Module.End k A) ∈ order r := by
  rw [Subalgebra.coe_smul]
  exact (order (k := k) (R := A) r).smul_mem c hP

/-- The order filtration is stable under finite sums in the subalgebra. -/
theorem sum_mem_order {ι : Type*} {s : Finset ι} {P : ι → algebra (k := k) (R := A)} {r : ℕ}
    (h : ∀ i ∈ s, (P i : Module.End k A) ∈ order r) :
    ((∑ i ∈ s, P i : algebra (k := k) (R := A)) : Module.End k A) ∈ order r := by
  rw [AddSubmonoidClass.coe_finsetSum]
  exact (order (k := k) (R := A) r).sum_mem h

end GlobalStafford.Operators

#print axioms GlobalStafford.Operators.coe_multiplicationD
#print axioms GlobalStafford.Operators.multiplicationD_mul
#print axioms GlobalStafford.Operators.multiplicationD_one
#print axioms GlobalStafford.Operators.multiplicationD_add
#print axioms GlobalStafford.Operators.multiplicationD_sum
#print axioms GlobalStafford.Operators.multiplicationD_pow
#print axioms GlobalStafford.Operators.multiplicationD_isUnit
#print axioms GlobalStafford.Operators.exists_order
#print axioms GlobalStafford.Operators.mul_mem_orderD
#print axioms GlobalStafford.Operators.multiplicationD_mem_order_zero
#print axioms GlobalStafford.Operators.smul_mem_order
#print axioms GlobalStafford.Operators.sum_mem_order
