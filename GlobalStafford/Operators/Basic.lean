import AlgebraicAnalysis.DifferentialOperators.Basic

/-!
# Multiplication operators (placeholder for WP-1)

`PLAN.md` §3, WP-1 (`Operators/Basic.lean`). WP-1 is being developed
concurrently in a separate worktree and is not yet available here. This
file provides the minimal subset of its interface that WP-2 needs:
`multiplicationD` and the basic coercion/unit lemmas, plus the order
lemmas `exists_order` and `mul_mem_orderD`. The controller reconciles this
copy with the WP-1 file when the branches merge.
-/

namespace GlobalStafford.Operators

open AlgebraicAnalysis.DifferentialOperators

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Multiplication by `a`, as an element of the differential-operator
subalgebra `D_k(A)` (order `0`). -/
def multiplicationD (a : A) : algebra (k := k) (R := A) :=
  ⟨multiplication (k := k) a,
    ⟨0, (mem_order_zero_iff_eq_multiplication _).2 (by
      ext x
      simp [multiplication_apply])⟩⟩

@[simp] theorem coe_multiplicationD (a : A) :
    (multiplicationD (k := k) (A := A) a : Module.End k A) = multiplication (k := k) a := rfl

theorem multiplicationD_mul (a b : A) :
    multiplicationD (k := k) (A := A) a * multiplicationD (k := k) (A := A) b =
      multiplicationD (k := k) (A := A) (a * b) := by
  apply Subtype.ext
  ext x
  simp [multiplicationD, multiplication_apply, mul_assoc]

theorem multiplicationD_one : multiplicationD (k := k) (A := A) (1 : A) = 1 := by
  apply Subtype.ext
  ext x
  simp [multiplicationD, multiplication_apply]

theorem multiplicationD_pow (a : A) (n : ℕ) :
    multiplicationD (k := k) (A := A) a ^ n = multiplicationD (k := k) (A := A) (a ^ n) := by
  induction n with
  | zero => simp [multiplicationD_one]
  | succ n ih => rw [pow_succ, pow_succ, ih, multiplicationD_mul]

theorem multiplicationD_isUnit {a : A} (h : IsUnit a) :
    IsUnit (multiplicationD (k := k) (A := A) a) := by
  rcases h with ⟨u, hu⟩
  refine ⟨⟨multiplicationD (k := k) (A := A) a,
      multiplicationD (k := k) (A := A) u.inv, ?_, ?_⟩, rfl⟩
  · have h : a * u.inv = 1 := by rw [← hu]; exact u.val_inv
    rw [multiplicationD_mul, h, multiplicationD_one]
  · have h : u.inv * a = 1 := by rw [← hu]; exact u.inv_val
    rw [multiplicationD_mul, h, multiplicationD_one]

/-- Every element of `D_k(A)` has some finite order. -/
theorem exists_order (P : algebra (k := k) (R := A)) :
    ∃ r, (P : Module.End k A) ∈ order (k := k) (R := A) r :=
  P.property

/-- Orders add under multiplication of differential operators. -/
theorem mul_mem_orderD {P Q : algebra (k := k) (R := A)} {m n : ℕ}
    (hP : (P : Module.End k A) ∈ order (k := k) (R := A) m)
    (hQ : (Q : Module.End k A) ∈ order (k := k) (R := A) n) :
    ((P * Q : algebra (k := k) (R := A)) : Module.End k A) ∈ order (k := k) (R := A) (m + n) := by
  have : ((P * Q : algebra (k := k) (R := A)) : Module.End k A) = (P : Module.End k A) * (Q : Module.End k A) :=
    rfl
  rw [this]
  exact mul_mem_order hP hQ

end GlobalStafford.Operators
