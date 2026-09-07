import GlobalStafford.Chart.ChartDomain.NormalForm
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Normal-form realization, the composition rule, and the leading symbol

`PLAN.md` §4, work package WP-14, steps 5–7 (`Chart/ChartDomain/Symbol.lean`).
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators

noncomputable section

universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {C : Type u} [CommRing C] [IsDomain C]
  [Algebra k C] [Algebra (B k n) C] [IsScalarTower k (B k n) C] [Algebra.FormallyEtale (B k n) C]

/-! ## 5a. Elementary `C`-module identities in `Module.End k C` -/

theorem smul_eq_multiplication_mul (c : C) (P : Module.End k C) :
    c • P = multiplication (k := k) (R := C) c * P := by
  ext x
  simp [multiplication_apply]

theorem smul_mul_assoc' (c : C) (P Q : Module.End k C) : (c • P) * Q = c • (P * Q) := by
  rw [smul_eq_multiplication_mul, smul_eq_multiplication_mul, mul_assoc]

/-! ## 5b. The normal-form realization map -/

/-- **`opOf`**: the realization of a coefficient polynomial `∑ c_α X^α` as the differential
operator `∑ c_α ∂^α` in normal form. -/
def opOf : MvPolynomial (Fin n) C →ₗ[C] Module.End k C :=
  (Finsupp.linearCombination C (partialMonomial (k := k) (C := C) (n := n))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R := C) (S := C) (M := Fin n →₀ ℕ)).toLinearMap

@[simp] theorem opOf_monomial (α : Fin n →₀ ℕ) (c : C) :
    opOf (k := k) (C := C) (MvPolynomial.monomial α c) =
      c • partialMonomial (k := k) (C := C) α := by
  simp [opOf, MvPolynomial.monomial, Finsupp.linearCombination_single]

theorem opOf_injective :
    Function.Injective (opOf (k := k) (C := C) (n := n)) := by
  intro f g h
  exact (AddMonoidAlgebra.coeffLinearEquiv (R := C) (S := C) (M := Fin n →₀ ℕ)).injective
    (linearIndependent_partialMonomial (k := k) (C := C) (n := n) h)

theorem exists_opOf (P : Module.End k C) (hP : P ∈ algebra (k := k) (R := C)) :
    ∃ f : MvPolynomial (Fin n) C, opOf (k := k) (C := C) f = P := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp
    (v := (partialMonomial (k := k) (C := C) (n := n) : (Fin n →₀ ℕ) → Module.End k C))
    |>.mp (mem_span_partialMonomial (k := k) (C := C) (n := n) P hP)
  refine ⟨(AddMonoidAlgebra.coeffLinearEquiv (R := C) (S := C) (M := Fin n →₀ ℕ)).symm c, ?_⟩
  simpa [opOf, Finsupp.linearCombination_apply] using hc

/-! ## 5c. The degree filtration on coefficient polynomials -/

/-- The `C`-submodule of coefficient polynomials all of whose monomials have total degree
strictly below `r`. -/
def degLt (r : ℕ) : Submodule C (MvPolynomial (Fin n) C) where
  carrier := {f | ∀ β ∈ f.support, β.degree < r}
  zero_mem' := by intro β hβ; simp at hβ
  add_mem' := by
    intro f g hf hg β hβ
    rcases Finset.mem_union.mp (MvPolynomial.support_add hβ) with h | h
    exacts [hf β h, hg β h]
  smul_mem' := by
    intro c f hf β hβ
    exact hf β (MvPolynomial.support_smul hβ)

theorem mem_degLt_iff {r : ℕ} {f : MvPolynomial (Fin n) C} :
    f ∈ degLt (C := C) (n := n) r ↔ ∀ β ∈ f.support, β.degree < r := Iff.rfl

theorem degLt_mono {r s : ℕ} (h : r ≤ s) : degLt (C := C) (n := n) r ≤ degLt s :=
  fun _ hf β hβ => lt_of_lt_of_le (hf β hβ) h

theorem monomial_mem_degLt {r : ℕ} {α : Fin n →₀ ℕ} (h : α.degree < r) (c : C) :
    MvPolynomial.monomial α c ∈ degLt (C := C) (n := n) r := by
  intro β hβ
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hβ)]
  exact h

theorem mul_monomial_mem_degLt {r : ℕ} {f : MvPolynomial (Fin n) C}
    (hf : f ∈ degLt (C := C) (n := n) r) (γ : Fin n →₀ ℕ) :
    f * MvPolynomial.monomial γ (1 : C) ∈ degLt (C := C) (n := n) (r + γ.degree) := by
  classical
  intro β hβ
  obtain ⟨β₁, hβ₁, β₂, hβ₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hβ)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hβ₂)]
  rw [map_add]
  exact Nat.add_lt_add_right (hf β₁ hβ₁) _

end
end GlobalStafford.Chart
