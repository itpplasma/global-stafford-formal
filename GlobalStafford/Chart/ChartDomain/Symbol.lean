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

theorem multiplication_mul_multiplication (a b : C) :
    multiplication (k := k) (R := C) (a * b) =
      multiplication (k := k) (R := C) a * multiplication (k := k) (R := C) b := by
  ext x
  simp [multiplication_apply, mul_assoc]

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

/-! ## 6. The composition rule -/

/-- Right composition with `∂^β` on a normal form is the polynomial multiplication by `X^β`. -/
theorem opOf_mul_partialMonomial (f : MvPolynomial (Fin n) C) (β : Fin n →₀ ℕ) :
    opOf (k := k) (C := C) f * partialMonomial (k := k) (C := C) β =
      opOf (k := k) (C := C) (f * MvPolynomial.monomial β (1 : C)) := by
  induction f using MvPolynomial.induction_on' with
  | monomial α a =>
      rw [MvPolynomial.monomial_mul, mul_one, opOf_monomial, opOf_monomial,
        smul_mul_assoc' (k := k), partialMonomial_add]
  | add f g hf hg =>
      rw [add_mul, map_add, map_add, add_mul, hf, hg]

/-- One-step commutation: `∂_i` moves past a multiplication operator at the price of the
derivative of the coefficient (`Derivation.leibniz`). -/
theorem liftDerivation_mul_multiplication (i : Fin n) (c : C) :
    (liftDerivation (k := k) (C := C) i).toLinearMap * multiplication (k := k) (R := C) c =
      multiplication (k := k) (R := C) c *
          (liftDerivation (k := k) (C := C) i).toLinearMap +
        multiplication (k := k) (R := C) ((liftDerivation (k := k) (C := C) i) c) := by
  ext x
  simp only [Module.End.mul_apply, multiplication_apply, LinearMap.add_apply,
    Derivation.coeFn_coe]
  rw [(liftDerivation (k := k) (C := C) i).leibniz]
  simp [smul_eq_mul, mul_comm]

/-- Removing one derivation from a nonzero multi-index. -/
theorem exists_pred_of_ne_zero {α : Fin n →₀ ℕ} (hα : α ≠ 0) :
    ∃ (i : Fin n) (α' : Fin n →₀ ℕ), α = α' + Finsupp.single i 1 ∧ α'.degree + 1 = α.degree := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hα (Finsupp.ext hcon)
  refine ⟨i, α - Finsupp.single i 1, ?_, ?_⟩
  · ext j
    by_cases hj : j = i
    · subst hj
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, hj, Ne.symm hj]
  · have hsplit : (α - Finsupp.single i 1) + Finsupp.single i 1 = α := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, hj, Ne.symm hj]
    calc (α - Finsupp.single i 1).degree + 1
        = (α - Finsupp.single i 1).degree + (Finsupp.single i 1 : Fin n →₀ ℕ).degree := by
          rw [Finsupp.degree_single]
      _ = ((α - Finsupp.single i 1) + Finsupp.single i 1 : Fin n →₀ ℕ).degree := (map_add _ _ _).symm
      _ = α.degree := by rw [hsplit]

/-- **Composition rule (weak form)**: `∂^α` commutes with a multiplication operator up to a
normal form of strictly smaller total degree. -/
theorem partialMonomial_commutator_mem_aux : ∀ (d : ℕ) (α : Fin n →₀ ℕ), α.degree ≤ d →
    ∀ c : C, partialMonomial (k := k) (C := C) α * multiplication (k := k) (R := C) c -
        multiplication (k := k) (R := C) c * partialMonomial (k := k) (C := C) α ∈
      Submodule.map (opOf (k := k) (C := C) (n := n)) (degLt (C := C) (n := n) α.degree) := by
  intro d
  induction d with
  | zero =>
      intro α hα c
      have hα0 : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (Nat.le_zero.mp hα)
      subst hα0
      simp
  | succ d ih =>
      intro α hα c
      by_cases hα0 : α = 0
      · subst hα0; simp
      obtain ⟨i, α', hsplit, hdeg⟩ := exists_pred_of_ne_zero hα0
      have hα'd : α'.degree ≤ d := by omega
      have hαA : partialMonomial (k := k) (C := C) α =
          partialMonomial (k := k) (C := C) α' *
            (liftDerivation (k := k) (C := C) i).toLinearMap := by
        rw [hsplit, partialMonomial_add, partialMonomial_single, pow_one]
      -- first correction: the induction hypothesis for `α'`, pushed right past `∂_i`
      obtain ⟨h₁, hh₁, hh₁eq⟩ := ih α' hα'd c
      -- second correction: the induction hypothesis for `α'` and the derived coefficient
      obtain ⟨h₂, hh₂, hh₂eq⟩ := ih α' hα'd ((liftDerivation (k := k) (C := C) i) c)
      refine ⟨h₁ * MvPolynomial.monomial (Finsupp.single i 1) (1 : C) + h₂ +
        MvPolynomial.monomial α' ((liftDerivation (k := k) (C := C) i) c), ?_, ?_⟩
      · refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
        · have := mul_monomial_mem_degLt (C := C) (n := n) hh₁ (Finsupp.single i 1)
          rw [Finsupp.degree_single] at this
          exact degLt_mono (by omega) this
        · exact degLt_mono (by omega) hh₂
        · exact monomial_mem_degLt (by omega) _
      · have hexp : opOf (k := k) (C := C)
            (h₁ * MvPolynomial.monomial (Finsupp.single i 1) (1 : C)) =
              opOf (k := k) (C := C) h₁ *
                (liftDerivation (k := k) (C := C) i).toLinearMap := by
          rw [← opOf_mul_partialMonomial, partialMonomial_single, pow_one]
        rw [map_add, map_add, hexp, hh₁eq, hh₂eq, opOf_monomial,
          smul_eq_multiplication_mul (k := k)]
        rw [hαA]
        have hstep := liftDerivation_mul_multiplication (k := k) (C := C) i c
        rw [mul_assoc (partialMonomial (k := k) (C := C) α')
          (liftDerivation (k := k) (C := C) i).toLinearMap
          (multiplication (k := k) (R := C) c), hstep]
        simp only [sub_mul, mul_sub, mul_add, add_mul, mul_assoc]
        abel

/-- **Composition rule (weak form)**, the form used below. -/
theorem partialMonomial_commutator_mem (α : Fin n →₀ ℕ) (c : C) :
    partialMonomial (k := k) (C := C) α * multiplication (k := k) (R := C) c -
        multiplication (k := k) (R := C) c * partialMonomial (k := k) (C := C) α ∈
      Submodule.map (opOf (k := k) (C := C) (n := n)) (degLt (C := C) (n := n) α.degree) :=
  partialMonomial_commutator_mem_aux α.degree α le_rfl c

/-! ## 7a. Multiplicativity of `opOf` modulo lower degree -/

/-- The single-monomial case of the product formula: composing two normal-form monomials
reproduces the polynomial product up to a normal form of total degree `< r`. -/
theorem opOf_monomial_mul_sub_mem (α β : Fin n →₀ ℕ) (a b : C) (r : ℕ)
    (hr : α.degree + β.degree ≤ r) :
    opOf (k := k) (C := C) (MvPolynomial.monomial α a) *
        opOf (k := k) (C := C) (MvPolynomial.monomial β b) -
        opOf (k := k) (C := C) (MvPolynomial.monomial α a * MvPolynomial.monomial β b) ∈
      Submodule.map (opOf (k := k) (C := C) (n := n)) (degLt (C := C) (n := n) r) := by
  obtain ⟨h, hh, hheq⟩ := partialMonomial_commutator_mem (k := k) (C := C) α b
  refine ⟨a • (h * MvPolynomial.monomial β (1 : C)), ?_, ?_⟩
  · refine Submodule.smul_mem _ a ?_
    exact degLt_mono hr (mul_monomial_mem_degLt (C := C) (n := n) hh β)
  · rw [map_smul, ← opOf_mul_partialMonomial]
    rw [MvPolynomial.monomial_mul, opOf_monomial, opOf_monomial, opOf_monomial, hheq]
    simp only [smul_eq_multiplication_mul (k := k),
      multiplication_mul_multiplication (k := k), partialMonomial_add,
      sub_mul, mul_sub, mul_assoc]

/-- The product formula for finite sums of monomials: composition of two normal forms agrees
with the polynomial product up to total degree `< r`. -/
theorem opOf_sum_mul_sub_mem (r : ℕ) (s t : Finset (Fin n →₀ ℕ)) (a b : (Fin n →₀ ℕ) → C)
    (hst : ∀ α ∈ s, ∀ β ∈ t, α.degree + β.degree ≤ r) :
    opOf (k := k) (C := C) (∑ α ∈ s, MvPolynomial.monomial α (a α)) *
        opOf (k := k) (C := C) (∑ β ∈ t, MvPolynomial.monomial β (b β)) -
        opOf (k := k) (C := C)
          ((∑ α ∈ s, MvPolynomial.monomial α (a α)) *
            (∑ β ∈ t, MvPolynomial.monomial β (b β))) ∈
      Submodule.map (opOf (k := k) (C := C) (n := n)) (degLt (C := C) (n := n) r) := by
  rw [map_sum, map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, map_sum]
  simp only [map_sum]
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun α hα => ?_)
  rw [← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ (fun β hβ =>
    opOf_monomial_mul_sub_mem (k := k) (C := C) α β (a α) (b β) r (hst α hα β hβ))

theorem finsupp_degree_eq_sum (d : Fin n →₀ ℕ) : d.degree = d.sum fun _ e => e := rfl

/-- **Product formula**: composition of two normal forms agrees with the polynomial product of
their coefficient polynomials, up to a normal form of total degree `< p + q`. -/
theorem opOf_mul_sub_mem (f g : MvPolynomial (Fin n) C) (p q : ℕ)
    (hf : ∀ α ∈ f.support, α.degree ≤ p) (hg : ∀ β ∈ g.support, β.degree ≤ q) :
    opOf (k := k) (C := C) f * opOf (k := k) (C := C) g -
        opOf (k := k) (C := C) (f * g) ∈
      Submodule.map (opOf (k := k) (C := C) (n := n)) (degLt (C := C) (n := n) (p + q)) := by
  have h := opOf_sum_mul_sub_mem (k := k) (C := C) (p + q) f.support g.support
    (fun α => MvPolynomial.coeff α f) (fun β => MvPolynomial.coeff β g)
    (fun α hα β hβ => Nat.add_le_add (hf α hα) (hg β hβ))
  rwa [← MvPolynomial.as_sum f, ← MvPolynomial.as_sum g] at h

/-! ## 7b. The leading symbol separates: `opOf` of a product is nonzero -/

/-- **Symbol multiplicativity**: the composition of two nonzero normal forms is nonzero, because
its degree-`(p+q)` part is the product of the two leading symbols in the domain
`MvPolynomial (Fin n) C`. -/
theorem opOf_mul_ne_zero {f g : MvPolynomial (Fin n) C} (hf : f ≠ 0) (hg : g ≠ 0) :
    opOf (k := k) (C := C) f * opOf (k := k) (C := C) g ≠ 0 := by
  intro hzero
  obtain ⟨e, he, heq⟩ := opOf_mul_sub_mem (k := k) (C := C) f g f.totalDegree g.totalDegree
    (fun α hα => by
      rw [finsupp_degree_eq_sum]; exact MvPolynomial.le_totalDegree hα)
    (fun β hβ => by
      rw [finsupp_degree_eq_sum]; exact MvPolynomial.le_totalDegree hβ)
  rw [hzero, zero_sub] at heq
  have hfg : f * g = -e := by
    refine opOf_injective (k := k) (C := C) (n := n) ?_
    rw [map_neg, heq, neg_neg]
  have hmem : f * g ∈ degLt (C := C) (n := n) (f.totalDegree + g.totalDegree) := by
    rw [hfg]
    exact Submodule.neg_mem _ he
  have hne : f * g ≠ 0 := mul_ne_zero hf hg
  have hsup : (f * g).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    exact hne (MvPolynomial.support_eq_empty.mp hcon)
  obtain ⟨β, hβ, hβeq⟩ := Finset.exists_mem_eq_sup (f * g).support hsup
    (fun s : Fin n →₀ ℕ => s.sum fun _ e => e)
  have hdeg : (f * g).totalDegree = f.totalDegree + g.totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hf hg
  have hβdeg : β.degree = f.totalDegree + g.totalDegree := by
    rw [finsupp_degree_eq_sum, ← hβeq]
    exact hdeg
  exact absurd hβdeg (Nat.ne_of_lt (hmem β hβ))

end
end GlobalStafford.Chart
