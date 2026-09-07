import GlobalStafford.Chart.ChartDomain.Monomials

/-!
# Left `C`-linear independence and spanning of `partialMonomial`

`PLAN.md` §4, work package WP-14, steps 3–4 (`Chart/ChartDomain/NormalForm.lean`). Assuming
additionally that `C` is a domain, the family `partialMonomial` is left-`C`-linearly independent
in `Module.End k C` (viewed as a `C`-module by left multiplication, `LinearMap.module`), via a
strong induction on the finite support removing, at each step, a multi-index of minimal total
degree and evaluating on the corresponding polynomial monomial (`Chart/ChartDomain/Monomials.lean`
`partialMonomial_monomial_self` / `partialMonomial_monomial_eq_zero_of_degree_le`).
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators

noncomputable section

universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {C : Type u} [CommRing C] [IsDomain C]
  [Algebra k C] [Algebra (B k n) C] [IsScalarTower k (B k n) C] [Algebra.FormallyEtale (B k n) C]

/-! ## 3. Left `C`-linear independence -/

theorem algebraMap_factorial_ne_zero (β : Fin n →₀ ℕ) :
    algebraMap k C (∏ i, (β i).factorial : k) ≠ 0 := by
  have hne : (∏ i, (β i).factorial : k) ≠ 0 := by
    have hnat : (∏ i : Fin n, (β i).factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
    have hcast : ((∏ i : Fin n, (β i).factorial : ℕ) : k) = ∏ i, ((β i).factorial : k) := by
      push_cast; ring
    rw [← hcast]
    exact_mod_cast hnat
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective k C)).mpr hne

/-- **`linearIndependent_partialMonomial`**: the family `partialMonomial` is left-`C`-linearly
independent in `Module.End k C`. -/
theorem linearIndependent_partialMonomial :
    LinearIndependent C (fun α : Fin n →₀ ℕ => partialMonomial (k := k) (C := C) α) := by
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro g hsum
    rcases s.eq_empty_or_nonempty with hempty | hsne
    · simp [hempty]
    · obtain ⟨m, hmmem, hmmin⟩ := Finset.exists_min_image s Finsupp.degree hsne
      have heval := congrArg
        (fun P : Module.End k C => P (algebraMap (B k n) C (MvPolynomial.monomial m 1))) hsum
      simp only [LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul] at heval
      have hsplit := Finset.add_sum_erase s
        (fun α => g α * partialMonomial (k := k) (C := C) α
          (algebraMap (B k n) C (MvPolynomial.monomial m 1))) hmmem
      have hzero_rest : ∑ α ∈ s.erase m, g α * partialMonomial (k := k) (C := C) α
          (algebraMap (B k n) C (MvPolynomial.monomial m 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro α hα
        have hα_mem : α ∈ s := Finset.mem_of_mem_erase hα
        have hα_ne : α ≠ m := Finset.ne_of_mem_erase hα
        rw [partialMonomial_monomial_eq_zero_of_degree_le α m (hmmin α hα_mem) hα_ne, mul_zero]
      have hfm : g m * partialMonomial (k := k) (C := C) m
          (algebraMap (B k n) C (MvPolynomial.monomial m 1)) = 0 := by
        have hcombine := hsplit.trans heval
        rwa [hzero_rest, add_zero] at hcombine
      rw [partialMonomial_monomial_self] at hfm
      have hgm : g m = 0 := by
        rcases mul_eq_zero.mp hfm with h | h
        · exact h
        · exact absurd h (algebraMap_factorial_ne_zero m)
      have hadd := Finset.add_sum_erase s
        (fun α => g α • partialMonomial (k := k) (C := C) α) hmmem
      simp only [hgm, zero_smul, zero_add] at hadd
      have hsum' : ∑ α ∈ s.erase m, g α • partialMonomial (k := k) (C := C) α = 0 :=
        hadd.trans hsum
      have hrest := ih (s.erase m) (Finset.erase_ssubset hmmem) g hsum'
      intro i hi
      by_cases him : i = m
      · subst him; exact hgm
      · exact hrest i (Finset.mem_erase.mpr ⟨him, hi⟩)

end
end GlobalStafford.Chart

#print axioms GlobalStafford.Chart.algebraMap_factorial_ne_zero
#print axioms GlobalStafford.Chart.linearIndependent_partialMonomial
