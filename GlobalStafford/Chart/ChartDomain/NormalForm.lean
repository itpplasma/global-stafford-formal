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

/-! ## 4. `C`-spanning -/

/-- **`mem_span_partialMonomial`**: every intrinsic finite-order differential operator on `C`
lies in the `C`-span of `partialMonomial` (`Chart/ChartDomain/Monomials.lean`), via
`mem_submodule_of_coordinates'` applied to the `k`-submodule underlying the `C`-span (a `C`-span
is automatically a `k`-submodule by restriction of scalars along `algebraMap k C`). -/
theorem mem_span_partialMonomial (P : Module.End k C) (hP : P ∈ algebra (k := k) (R := C)) :
    P ∈ Submodule.span C
      (Set.range (partialMonomial (k := k) (C := C) : (Fin n →₀ ℕ) → Module.End k C)) := by
  set Dspan : Submodule k (Module.End k C) :=
    (Submodule.span C (Set.range (partialMonomial (k := k) (C := C) (n := n)))).restrictScalars k with hDspan
  have hmul : ∀ r : C, multiplication (k := k) (R := C) r ∈ Dspan := by
    intro r
    rw [hDspan, Submodule.restrictScalars_mem]
    have heq : multiplication (k := k) (R := C) r =
        r • partialMonomial (k := k) (C := C) (0 : Fin n →₀ ℕ) := by
      rw [partialMonomial_zero]
      ext x
      simp [multiplication_apply]
    rw [heq]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨0, rfl⟩)
  have hright : ∀ (i : Fin n) (Q : Module.End k C), Q ∈ Dspan →
      Q * (liftDerivation (k := k) (C := C) i).toLinearMap ∈ Dspan := by
    intro i Q hQ
    rw [hDspan, Submodule.restrictScalars_mem] at hQ ⊢
    induction hQ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨α, rfl⟩ := hx
        rw [← pow_one (liftDerivation (k := k) (C := C) i).toLinearMap,
          ← partialMonomial_single i 1, ← partialMonomial_add]
        exact Submodule.subset_span ⟨α + Finsupp.single i 1, rfl⟩
    | zero =>
        simpa using Submodule.zero_mem _
    | add x y _ _ ihx ihy =>
        rw [add_mul]
        exact Submodule.add_mem _ ihx ihy
    | smul c x _ ihx =>
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ c ihx
  have hmem := AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration.mem_submodule_of_coordinates'
    (xC k n C) (liftDerivation (k := k) (C := C)) (liftDerivation_coord (k := k) (C := C))
    (fun P hP h => coordinateRigidity P hP h) Dspan hmul hright P hP
  rwa [hDspan, Submodule.restrictScalars_mem] at hmem

end
end GlobalStafford.Chart

#print axioms GlobalStafford.Chart.algebraMap_factorial_ne_zero
#print axioms GlobalStafford.Chart.linearIndependent_partialMonomial
#print axioms GlobalStafford.Chart.mem_span_partialMonomial
