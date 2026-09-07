import GlobalStafford.Chart.EtaleDerivations

/-!
# Iterated coordinate derivations and their action on polynomial monomials

`PLAN.md` §4, work package WP-14, steps 1–2 (`Chart/ChartDomain/Monomials.lean`). For `C` étale
over `B = k[x_1,…,x_n]`, this file packages iterated products of the coordinate derivations
`liftDerivation i` from `Chart/EtaleDerivations.lean` into `partialMonomial α : Module.End k C`
for a multi-index `α : Fin n →₀ ℕ` (`Finset.noncommProd` over the coordinates, well defined
since the derivations commute, `liftDerivation_comm`), and computes its action on the image of a
polynomial monomial of `B` (`pderiv_iterate_monomial`, `liftDerivation_pow_algebraMap`): the
coefficient picks up a product of descending factorials, and vanishes once some exponent of `α`
exceeds the corresponding exponent of `β`.
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators

noncomputable section

universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {C : Type u} [CommRing C] [Algebra k C]
  [Algebra (B k n) C] [IsScalarTower k (B k n) C] [Algebra.FormallyEtale (B k n) C]

/-! ## 1. `partialMonomial` -/

/-- The coordinate derivations of `C`, as linear endomorphisms, pairwise commute
(`liftDerivation_comm`, restated in the `Commute` API). -/
theorem liftDerivation_commute (i j : Fin n) :
    Commute ((liftDerivation (k := k) (C := C) i).toLinearMap)
      ((liftDerivation (k := k) (C := C) j).toLinearMap) :=
  liftDerivation_comm i j

/-- Pairwise commutation of the family `i ↦ (liftDerivation i).toLinearMap ^ α i` over any
finset, needed to form `partialMonomial α` (and its partial products) as `Finset.noncommProd`. -/
theorem liftDerivation_pow_commute_pairwise (α : Fin n →₀ ℕ) (s : Finset (Fin n)) :
    (s : Set (Fin n)).Pairwise
      (Function.onFun Commute fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ α i) :=
  fun i _ j _ _ => (liftDerivation_commute (k := k) (C := C) i j).pow_pow (α i) (α j)

/-- **`partialMonomial`**: the iterated coordinate derivation `∏ i, (∂_i)^{α i}`, well defined
since the factors pairwise commute. -/
def partialMonomial (α : Fin n →₀ ℕ) : Module.End k C :=
  Finset.univ.noncommProd
    (fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ α i)
    (liftDerivation_pow_commute_pairwise α Finset.univ)

theorem partialMonomial_eq_noncommProd (α : Fin n →₀ ℕ)
    (comm : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Commute fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ α i)) :
    partialMonomial (k := k) (C := C) α =
      Finset.univ.noncommProd
        (fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ α i) comm := rfl

@[simp] theorem partialMonomial_zero :
    partialMonomial (k := k) (C := C) (0 : Fin n →₀ ℕ) = 1 := by
  unfold partialMonomial
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 (fun i _ => by simp), one_pow]

/-- `partialMonomial` peels off the `i`-th factor, matching the recursion used to prove
`partialMonomial_add` and the action on monomials. -/
theorem partialMonomial_eq_mul_erase (α : Fin n →₀ ℕ) (i : Fin n) :
    partialMonomial (k := k) (C := C) α =
      (liftDerivation (k := k) (C := C) i).toLinearMap ^ α i *
        (Finset.univ.erase i).noncommProd
          (fun j => (liftDerivation (k := k) (C := C) j).toLinearMap ^ α j)
          (liftDerivation_pow_commute_pairwise α (Finset.univ.erase i)) := by
  have heq := Finset.noncommProd_congr
      (s₁ := (Finset.univ : Finset (Fin n)))
      (s₂ := insert i (Finset.univ.erase i))
      (f := fun j => (liftDerivation (k := k) (C := C) j).toLinearMap ^ α j)
      (Finset.insert_erase (Finset.mem_univ i)).symm (fun _ _ => rfl)
      (liftDerivation_pow_commute_pairwise α Finset.univ)
  have hins := Finset.noncommProd_insert_of_notMem (Finset.univ.erase i) i
      (fun j => (liftDerivation (k := k) (C := C) j).toLinearMap ^ α j)
      (liftDerivation_pow_commute_pairwise α (insert i (Finset.univ.erase i)))
      (Finset.notMem_erase i _)
  rw [partialMonomial_eq_noncommProd α (liftDerivation_pow_commute_pairwise α Finset.univ)]
  exact heq.trans hins

theorem partialMonomial_single (i : Fin n) (m : ℕ) :
    partialMonomial (k := k) (C := C) (Finsupp.single i m) =
      (liftDerivation (k := k) (C := C) i).toLinearMap ^ m := by
  rw [partialMonomial_eq_mul_erase _ i]
  simp only [Finsupp.single_eq_same]
  rw [Finset.noncommProd_eq_pow_card (Finset.univ.erase i) _ _ 1
      (fun j hj => by
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [Finsupp.single_apply, hji]),
    one_pow, mul_one]

theorem partialMonomial_add (α β : Fin n →₀ ℕ) :
    partialMonomial (k := k) (C := C) (α + β) =
      partialMonomial (k := k) (C := C) α * partialMonomial (k := k) (C := C) β := by
  have hcomm := liftDerivation_pow_commute_pairwise (k := k) (C := C) α Finset.univ
  have hcomm' := liftDerivation_pow_commute_pairwise (k := k) (C := C) β Finset.univ
  have hcomm'' : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (fun i j => Commute
        ((fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ β i) i)
        ((fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ α i) j)) := by
    intro i _ j _ _
    exact ((liftDerivation_commute (k := k) (C := C) j i).pow_pow (α j) (β i)).symm
  have hmix := liftDerivation_pow_commute_pairwise (k := k) (C := C) (α + β) Finset.univ
  have hbridge :
      partialMonomial (k := k) (C := C) (α + β) =
        Finset.univ.noncommProd
          ((fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ α i) *
            fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ β i)
          (Finset.noncommProd_mul_distrib_aux hcomm hcomm' hcomm'') := by
    rw [partialMonomial_eq_noncommProd (α + β) hmix]
    apply Finset.noncommProd_congr rfl
    intro i _
    simp [Pi.mul_apply, Finsupp.add_apply, pow_add]
  rw [hbridge, Finset.noncommProd_mul_distrib _ _ hcomm hcomm' hcomm'']
  rw [partialMonomial_eq_noncommProd α hcomm, partialMonomial_eq_noncommProd β hcomm']

/-- `partialMonomial α` is an intrinsic finite-order differential operator. -/
theorem partialMonomial_mem_algebra (α : Fin n →₀ ℕ) :
    partialMonomial (k := k) (C := C) α ∈ algebra (k := k) (R := C) := by
  unfold partialMonomial
  apply Finset.noncommProd_induction _ _ _
    (fun P => P ∈ algebra (k := k) (R := C))
    (fun P Q hP hQ => (algebra (k := k) (R := C)).mul_mem hP hQ)
    (algebra (k := k) (R := C)).one_mem
  intro i _
  have hder : (liftDerivation (k := k) (C := C) i).toLinearMap ∈ algebra (k := k) (R := C) :=
    AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration.derivation_mem_algebra
      (k := k) (R := C) (liftDerivation (k := k) (C := C) i)
  exact (algebra (k := k) (R := C)).pow_mem hder _

/-! ## 2. Action on polynomial monomials -/

/-- `liftDerivation i`, iterated `a` times, transports along `algebraMap` to the `a`-th iterate
of `MvPolynomial.pderiv i`. -/
theorem liftDerivation_pow_algebraMap (i : Fin n) (a : ℕ) (b : B k n) :
    ((liftDerivation (k := k) (C := C) i).toLinearMap ^ a) (algebraMap (B k n) C b) =
      algebraMap (B k n) C ((MvPolynomial.pderiv i)^[a] b) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
      rw [pow_succ', Module.End.mul_apply, ih, Derivation.coeFn_coe, liftDerivation_algebraMap]
      exact congrArg (algebraMap (B k n) C)
        (Function.iterate_succ_apply' (MvPolynomial.pderiv i) a b).symm

/-- Peeling the leading factor off a descending factorial. -/
theorem descFactorial_succ' (n a : ℕ) :
    n.descFactorial (a + 1) = n * (n - 1).descFactorial a := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
    Finset.prod_range_succ']
  rw [Nat.sub_zero, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  omega

/-- The `a`-th iterate of `MvPolynomial.pderiv i` on a monomial: a descending-factorial
coefficient, and the `i`-th exponent truncated-subtracted by `a`. -/
theorem pderiv_iterate_monomial (i : Fin n) (a : ℕ) (β : Fin n →₀ ℕ) (r : k) :
    (MvPolynomial.pderiv i)^[a] (MvPolynomial.monomial β r) =
      MvPolynomial.monomial (β - Finsupp.single i a) (r * (Nat.descFactorial (β i) a : k)) := by
  induction a generalizing β r with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply, MvPolynomial.pderiv_monomial, ih]
      have hidx : (β - Finsupp.single i 1 : Fin n →₀ ℕ) i = β i - 1 := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      have hexp : (β - Finsupp.single i 1 : Fin n →₀ ℕ) - Finsupp.single i a =
          β - Finsupp.single i (a + 1) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp [Finsupp.tsub_apply, Finsupp.single_apply, hidx]; omega
        · simp [Finsupp.tsub_apply, Finsupp.single_apply, hj, Ne.symm hj]
      have hcoeff : (r * (β i : k)) *
          (Nat.descFactorial ((β - Finsupp.single i 1 : Fin n →₀ ℕ) i) a : k) =
          r * (Nat.descFactorial (β i) (a + 1) : k) := by
        rw [hidx, descFactorial_succ' (β i) a]
        push_cast
        ring
      rw [hexp, hcoeff]

/-! ## 3. Action of `partialMonomial` on polynomial monomials, over an arbitrary finset -/

theorem algebraMap_C (c : k) :
    algebraMap (B k n) C (MvPolynomial.C c) = algebraMap k C c := by
  calc
    algebraMap (B k n) C (MvPolynomial.C c)
        = algebraMap (B k n) C (algebraMap k (B k n) c) := by rw [MvPolynomial.algebraMap_eq]
    _ = algebraMap k C c := (IsScalarTower.algebraMap_apply k (B k n) C c).symm

/-- The action of the partial-derivative product indexed by an arbitrary finset `S` on the
image of a polynomial monomial: a descending-factorial coefficient over `S`, and the exponents
in `S` truncated-subtracted. -/
theorem partialMonomial_finset_monomial (S : Finset (Fin n)) (α β : Fin n →₀ ℕ) (r : k) :
    (S.noncommProd (fun i => (liftDerivation (k := k) (C := C) i).toLinearMap ^ α i)
        (liftDerivation_pow_commute_pairwise α S))
      (algebraMap (B k n) C (MvPolynomial.monomial β r)) =
    algebraMap (B k n) C
      (MvPolynomial.monomial (β - S.sum (fun i => Finsupp.single i (α i)))
        (r * ∏ i ∈ S, (Nat.descFactorial (β i) (α i) : k))) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons i S hiS ih =>
      rw [Finset.noncommProd_cons, Module.End.mul_apply, ih, liftDerivation_pow_algebraMap,
        pderiv_iterate_monomial]
      have hSi : (S.sum (fun j => Finsupp.single j (α j)) : Fin n →₀ ℕ) i = 0 := by
        rw [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro j hj
        have hji : j ≠ i := fun h => hiS (h ▸ hj)
        simp [Finsupp.single_apply, hji]
      have hidx : (β - S.sum (fun j => Finsupp.single j (α j)) : Fin n →₀ ℕ) i = β i := by
        rw [Finsupp.tsub_apply, hSi, Nat.sub_zero]
      have hexp : (β - S.sum (fun j => Finsupp.single j (α j)) : Fin n →₀ ℕ)
          - Finsupp.single i (α i) =
          β - (Finset.cons i S hiS).sum (fun j => Finsupp.single j (α j)) := by
        rw [Finset.sum_cons]
        ext j
        by_cases hj : j = i
        · subst hj
          simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.add_apply, hidx]
          omega
        · have hSj : (Finsupp.single i (α i) + S.sum (fun l => Finsupp.single l (α l))
              : Fin n →₀ ℕ) j = (S.sum (fun l => Finsupp.single l (α l)) : Fin n →₀ ℕ) j := by
            simp [Finsupp.add_apply, Finsupp.single_apply, hj]
          simp [Finsupp.tsub_apply, Finsupp.single_apply, hj, hSj]
      have hcoeff : (r * ∏ j ∈ S, (Nat.descFactorial (β j) (α j) : k)) *
          (Nat.descFactorial
              ((β - S.sum (fun j => Finsupp.single j (α j)) : Fin n →₀ ℕ) i) (α i) : k) =
          r * ∏ j ∈ Finset.cons i S hiS, (Nat.descFactorial (β j) (α j) : k) := by
        rw [hidx, Finset.prod_cons]
        ring
      rw [hexp, hcoeff]

/-- The diagonal value of `partialMonomial` on the matching monomial: a nonzero scalar
multiple determined by the factorials of the exponents. -/
theorem partialMonomial_monomial_self (β : Fin n →₀ ℕ) :
    partialMonomial (k := k) (C := C) β (algebraMap (B k n) C (MvPolynomial.monomial β (1 : k))) =
      algebraMap k C (∏ i, (β i).factorial : k) := by
  unfold partialMonomial
  rw [partialMonomial_finset_monomial Finset.univ β β 1]
  have hsum : (Finset.univ.sum (fun i => Finsupp.single i (β i)) : Fin n →₀ ℕ) = β :=
    Finsupp.univ_sum_single β
  have hself : ∀ i, (Nat.descFactorial (β i) (β i) : k) = ((β i).factorial : k) := by
    intro i; exact_mod_cast Nat.descFactorial_self (β i)
  rw [hsum, tsub_self, one_mul, Finset.prod_congr rfl (fun i _ => hself i),
    ← MvPolynomial.C_apply, algebraMap_C]

/-- Every exponent multi-index with a coordinate strictly exceeding `β`'s makes the
descending-factorial coefficient (and hence the action of `partialMonomial`) vanish, provided
the total degrees compare the other way. -/
theorem exists_lt_of_ne_of_degree_le {α β : Fin n →₀ ℕ} (hle : β.degree ≤ α.degree)
    (hne : α ≠ β) : ∃ i, β i < α i := by
  by_contra hcon
  push_neg at hcon
  have hne' : ∃ i, α i ≠ β i := by
    by_contra hall
    push_neg at hall
    exact hne (Finsupp.ext hall)
  obtain ⟨i0, hi0⟩ := hne'
  have hlt : α i0 < β i0 := lt_of_le_of_ne (hcon i0) hi0
  have hcontra : α.degree < β.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_lt_sum (fun i _ => hcon i) ⟨i0, Finset.mem_univ i0, hlt⟩
  omega

/-- **`partialMonomial_monomial_eq_zero_of_degree_le`**: if `α ≠ β` and `β`'s total degree is at
most `α`'s, `partialMonomial α` kills the image of the monomial `X^β`. -/
theorem partialMonomial_monomial_eq_zero_of_degree_le (α β : Fin n →₀ ℕ)
    (hle : β.degree ≤ α.degree) (hne : α ≠ β) (r : k) :
    partialMonomial (k := k) (C := C) α (algebraMap (B k n) C (MvPolynomial.monomial β r)) = 0 := by
  unfold partialMonomial
  rw [partialMonomial_finset_monomial Finset.univ α β r]
  obtain ⟨i0, hi0⟩ := exists_lt_of_ne_of_degree_le hle hne
  have hz : (Nat.descFactorial (β i0) (α i0) : k) = 0 := by
    exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr hi0
  have hprod : (∏ i, (Nat.descFactorial (β i) (α i) : k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i0) hz
  rw [hprod, mul_zero, MvPolynomial.monomial_zero, map_zero]

end
end GlobalStafford.Chart

#print axioms GlobalStafford.Chart.partialMonomial_add
#print axioms GlobalStafford.Chart.partialMonomial_single
#print axioms GlobalStafford.Chart.partialMonomial_mem_algebra
#print axioms GlobalStafford.Chart.liftDerivation_pow_algebraMap
#print axioms GlobalStafford.Chart.pderiv_iterate_monomial
#print axioms GlobalStafford.Chart.partialMonomial_finset_monomial
#print axioms GlobalStafford.Chart.partialMonomial_monomial_self
#print axioms GlobalStafford.Chart.partialMonomial_monomial_eq_zero_of_degree_le
