import AlgebraicAnalysis.Ore.RightHilbertBasis
import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity
import Stafford38.Weyl.IteratedEquivalence
import Stafford38.FoundationClosure
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The presented Weyl algebra is a right Ore domain

`PLAN.md` Section 4, work package WP-15 (`Weyl/OreDomain.lean`). Supplies
`NoZeroDivisors (PresentedWeyl k n)`, the right Ore condition
(`weyl_rightOre`), and the induced
`OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰` instance consumed as
hypotheses by `GlobalStafford/Chart/EtaleChartData.lean` and
`GlobalStafford/Assembly/PhaseI.lean`.

The domain property and the right Ore condition are both proved by the same
tower induction on the recursive Ore construction
`Stafford38.OreIteratedPairStage.IteratedPairStage`, transported along
`Stafford38.WeylIteratedEquivalence.presentedIteratedEquiv` to the presented
quotient `PresentedWeyl k n`:

* domain: each successor stage is `NormalOre D` over the previous stage for a
  derivation `D`; the leading-coefficient (top-degree) calculus of
  `AlgebraicAnalysis.Ore.RightDivision` shows `NormalOre D` is a domain
  whenever the coefficient ring is (`normalOre_noZeroDivisors`), generalizing
  the monic-only `rightMul_coeff_top` of that file to arbitrary nonzero
  factors.
* right Ore: each successor stage is right-Noetherian-transposed
  (`IsNoetherianRing (NormalOre D)ᵐᵒᵖ`) whenever the coefficient ring is, by
  `AlgebraicAnalysis.OreDerivationRightHilbertBasis.derivationOre_rightHilbertBasis`;
  the generic Goldie-style lemma `rightOre_of_rightNoetherian_domain` then
  produces the right Ore condition for any right-Noetherian domain from a
  strictly ascending chain of right ideals `Σ_{i<N} y^i x R`, contradicting
  `IsNoetherianRing Rᵐᵒᵖ`.
-/

namespace GlobalStafford.Weyl

open AlgebraicAnalysis AlgebraicAnalysis.OreAssociativity AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreDerivationRightHilbertBasis
open Stafford38.WeylIteratedEquivalence Stafford38.OreIteratedPairStage
open Stafford38.OrePairStage Stafford38.OreCoordinateStage
open scoped nonZeroDivisors

noncomputable section

universe u

/-! ## A `NormalOre` extension of a domain is a domain -/

section NormalOreDomain

variable {B : Type u} [Ring B]

/-- The top coefficient of the (unquotiented) right Ore product of two
nonzero coefficient-left polynomials, without assuming the first factor is
monic. Generalizes `AlgebraicAnalysis.OreDivision.rightMul_coeff_top`, whose
proof this mirrors. -/
private lemma rightMul_coeff_top_of_ne_zero [Nontrivial B]
    (D : OreDivisionDerivation B) (d q : Polynomial B) (hd : d ≠ 0) (hq : q ≠ 0) :
    (rightMul D d q).coeff (d.natDegree + q.natDegree) =
      d.leadingCoeff * q.leadingCoeff := by
  rw [rightMul, Polynomial.coeff_sum, Polynomial.sum_def]
  have hqtop : q.natDegree ∈ q.support :=
    Polynomial.natDegree_mem_support_of_nonzero hq
  rw [Finset.sum_eq_single q.natDegree (by
    intro j hj hne
    have hj_le : j ≤ q.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
    have hj_lt : j < q.natDegree := lt_of_le_of_ne hj_le hne
    have hdeg : (rightMulMonomial D d (q.coeff j) j).degree ≤
        (d.natDegree + j : WithBot ℕ) :=
      rightMulMonomial_degree_le D d (q.coeff j) j
    have hlt : (d.natDegree + j : WithBot ℕ) <
        (d.natDegree + q.natDegree : WithBot ℕ) := by
      exact_mod_cast Nat.add_lt_add_left hj_lt d.natDegree
    exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hdeg hlt))
    (by simp [hqtop])]
  exact rightMulMonomial_coeff_top D d hd (q.coeff q.natDegree) q.natDegree

/-- Over a domain coefficient ring, the right Ore product of two nonzero
polynomials is nonzero. -/
private lemma rightMul_ne_zero [Nontrivial B] [NoZeroDivisors B]
    (D : OreDivisionDerivation B) {p q : Polynomial B} (hp : p ≠ 0) (hq : q ≠ 0) :
    rightMul D p q ≠ 0 := by
  intro h
  have hc := rightMul_coeff_top_of_ne_zero D p q hp hq
  rw [h] at hc
  simp only [Polynomial.coeff_zero] at hc
  rcases mul_eq_zero.mp hc.symm with hc | hc
  · exact Polynomial.leadingCoeff_ne_zero.mpr hp hc
  · exact Polynomial.leadingCoeff_ne_zero.mpr hq hc

/-- `NormalOre D` over a domain coefficient ring is again a domain. -/
theorem normalOreNoZeroDivisors [Nontrivial B] [NoZeroDivisors B]
    (D : OreDivisionDerivation B) : NoZeroDivisors (NormalOre D) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro x y hxy
    by_contra hcon
    push_neg at hcon
    obtain ⟨hx, hy⟩ := hcon
    rcases normalForm_surjective D x with ⟨p, rfl⟩
    rcases normalForm_surjective D y with ⟨q, rfl⟩
    have hp : p ≠ 0 := fun h => hx (by rw [h, normalForm_zero])
    have hq : q ≠ 0 := fun h => hy (by rw [h, normalForm_zero])
    apply rightMul_ne_zero D hp hq
    apply normalForm_injective D
    rw [normalForm_mul, hxy, normalForm_zero]

/-- `NormalOre D` over a nontrivial coefficient ring is nontrivial. -/
theorem normalOreNontrivial [Nontrivial B] (D : OreDivisionDerivation B) :
    Nontrivial (NormalOre D) := by
  refine ⟨normalForm D 0, normalForm D 1, ?_⟩
  intro h
  exact zero_ne_one (normalForm_injective D h)

end NormalOreDomain

/-! ## The right Ore condition from right-Noetherianity -/

section RightOreOfRightNoetherian

variable {R : Type u} [Ring R] [Nontrivial R] [NoZeroDivisors R]

/-- The Goldie cancellation step: if `y` is not a right zero divisor and
`y^N * x` lies in the right ideal spanned by `{y^i * x : i < N}`, then
`x = 0`. This is the algebraic heart of `rightOre_of_rightNoetherian_domain`:
cancelling `y` from the left, repeatedly, forces every coefficient (and
hence `x` itself) to vanish. -/
private theorem eq_zero_of_mem_span_shifted_powers
    {x y : R} (hy : y ≠ 0) (hcon : ∀ a b : R, x * a = y * b → a = 0) :
    ∀ (N : ℕ) (r : Fin N → R),
      y ^ N * x = ∑ i : Fin N, y ^ (i : ℕ) * x * r i → x = 0 := by
  haveI : IsCancelMulZero R := NoZeroDivisors.toIsCancelMulZero
  intro N
  induction N with
  | zero =>
      intro r h
      simpa using h
  | succ N ih =>
      intro r h
      rw [Fin.sum_univ_succ] at h
      simp only [Fin.val_zero, pow_zero, one_mul] at h
      have hsucc : ∀ i : Fin N, y ^ (i.succ : ℕ) * x * r i.succ =
          y * (y ^ (i : ℕ) * x * r i.succ) := by
        intro i
        rw [Fin.val_succ, pow_succ']
        noncomm_ring
      rw [Finset.sum_congr rfl (fun i _ => hsucc i), ← Finset.mul_sum] at h
      rw [pow_succ', mul_assoc] at h
      have heq : x * r 0 = y * (y ^ N * x - ∑ i : Fin N, y ^ (i : ℕ) * x * r i.succ) := by
        rw [mul_sub, h]
        abel
      have hr0 : r 0 = 0 := hcon (r 0) _ heq
      rw [hr0, mul_zero, zero_add] at h
      have hcancel : y ^ N * x = ∑ i : Fin N, y ^ (i : ℕ) * x * r i.succ :=
        mul_left_cancel₀ hy h
      exact ih (fun i => r i.succ) hcancel

/-- A right-Noetherian domain satisfies the right Ore condition. The proof
builds the right ideal chain `I_N = Σ_{i<N} y^i x R` (as an `Rᵐᵒᵖ`-submodule
of `R`); `eq_zero_of_mem_span_shifted_powers` shows it is strictly
increasing under the negation of the conclusion, contradicting
`IsNoetherianRing Rᵐᵒᵖ`. -/
theorem rightOre_of_rightNoetherian_domain [IsNoetherianRing Rᵐᵒᵖ]
    (x y : R) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a b : R, a ≠ 0 ∧ x * a = y * b := by
  by_contra hcon
  push_neg at hcon
  have hcon' : ∀ a b : R, x * a = y * b → a = 0 := by
    intro a b hab
    by_contra ha
    exact hcon a b ha hab
  haveI : IsNoetherian Rᵐᵒᵖ R :=
    isNoetherian_of_linearEquiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm
  let ι : ℕ → Submodule Rᵐᵒᵖ R :=
    fun N => Submodule.span Rᵐᵒᵖ (Set.range (fun i : Fin N => y ^ (i : ℕ) * x))
  have hmono : Monotone ι := by
    intro N M hNM
    apply Submodule.span_mono
    rintro z ⟨i, rfl⟩
    exact ⟨Fin.castLE hNM i, rfl⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance ⟨ι, hmono⟩
  have hstab : ι n = ι (n + 1) := hn (n + 1) (Nat.le_succ n)
  have hmem : y ^ n * x ∈ ι (n + 1) :=
    Submodule.subset_span ⟨Fin.last n, by simp⟩
  rw [← hstab] at hmem
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : y ^ n * x = ∑ i : Fin n, y ^ (i : ℕ) * x * (c i).unop := by
    rw [← hc]
    apply Finset.sum_congr rfl
    intro i _
    rw [MulOpposite.smul_eq_mul_unop]
  exact hx (eq_zero_of_mem_span_shifted_powers hy hcon' n (fun i => (c i).unop) hc')

end RightOreOfRightNoetherian

/-! ## The iterated Ore tower is a right-Noetherian domain -/

section Tower

variable (k : Type u) [Field k]

/-- The recursively iterated Ore construction is transposed
right-Noetherian at every stage: `IsNoetherianRing (IteratedPairStage k n)ᵐᵒᵖ`.
Induction on `n`; the base case is the field `k`, the successor case adjoins
two derivation-Ore stages (`CoordinateStage` then `PairStage`) via
`derivationOre_rightHilbertBasis`, applied twice. -/
theorem iteratedPairStage_isNoetherianRing_op :
    ∀ n : ℕ, IsNoetherianRing (IteratedPairStage k n)ᵐᵒᵖ
  | 0 => (inferInstance : IsNoetherianRing kᵐᵒᵖ)
  | n + 1 =>
      have ih := iteratedPairStage_isNoetherianRing_op n
      have h1 : IsNoetherianRing (CoordinateStage (B := IteratedPairStage k n))ᵐᵒᵖ :=
        derivationOre_rightHilbertBasis ih zeroDerivation
      derivationOre_rightHilbertBasis h1 coordinateDerivation

/-- The recursively iterated Ore construction is a domain at every stage. -/
theorem iteratedPairStage_domain :
    ∀ n : ℕ, NoZeroDivisors (IteratedPairStage k n) ∧
      Nontrivial (IteratedPairStage k n)
  | 0 => ⟨(inferInstance : NoZeroDivisors k), (inferInstance : Nontrivial k)⟩
  | n + 1 => by
      obtain ⟨hz, hn⟩ := iteratedPairStage_domain n
      haveI := hz
      haveI := hn
      haveI hz1 : NoZeroDivisors (CoordinateStage (B := IteratedPairStage k n)) :=
        normalOreNoZeroDivisors (zeroDerivation (B := IteratedPairStage k n))
      haveI hn1 : Nontrivial (CoordinateStage (B := IteratedPairStage k n)) :=
        normalOreNontrivial (zeroDerivation (B := IteratedPairStage k n))
      exact ⟨normalOreNoZeroDivisors
          (coordinateDerivation (B := IteratedPairStage k n)),
        normalOreNontrivial (coordinateDerivation (B := IteratedPairStage k n))⟩

end Tower

/-! ## Transport to the presented Weyl algebra -/

variable (k : Type u) [Field k] (n : ℕ)

/-- The presented rank-`n` Weyl algebra has no zero divisors (`PLAN.md`
WP-15, route 2/fallback: leading-coefficient degree argument at every
`NormalOre` stage of the recursive tower, transported along
`presentedIteratedEquiv`). -/
instance instNoZeroDivisorsPresentedWeyl : NoZeroDivisors (PresentedWeyl k n) :=
  have hdomain := (iteratedPairStage_domain k n).1
  Function.Injective.noZeroDivisors (presentedIteratedEquiv k n)
    (presentedIteratedEquiv k n).injective (map_zero _) (map_mul _)

/-- The presented rank-`n` Weyl algebra is nontrivial. -/
instance instNontrivialPresentedWeyl : Nontrivial (PresentedWeyl k n) :=
  have hnontrivial := (iteratedPairStage_domain k n).2
  (presentedIteratedEquiv k n).toEquiv.nontrivial

/-- Right-Noetherianity of the presented rank-`n` Weyl algebra's opposite,
transported from the iterated Ore tower along `presentedIteratedEquiv`. -/
instance instIsNoetherianRingOpPresentedWeyl :
    IsNoetherianRing (PresentedWeyl k n)ᵐᵒᵖ :=
  have h := iteratedPairStage_isNoetherianRing_op k n
  isNoetherianRing_of_ringEquiv (IteratedPairStage k n)ᵐᵒᵖ
    (RingEquiv.op (presentedIteratedEquiv k n).toRingEquiv).symm

/-- The right Ore condition for the presented rank-`n` Weyl algebra
(`PLAN.md` WP-15, route 2): from right-Noetherianity of the opposite ring
and the domain property, via `rightOre_of_rightNoetherian_domain`. -/
theorem weyl_rightOre : ∀ x y : PresentedWeyl k n, x ≠ 0 → y ≠ 0 →
    ∃ a b : PresentedWeyl k n, a ≠ 0 ∧ x * a = y * b :=
  rightOre_of_rightNoetherian_domain

/-- Skolemized data for the `OreSet` instance below: for every `r` in the
opposite ring and every nonzero-divisor denominator `s`, a numerator `a` and
a nonzero denominator-witness `b` with `s.unop * a = r.unop * b`. The case
`r = 0` is trivial (`a = 0`, `b = 1`); otherwise `b ≠ 0` follows from
`a ≠ 0` (`weyl_rightOre`) together with the domain property. -/
private theorem exists_opOreWitness (r : (PresentedWeyl k n)ᵐᵒᵖ)
    (s : ((PresentedWeyl k n)ᵐᵒᵖ)⁰) :
    ∃ a b : PresentedWeyl k n, s.1.unop * a = r.unop * b ∧ b ≠ 0 := by
  by_cases hr : r = 0
  · refine ⟨0, 1, ?_, one_ne_zero⟩
    rw [mul_zero, hr, MulOpposite.unop_zero, zero_mul]
  · have hy : r.unop ≠ 0 := fun h =>
      hr (by rw [← MulOpposite.op_unop r, h, MulOpposite.op_zero])
    have hx0 : (s.1 : (PresentedWeyl k n)ᵐᵒᵖ) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp s.2
    have hx : s.1.unop ≠ 0 := fun h =>
      hx0 (by rw [← MulOpposite.op_unop s.1, h, MulOpposite.op_zero])
    obtain ⟨a, b, ha, hab⟩ := weyl_rightOre k n s.1.unop r.unop hx hy
    refine ⟨a, b, hab, fun hb0 => ?_⟩
    rw [hb0, mul_zero] at hab
    exact ha ((mul_eq_zero.mp hab).resolve_left hx)

/-- The right Ore condition on `T = PresentedWeyl k n`, packaged as an
`OreLocalization.OreSet` instance for `((PresentedWeyl k n)ᵐᵒᵖ)⁰`: the left
Ore condition in `(PresentedWeyl k n)ᵐᵒᵖ` is the right Ore condition in
`PresentedWeyl k n` (`weyl_rightOre`), and cancellability of nonzero
denominators is automatic in a domain (`OreLocalization.oreSetOfNoZeroDivisors`). -/
instance instOreSetPresentedWeylMop :
    OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰ := by
  choose oreNumFn oreDenomFn hEq hDenomNe using exists_opOreWitness k n
  refine OreLocalization.oreSetOfNoZeroDivisors
    (S := ((PresentedWeyl k n)ᵐᵒᵖ)⁰)
    (fun r s => MulOpposite.op (oreNumFn r s))
    (fun r s => ⟨MulOpposite.op (oreDenomFn r s),
      mem_nonZeroDivisors_of_ne_zero (fun h => hDenomNe r s (by
        simpa using congrArg MulOpposite.unop h))⟩)
    (fun r s => by
      apply MulOpposite.unop_injective
      simp only [MulOpposite.unop_mul, MulOpposite.unop_op]
      exact (hEq r s).symm)

/-- The Weyl-algebra two-generator identity (`Stafford38.universalStatement`),
restated as `AlgebraicAnalysis.TwoGeneratorIdentity` for the presented
rank-`n` Weyl algebra, for a sanity check of the WP-15 instances against a
literal consumer. -/
theorem twoGeneratorIdentity_presentedWeyl [CharZero k] :
    AlgebraicAnalysis.TwoGeneratorIdentity (PresentedWeyl k n) :=
  Stafford38.universalStatement k n

#print axioms instNoZeroDivisorsPresentedWeyl
#print axioms weyl_rightOre
#print axioms instOreSetPresentedWeylMop
#print axioms twoGeneratorIdentity_presentedWeyl

end
end GlobalStafford.Weyl
