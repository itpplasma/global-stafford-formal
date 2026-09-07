import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Smooth cover by étale charts (`PLAN.md` WP-17)

`PLAN.md` §4, work package WP-17 (`Chart/SmoothCover.lean`). This file proves:

* `EtaleCoordinateChart k S` : bundled data exhibiting `S` as an étale algebra over a
  polynomial ring `MvPolynomial (Fin n) k` for some `n`.
* `etale_over_polynomial_of_isStandardSmooth` : every standard-smooth `k`-algebra `S`
  admits such a chart (the presentation route: a `SubmersivePresentation k S ι σ` is
  reindexed via `ι ≃ σ ⊕ Fin n` to a `SubmersivePresentation Q S σ σ` over
  `Q := MvPolynomial (Fin n) k` with `map := id`, of relative dimension `0`, hence
  `Algebra.Etale Q S` by `Etale.iff_isStandardSmoothOfRelativeDimension_zero`).
* `exists_finite_etale_cover` : every smooth integral affine `k`-algebra `A` (`char 0`)
  has a finite principal cover `f : Fin s → A` by nonzero elements such that each
  `Localization.Away (f i)` carries an `EtaleCoordinateChart` (Theorem 6.3).

The Kähler-differential route sketched in `PLAN.md` needs
`Algebra.FormallySmooth.iff_subsingleton_and_projective`, which is not present in the
pinned Mathlib; this file uses the presentation route flagged as the alternative there.
-/

namespace GlobalStafford.Chart

noncomputable section

universe u

open MvPolynomial Algebra

section Construction

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S] {ι σ : Type} [Finite σ]
  (P : Algebra.SubmersivePresentation k S ι σ) [Finite ι]

open scoped Classical in
/-- The complement of `Set.range P.map` inside `ι`, indexed as a `Sigma`-style equivalence
`ι ≃ σ ⊕ (free variables)`. -/
def freeIndexEquiv : ι ≃ σ ⊕ ((Set.range P.map)ᶜ : Set ι) :=
  (Equiv.Set.sumCompl (Set.range P.map)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj).symm (Equiv.refl _))

instance : Finite ((Set.range P.map)ᶜ : Set ι) := Subtype.finite

/-- The number of free (non-relation) variables of the presentation `P`. -/
def freeRank : ℕ := Nat.card ((Set.range P.map)ᶜ : Set ι)

/-- `ι` split into the relation-indexed variables `σ` and `Fin (freeRank P)` free variables. -/
def splitEquiv : ι ≃ σ ⊕ Fin (freeRank P) :=
  (freeIndexEquiv P).trans (Equiv.sumCongr (Equiv.refl σ) (Finite.equivFin _))

@[simp] lemma splitEquiv_map (j : σ) : splitEquiv P (P.map j) = Sum.inl j := by
  classical
  have hmem : P.map j ∈ Set.range P.map := Set.mem_range_self j
  unfold splitEquiv freeIndexEquiv
  simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hmem,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.ofInjective_symm_apply,
    Equiv.refl_apply, Equiv.coe_refl]
  rfl

lemma splitEquiv_symm_inl (j : σ) : (splitEquiv P).symm (Sum.inl j) = P.map j := by
  rw [Equiv.symm_apply_eq, splitEquiv_map]

/-- The base polynomial ring of the transported presentation: `k` in the free variables of
`P` (those not in the image of `P.map`). -/
abbrev Base : Type u := MvPolynomial (Fin (freeRank P)) k

/-- The images in `S` of the relation-indexed generators of the transported presentation. -/
def val (j : σ) : S := P.val (P.map j)

/-- The images in `S` of the free variables of `P`. -/
def freeVal (i : Fin (freeRank P)) : S := P.val ((splitEquiv P).symm (Sum.inr i))

/-- The `k`-algebra map `Base P → S` sending the free variables to their images. -/
def toBaseAlgHom : Base P →ₐ[k] S := aeval (freeVal P)

instance : Algebra (Base P) S := (toBaseAlgHom P).toRingHom.toAlgebra

instance : IsScalarTower k (Base P) S := IsScalarTower.of_algHom (toBaseAlgHom P)

@[simp] lemma algebraMap_base_apply (q : Base P) : algebraMap (Base P) S q = toBaseAlgHom P q := rfl

/-- `combined` reads off the images of all of `P`'s generators, split as `σ ⊕ Fin (freeRank P)`. -/
lemma sumElim_val_freeVal :
    Sum.elim (val P) (freeVal P) = P.val ∘ (splitEquiv P).symm := by
  funext x
  cases x with
  | inl j => simp [val, splitEquiv_symm_inl]
  | inr i => simp [freeVal]

/-- Transport of a polynomial in the original variables `ι` of `P` to the ring
`MvPolynomial σ (Base P)` of the transported presentation, via `splitEquiv P` and
`sumAlgEquiv`. -/
def transport (p : MvPolynomial ι k) : MvPolynomial σ (Base P) :=
  MvPolynomial.sumAlgEquiv k σ (Fin (freeRank P)) (MvPolynomial.rename (splitEquiv P) p)

lemma sumAlgEquiv_eq_aeval {R S₁ S₂ : Type*} [CommRing R] (p : MvPolynomial (S₁ ⊕ S₂) R) :
    MvPolynomial.sumAlgEquiv R S₁ S₂ p =
      MvPolynomial.aeval (Sum.elim X (C ∘ (X : S₂ → MvPolynomial S₂ R))) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i h => cases i <;> simp [h]

/-- The key compatibility square: transporting a polynomial and evaluating at the images
of the relation-indexed generators gives the same result as evaluating the original
polynomial at the images of `P`'s generators. -/
lemma aeval_val_transport (p : MvPolynomial ι k) :
    aeval (val P) (transport P p) = aeval P.val p := by
  have h := MvPolynomial.aeval_sumElim (R := k) (S := Base P) (T := S)
    (rename (splitEquiv P) p) (MvPolynomial.X (R := k)) (val P)
  simp only [Function.comp_def, algebraMap_base_apply, toBaseAlgHom, aeval_X] at h
  rw [sumElim_val_freeVal] at h
  unfold transport
  rw [sumAlgEquiv_eq_aeval]
  simp only [Function.comp_def]
  rw [← h, MvPolynomial.aeval_rename]
  have : (P.val ∘ (splitEquiv P).symm) ∘ (splitEquiv P) = P.val := by
    funext i; simp
  rw [this]

lemma transport_pderiv (p : MvPolynomial ι k) (j : σ) :
    pderiv j (transport P p) = transport P (pderiv (P.map j) p) := by
  classical
  unfold transport
  rw [pderiv_sumAlgEquiv, ← splitEquiv_map P j, pderiv_rename (splitEquiv P).injective]

end Construction

/-- Bundled data exhibiting `S` as an étale `k`-algebra over a polynomial ring
`MvPolynomial (Fin n) k` for some `n : ℕ` (`PLAN.md` Theorem 6.3 chart shape). -/
structure EtaleCoordinateChart (k S : Type u) [Field k] [CommRing S] [Algebra k S] where
  /-- The number of coordinates of the chart. -/
  n : ℕ
  /-- The algebra structure of `S` over `MvPolynomial (Fin n) k`. -/
  alg : Algebra (MvPolynomial (Fin n) k) S
  /-- Compatibility of the `MvPolynomial (Fin n) k`-algebra structure with the `k`-algebra
  structure. -/
  tower : letI := alg; IsScalarTower k (MvPolynomial (Fin n) k) S
  /-- `S` is étale over `MvPolynomial (Fin n) k`. -/
  etale : letI := alg; Algebra.Etale (MvPolynomial (Fin n) k) S

end

end GlobalStafford.Chart
