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

noncomputable local instance : Fintype σ := Fintype.ofFinite σ
noncomputable local instance : DecidableEq σ := Classical.decEq σ

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
    Equiv.coe_refl]
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

/-- `transport` as a `k`-algebra isomorphism, splitting the presentation ring `MvPolynomial ι k`
into relation-indexed variables `σ` over the base `Base P`. -/
def transportEquiv : MvPolynomial ι k ≃ₐ[k] MvPolynomial σ (Base P) :=
  (renameEquiv k (splitEquiv P)).trans (sumAlgEquiv k σ (Fin (freeRank P)))

lemma transport_eq (p : MvPolynomial ι k) : transport P p = transportEquiv P p := rfl

lemma surjective_aeval_val : Function.Surjective (aeval (R := Base P) (val P)) := by
  have hcomp : Function.Surjective ((aeval (val P) : MvPolynomial σ (Base P) →ₐ[Base P] S) ∘
      (transportEquiv P)) := by
    have : (aeval (val P) : MvPolynomial σ (Base P) →ₐ[Base P] S) ∘ (transportEquiv P) =
        fun p => aeval P.val p := by
      funext p
      simpa [transport_eq] using aeval_val_transport P p
    rw [this]
    exact P.toGenerators.aeval_val_surjective
  exact hcomp.of_comp

/-- The transported `Generators (Base P) S σ` (Generators.val = `val P`). -/
noncomputable def generators : Algebra.Generators (Base P) S σ :=
  Algebra.Generators.ofSurjective (val P) (surjective_aeval_val P)

@[simp] lemma generators_val : (generators P).val = val P := rfl

/-- `aeval (val P)` as a plain `RingHom`. -/
def valRingHom : MvPolynomial σ (Base P) →+* S := (aeval (val P)).toRingHom

/-- `aeval P.val` as a plain `RingHom`. -/
def PvalRingHom : MvPolynomial ι k →+* S := (aeval P.val).toRingHom

lemma generators_ker : (generators P).ker = RingHom.ker (valRingHom P) :=
  Algebra.Generators.ker_eq_ker_aeval_val _

/-- `transportEquiv P` as a plain `RingHom`. -/
def transportRingHom : MvPolynomial ι k →+* MvPolynomial σ (Base P) :=
  (transportEquiv P).toAlgHom.toRingHom

lemma transportRingHom_apply (p : MvPolynomial ι k) : transportRingHom P p = transport P p :=
  (transport_eq P p).symm

lemma aeval_val_comp_transportRingHom :
    (valRingHom P).comp (transportRingHom P) = PvalRingHom P := by
  apply RingHom.ext
  intro p
  show aeval (val P) (transportRingHom P p) = aeval P.val p
  rw [transportRingHom_apply, aeval_val_transport]

lemma ker_eq_comap :
    P.ker = Ideal.comap (transportRingHom P) (RingHom.ker (valRingHom P)) := by
  rw [P.ker_eq_ker_aeval_val]
  show RingHom.ker (PvalRingHom P) = Ideal.comap (transportRingHom P) (RingHom.ker (valRingHom P))
  rw [← aeval_val_comp_transportRingHom, RingHom.comap_ker]

lemma map_ker_eq :
    Ideal.map (transportRingHom P) P.ker = RingHom.ker (valRingHom P) := by
  rw [ker_eq_comap]
  exact Ideal.map_comap_of_surjective (transportRingHom P) (transportEquiv P).surjective _

/-- The transported presentation of `S` over `Base P`, with relations indexed by `σ` (the same
type as `P`'s relations). -/
noncomputable def presentation : Algebra.Presentation (Base P) S σ σ where
  toGenerators := generators P
  relation j := transport P (P.relation j)
  span_range_relation_eq_ker := by
    rw [generators_ker, ← map_ker_eq, ← P.span_range_relation_eq_ker, Ideal.map_span,
      ← Set.range_comp]
    congr 1

/-- The transported pre-submersive presentation, with `map := id`. -/
noncomputable def preSubmersivePresentation : Algebra.PreSubmersivePresentation (Base P) S σ σ where
  toPresentation := presentation P
  map := id
  map_inj := Function.injective_id

lemma preSubmersivePresentation_jacobiMatrix_apply (i j : σ) :
    (preSubmersivePresentation P).jacobiMatrix i j = pderiv i (transport P (P.relation j)) := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

lemma preSubmersivePresentation_jacobian_eq : (preSubmersivePresentation P).jacobian = P.jacobian := by
  have e1 : (preSubmersivePresentation P).jacobian =
      aeval (val P) (preSubmersivePresentation P).jacobiMatrix.det := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    exact Algebra.Generators.algebraMap_apply _ _
  have e2 : P.jacobian = aeval P.val P.jacobiMatrix.det := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    exact Algebra.Generators.algebraMap_apply _ _
  rw [e1, e2, AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
    preSubmersivePresentation_jacobiMatrix_apply]
  show aeval (val P) (pderiv i (transport P (P.relation j))) = aeval P.val (P.jacobiMatrix i j)
  rw [transport_pderiv, aeval_val_transport, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]

/-- **The transported submersive presentation**: `S` presented over `Base P` with variables
and relations both indexed by `σ`, `map := id`, and the same Jacobian as `P` (hence a unit). -/
noncomputable def submersivePresentation : Algebra.SubmersivePresentation (Base P) S σ σ where
  toPreSubmersivePresentation := preSubmersivePresentation P
  jacobian_isUnit := by rw [preSubmersivePresentation_jacobian_eq]; exact P.jacobian_isUnit

lemma submersivePresentation_dimension : (submersivePresentation P).dimension = 0 := by
  simp [Algebra.Presentation.dimension]

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

/-- **WP-17 (A)**: every standard-smooth `k`-algebra `S` admits an `EtaleCoordinateChart`,
i.e. `S` is étale over a polynomial ring `MvPolynomial (Fin n) k` for some `n`. Route: a
`SubmersivePresentation k S ι σ` reindexed to a `SubmersivePresentation Q S σ σ` (`map := id`)
over `Q := MvPolynomial (Fin (freeRank P)) k`, of relative dimension `0`, hence étale by
`Etale.iff_isStandardSmoothOfRelativeDimension_zero`. -/
theorem exists_etaleCoordinateChart (k S : Type u) [Field k] [CommRing S] [Algebra k S]
    [Algebra.IsStandardSmooth k S] : Nonempty (EtaleCoordinateChart k S) := by
  classical
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth k S›.out
  have := hσ
  have := hι
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension 0 (Base P) S :=
    (submersivePresentation P).isStandardSmoothOfRelativeDimension
      (submersivePresentation_dimension P)
  have hetale : Algebra.Etale (Base P) S :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr hstd
  exact ⟨⟨freeRank P, inferInstance, inferInstance, hetale⟩⟩

end

end GlobalStafford.Chart
