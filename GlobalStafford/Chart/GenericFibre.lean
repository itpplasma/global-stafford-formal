import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite generic fibre (`PLAN.md` WP-13)

`PLAN.md` §4 work package WP-13 (`Chart/GenericFibre.lean`). Let `B = k[x_1,…,x_n]`
and let `C` be an integral domain, étale over `B`. This file proves:

* `algebraMap_injective_of_etale` : `B → C` is injective (`Algebra.Etale` gives
  `Module.Flat B C`, and flatness makes every nonzerodivisor of `B` act
  regularly on `C`).
* `algebraMap_ne_zero_of_etale` : the injectivity statement restated for
  nonzero elements, matching the `EtaleChartData.algebraMap_ne_zero` field.
* `finiteGenericFibre_of_etale` : the generic fibre `L ⊗[B] C` (`L := FractionRing B`)
  is a finite `L`-algebra (étale base change plus `Algebra.Etale.iff_exists_algEquiv_prod`),
  hence every `x : C` becomes, after clearing a nonzero coefficient of `B`, a finite
  `C`-linear combination of a fixed finite family `c : Fin m → C` with `B`-coefficients
  — matching the `EtaleChartData.finiteGenericFibre` field.
-/

namespace GlobalStafford.Chart

open scoped nonZeroDivisors TensorProduct

universe u

variable {k : Type u} [Field k] {n : ℕ} {C : Type u} [CommRing C] [IsDomain C] [Algebra k C]
  [Algebra (MvPolynomial (Fin n) k) C] [IsScalarTower k (MvPolynomial (Fin n) k) C]
  [Algebra.Etale (MvPolynomial (Fin n) k) C]

/-- The coordinate polynomial ring `k[x_1,…,x_n]`. -/
abbrev Bpoly : Type u := MvPolynomial (Fin n) k

/-- The fraction field of `B`. -/
abbrev L : Type u := FractionRing (Bpoly (k := k) (n := n))

/-- The generic fibre `L ⊗[B] C`. -/
abbrev CL : Type u := L (k := k) (n := n) ⊗[Bpoly (k := k) (n := n)] C

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `Algebra.Etale` gives `Module.Flat B C`, so a nonzero `b : B` acts regularly on `C`;
since `C` is nontrivial this forces `algebraMap B C` to be injective. -/
theorem algebraMap_injective_of_etale :
    Function.Injective (algebraMap (Bpoly (k := k) (n := n)) C) := by
  intro a a' h
  by_contra hne
  have hb0 : a - a' ≠ 0 := sub_ne_zero.mpr hne
  have hreg : IsSMulRegular C (a - a') :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_iff_ne_zero.mpr hb0)
  have hzero : algebraMap (Bpoly (k := k) (n := n)) C (a - a') = 0 := by
    rw [map_sub, h, sub_self]
  have h1 : (a - a') • (1 : C) = (a - a') • (0 : C) := by
    rw [Algebra.smul_def, Algebra.smul_def, hzero, zero_mul, zero_mul]
  exact one_ne_zero (hreg h1)

/-- Restatement of `algebraMap_injective_of_etale` for nonzero elements, matching the
`EtaleChartData.algebraMap_ne_zero` field. -/
theorem algebraMap_ne_zero_of_etale (b : Bpoly (k := k) (n := n)) (hb : b ≠ 0) :
    algebraMap (Bpoly (k := k) (n := n)) C b ≠ 0 := fun h0 =>
  hb (algebraMap_injective_of_etale (h0.trans (map_zero (algebraMap (Bpoly (k := k) (n := n)) C)).symm))

/-- **WP-13**: the generic fibre `C ⊗_B \operatorname{Frac}(B)` is finitely generated: every
`x : C` becomes a finite `C`-combination of finitely many fixed elements `c i`, after
clearing a nonzero coefficient of `B` on the left. -/
theorem finiteGenericFibre_of_etale :
    ∃ (m : ℕ) (c : Fin m → C), ∀ x : C, ∃ b : Bpoly (k := k) (n := n), b ≠ 0 ∧
      ∃ t : Fin m → Bpoly (k := k) (n := n),
        algebraMap (Bpoly (k := k) (n := n)) C b * x = ∑ i, c i * algebraMap (Bpoly (k := k) (n := n)) C (t i) := by
  classical
  -- `algebraMapSubmonoid C B⁰` consists of nonzerodivisors of `C`.
  have hsub : Algebra.algebraMapSubmonoid C (nonZeroDivisors (Bpoly (k := k) (n := n))) ≤
      nonZeroDivisors C := by
    rintro s ⟨b, hb, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (algebraMap_ne_zero_of_etale b (mem_nonZeroDivisors_iff_ne_zero.mp hb))
  -- `CL` is the localization of `C` at that submonoid (pushout comparison).
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors (Bpoly (k := k) (n := n))))
      (CL (k := k) (n := n) (C := C)) :=
    (Algebra.isLocalization_iff_isPushout (R := Bpoly (k := k) (n := n))
      (S := nonZeroDivisors (Bpoly (k := k) (n := n))) (A := L (k := k) (n := n))
      (T := C) (B := CL (k := k) (n := n) (C := C))).mpr inferInstance
  haveI hdomCL : IsDomain (CL (k := k) (n := n) (C := C)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (CL (k := k) (n := n) (C := C)) hsub
  haveI hinjCtoCL : Function.Injective (algebraMap C (CL (k := k) (n := n) (C := C))) :=
    IsLocalization.injective (CL (k := k) (n := n) (C := C)) hsub
  -- `CL` is étale, hence finite, over `L`.
  obtain ⟨I, hI, Ai, hAiField, hAiAlg, e, hAifin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (L (k := k) (n := n))
      (CL (k := k) (n := n) (C := C))).mp inferInstance
  letI := hI
  letI := hAiField
  letI := hAiAlg
  letI := fun i => (hAifin i).1
  haveI hCLfin : Module.Finite (L (k := k) (n := n)) (CL (k := k) (n := n) (C := C)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  -- A finite spanning family of `CL` over `L`.
  obtain ⟨m', g, hg⟩ := Module.Finite.exists_fin (R := L (k := k) (n := n))
    (M := CL (k := k) (n := n) (C := C))
  set S := Algebra.algebraMapSubmonoid C (nonZeroDivisors (Bpoly (k := k) (n := n))) with hS
  -- Numerators and denominators of the spanning family, via `IsLocalization.sec`.
  set numer : Fin m' → C := fun j => (IsLocalization.sec S (g j)).1 with hnumer
  set denom : Fin m' → S := fun j => (IsLocalization.sec S (g j)).2 with hdenom
  have hspec : ∀ j, algebraMap C (CL (k := k) (n := n) (C := C)) (denom j : C) * g j =
      algebraMap C (CL (k := k) (n := n) (C := C)) (numer j) := by
    intro j
    have := IsLocalization.mk'_spec' (CL (k := k) (n := n) (C := C)) (numer j) (denom j)
    rwa [IsLocalization.mk'_sec (CL (k := k) (n := n) (C := C)) (g j)] at this
  -- Each denominator is the image of a nonzero element `denomB j : B`.
  choose denomB hdenomB hdenomBeq using fun j => (denom j).2
  -- `denom j` becomes, in `L`, a unit `algebraMap B L (denomB j)`.
  have hunit : ∀ j, IsUnit (algebraMap (Bpoly (k := k) (n := n)) (L (k := k) (n := n)) (denomB j)) :=
    fun j => IsLocalization.map_units (L (k := k) (n := n)) (⟨denomB j, hdenomB j⟩ :
      nonZeroDivisors (Bpoly (k := k) (n := n)))
  have hCLdenom : ∀ j, algebraMap C (CL (k := k) (n := n) (C := C)) (denom j : C) =
      algebraMap (L (k := k) (n := n)) (CL (k := k) (n := n) (C := C))
        (algebraMap (Bpoly (k := k) (n := n)) (L (k := k) (n := n)) (denomB j)) := by
    intro j
    rw [← hdenomBeq j, ← IsScalarTower.algebraMap_apply (Bpoly (k := k) (n := n)) C
        (CL (k := k) (n := n) (C := C)),
      IsScalarTower.algebraMap_apply (Bpoly (k := k) (n := n)) (L (k := k) (n := n))
        (CL (k := k) (n := n) (C := C))]
  -- Hence `g j` is an `L`-scalar multiple of `algebraMap C CL (numer j)`.
  have hgmem : ∀ j, g j ∈ Submodule.span (L (k := k) (n := n))
      (Set.range (fun j => algebraMap C (CL (k := k) (n := n) (C := C)) (numer j))) := by
    intro j
    have hβ : (algebraMap (Bpoly (k := k) (n := n)) (L (k := k) (n := n)) (denomB j)) • g j =
        algebraMap C (CL (k := k) (n := n) (C := C)) (numer j) := by
      rw [Algebra.smul_def (algebraMap (Bpoly (k := k) (n := n)) (L (k := k) (n := n)) (denomB j))
        (g j), ← hCLdenom j]
      exact hspec j
    set u := (hunit j).unit with hu
    have hguβ : (u : L (k := k) (n := n)) • g j = algebraMap C (CL (k := k) (n := n) (C := C))
        (numer j) := hβ
    have : g j = (↑u⁻¹ : L (k := k) (n := n)) •
        algebraMap C (CL (k := k) (n := n) (C := C)) (numer j) := by
      rw [← hguβ, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  have hrange : Set.range g ⊆
      (Submodule.span (L (k := k) (n := n))
        (Set.range (fun j => algebraMap C (CL (k := k) (n := n) (C := C)) (numer j))) :
        Submodule (L (k := k) (n := n)) (CL (k := k) (n := n) (C := C))) := by
    rintro _ ⟨j, rfl⟩; exact hgmem j
  have htop : Submodule.span (L (k := k) (n := n))
      (Set.range (fun j => algebraMap C (CL (k := k) (n := n) (C := C)) (numer j))) = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Submodule (L (k := k) (n := n)) (CL (k := k) (n := n) (C := C)))
        = Submodule.span (L (k := k) (n := n)) (Set.range g) := hg.symm
      _ ≤ _ := Submodule.span_le.mpr hrange
  -- Present the given `x : C` via the spanning family, over `L`.
  refine ⟨m', numer, fun x => ?_⟩
  have hxmem : algebraMap C (CL (k := k) (n := n) (C := C)) x ∈
      Submodule.span (L (k := k) (n := n))
        (Set.range (fun j => algebraMap C (CL (k := k) (n := n) (C := C)) (numer j))) := by
    rw [htop]; trivial
  obtain ⟨lam, hlam⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (L (k := k) (n := n))).mp hxmem
  -- Clear the denominators of the finitely many coefficients `lam j`.
  obtain ⟨bdiv, hbdiv⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Bpoly (k := k) (n := n))) lam
  choose t ht using hbdiv
  refine ⟨(bdiv : Bpoly (k := k) (n := n)), nonZeroDivisors.ne_zero bdiv.2, t, ?_⟩
  apply hinjCtoCL
  have hlhs : algebraMap C (CL (k := k) (n := n) (C := C))
      (algebraMap (Bpoly (k := k) (n := n)) C (bdiv : Bpoly (k := k) (n := n)) * x) =
      (bdiv : Bpoly (k := k) (n := n)) • algebraMap C (CL (k := k) (n := n) (C := C)) x := by
    rw [Algebra.smul_def (bdiv : Bpoly (k := k) (n := n))
        (algebraMap C (CL (k := k) (n := n) (C := C)) x),
      map_mul,
      ← IsScalarTower.algebraMap_apply (Bpoly (k := k) (n := n)) C
        (CL (k := k) (n := n) (C := C)) (bdiv : Bpoly (k := k) (n := n))]
  rw [map_sum]
  have hrhs : ∀ j, algebraMap C (CL (k := k) (n := n) (C := C))
      (numer j * algebraMap (Bpoly (k := k) (n := n)) C (t j)) =
      ((bdiv : Bpoly (k := k) (n := n)) • lam j) • algebraMap C (CL (k := k) (n := n) (C := C))
        (numer j) := by
    intro j
    rw [mul_comm, map_mul,
      ← IsScalarTower.algebraMap_apply (Bpoly (k := k) (n := n)) C
        (CL (k := k) (n := n) (C := C)) (t j),
      IsScalarTower.algebraMap_apply (Bpoly (k := k) (n := n)) (L (k := k) (n := n))
        (CL (k := k) (n := n) (C := C)) (t j),
      ht j,
      ← Algebra.smul_def ((bdiv : Bpoly (k := k) (n := n)) • lam j)
        (algebraMap C (CL (k := k) (n := n) (C := C)) (numer j))]
  simp only [hrhs]
  rw [hlhs, ← hlam, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (smul_assoc (bdiv : Bpoly (k := k) (n := n)) (lam j)
    (algebraMap C (CL (k := k) (n := n) (C := C)) (numer j))).symm

#print axioms GlobalStafford.Chart.algebraMap_injective_of_etale
#print axioms GlobalStafford.Chart.algebraMap_ne_zero_of_etale
#print axioms GlobalStafford.Chart.finiteGenericFibre_of_etale

end GlobalStafford.Chart
