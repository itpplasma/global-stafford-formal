import GlobalStafford.Chart.ScalarExtension
import GlobalStafford.Chart.EtaleDerivations
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Polynomial.Basic

/-!
# Construction of the scalar extension interface (WP-16)

`PLAN.md` §4, work package WP-16 (`Chart/ScalarExtensionConstruction.lean`). For an
étale chart `C` over `B = k[x_1,…,x_n]` this file constructs the
`ScalarExtensionInterface` of WP-9 for the scalar extension
`K := RatFunc k`, `t := RatFunc.X`, `CK := K ⊗[k] C`, `DK := D_K(CK)`.
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators
open scoped TensorProduct

noncomputable section

universe u

/-! ## 0. Generic commutator lemmas over an arbitrary base -/

section Generic

variable {F R : Type*} [CommRing F] [CommRing R] [Algebra F R]

/-- The commutator is additive in its scalar argument. -/
theorem commutator_add_right' (P : Module.End F R) (a b : R) :
    commutator P (a + b) = commutator P a + commutator P b := by
  ext z
  simp only [commutator_apply, LinearMap.add_apply, add_mul, map_add]
  ring

@[simp] theorem commutator_zero_right' (P : Module.End F R) :
    commutator P (0 : R) = 0 := by
  ext z; simp [commutator_apply]

/-- `algebraMap F (algebra F R)` is multiplication by the image scalar. -/
theorem algebraMap_eq_multiplicationD (c : F) :
    algebraMap F (algebra (k := F) (R := R)) c =
      GlobalStafford.Operators.multiplicationD (algebraMap F R c) := by
  apply Subtype.ext
  rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]
  ext x
  simp [GlobalStafford.Operators.multiplicationD, multiplication_apply, Algebra.smul_def]

end Generic

/-! ## 1. The scalar extension and the base change of operators -/

variable {k : Type u} [Field k] {C : Type u} [CommRing C] [Algebra k C]

/-- The scalar extension `C_K = K ⊗_k C` of the chart ring, `K = k(t)`. -/
abbrev CK (k : Type u) [Field k] (C : Type u) [CommRing C] [Algebra k C] : Type u :=
  RatFunc k ⊗[k] C

/-- The base change to `K = k(t)` of a `k`-linear endomorphism of `C`. -/
def baseChangeEnd (P : Module.End k C) : Module.End (RatFunc k) (CK k C) :=
  LinearMap.baseChange (RatFunc k) P

@[simp] theorem baseChangeEnd_tmul (P : Module.End k C) (κ : RatFunc k) (c : C) :
    baseChangeEnd P (κ ⊗ₜ[k] c) = κ ⊗ₜ[k] P c :=
  LinearMap.baseChange_tmul _ _ _

/-- Scalars of `K` act on pure tensors through the left factor. -/
@[simp] theorem smul_tmul_CK (κ μ : RatFunc k) (c : C) :
    κ • (μ ⊗ₜ[k] c : CK k C) = (κ * μ) ⊗ₜ[k] c := by
  rw [Algebra.smul_def]
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem baseChangeEnd_zero : baseChangeEnd (k := k) (C := C) 0 = 0 :=
  LinearMap.baseChange_zero

theorem baseChangeEnd_add (P Q : Module.End k C) :
    baseChangeEnd (k := k) (C := C) (P + Q) = baseChangeEnd P + baseChangeEnd Q :=
  LinearMap.baseChange_add _ _

theorem baseChangeEnd_one : baseChangeEnd (k := k) (C := C) 1 = 1 :=
  LinearMap.baseChange_one _ _

theorem baseChangeEnd_mul (P Q : Module.End k C) :
    baseChangeEnd (k := k) (C := C) (P * Q) = baseChangeEnd P * baseChangeEnd Q :=
  LinearMap.baseChange_mul _ _

/-- The commutator of a base-changed operator with a pure tensor. -/
theorem commutator_baseChangeEnd_tmul (P : Module.End k C) (κ : RatFunc k) (c : C) :
    commutator (baseChangeEnd (k := k) (C := C) P) (κ ⊗ₜ[k] c) =
      κ • baseChangeEnd (commutator P c) := by
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul μ d =>
      simp [commutator_apply, Algebra.TensorProduct.tmul_mul_tmul, smul_sub,
        TensorProduct.tmul_sub]
  | add y z hy hz =>
      simp only [commutator_apply, map_add, LinearMap.smul_apply] at hy hz ⊢
      rw [hy, hz]

/-- **Order preservation**: base change preserves the order filtration. -/
theorem baseChangeEnd_mem_order : ∀ (r : ℕ) (P : Module.End k C),
    P ∈ order (k := k) (R := C) r →
      baseChangeEnd (k := k) (C := C) P ∈ order (k := RatFunc k) (R := CK k C) r := by
  intro r
  induction r with
  | zero =>
      intro P hP
      rw [mem_order_zero_iff] at hP ⊢
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact commutator_zero_right' _
      | tmul κ c =>
          rw [commutator_baseChangeEnd_tmul, hP c, baseChangeEnd_zero, smul_zero]
      | add y z hy hz => rw [commutator_add_right', hy, hz, add_zero]
  | succ r IH =>
      intro P hP
      rw [mem_order_succ_iff] at hP ⊢
      intro y
      induction y using TensorProduct.induction_on with
      | zero => rw [commutator_zero_right']; exact Submodule.zero_mem _
      | tmul κ c =>
          rw [commutator_baseChangeEnd_tmul]
          exact Submodule.smul_mem _ κ (IH _ (hP c))
      | add y z hy hz =>
          rw [commutator_add_right']
          exact Submodule.add_mem _ hy hz

/-! ## 2. The scalar-extension ring homomorphism -/

/-- The operator ring of the scalar extension, `D_K(C_K)`. -/
abbrev DK (k : Type u) [Field k] (C : Type u) [CommRing C] [Algebra k C] :=
  algebra (k := RatFunc k) (R := CK k C)

/-- Base change of a finite-order operator, as an element of `D_K(C_K)`. -/
def baseChangeD (P : algebra (k := k) (R := C)) : DK k C :=
  ⟨baseChangeEnd (P : Module.End k C), by
    obtain ⟨r, hr⟩ := P.property
    exact ⟨r, baseChangeEnd_mem_order r _ hr⟩⟩

@[simp] theorem coe_baseChangeD (P : algebra (k := k) (R := C)) :
    (baseChangeD P : Module.End (RatFunc k) (CK k C)) = baseChangeEnd (P : Module.End k C) := rfl

/-- `Θ₀`: base change of operators, as a ring homomorphism `D_k(C) →+* D_K(C_K)`. -/
def bcHom : algebra (k := k) (R := C) →+* DK k C where
  toFun := baseChangeD
  map_one' := Subtype.ext (by rw [coe_baseChangeD, Subalgebra.coe_one, baseChangeEnd_one]; rfl)
  map_mul' P Q := Subtype.ext (by
    rw [coe_baseChangeD, Subalgebra.coe_mul, baseChangeEnd_mul]; rfl)
  map_zero' := Subtype.ext (by rw [coe_baseChangeD, Subalgebra.coe_zero, baseChangeEnd_zero]; rfl)
  map_add' P Q := Subtype.ext (by
    rw [coe_baseChangeD, Subalgebra.coe_add, baseChangeEnd_add]; rfl)

@[simp] theorem coe_bcHom (P : algebra (k := k) (R := C)) :
    ((bcHom P : DK k C) : Module.End (RatFunc k) (CK k C)) =
      baseChangeEnd (P : Module.End k C) := rfl

/-- Base change of a multiplication operator is multiplication by `1 ⊗ a`. -/
theorem baseChangeEnd_multiplication (a : C) :
    baseChangeEnd (k := k) (C := C) (multiplication a) =
      multiplication ((1 : RatFunc k) ⊗ₜ[k] a) := by
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul μ d => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem one_tmul_algebraMap (c : k) :
    (1 : RatFunc k) ⊗ₜ[k] (algebraMap k C c) = algebraMap k (CK k C) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
  rfl

/-- `Θ₀` is compatible with the base scalars. -/
theorem bcHom_algebraMap (c : k) :
    bcHom (k := k) (C := C) (algebraMap k (algebra (k := k) (R := C)) c) =
      algebraMap (RatFunc k) (DK k C) (algebraMap k (RatFunc k) c) := by
  apply Subtype.ext
  rw [coe_bcHom, algebraMap_eq_multiplicationD, GlobalStafford.Operators.coe_multiplicationD,
    baseChangeEnd_multiplication, one_tmul_algebraMap, algebraMap_eq_multiplicationD,
    GlobalStafford.Operators.coe_multiplicationD, ← IsScalarTower.algebraMap_apply k (RatFunc k)
      (CK k C) c]

/-- **`Θ`** (`PLAN.md` WP-16.3): the scalar-extension ring homomorphism
`D_k(C)[T] →+* D_K(C_K)`, sending `T` to the central scalar `t = RatFunc.X`. -/
def bigTheta : Polynomial (algebra (k := k) (R := C)) →+* DK k C :=
  Polynomial.eval₂RingHom' bcHom (algebraMap (RatFunc k) (DK k C) (RatFunc.X : RatFunc k))
    (fun P => (Algebra.commutes (RatFunc.X : RatFunc k) (bcHom P)).symm)

theorem bigTheta_apply (p : Polynomial (algebra (k := k) (R := C))) :
    bigTheta p = p.eval₂ bcHom (algebraMap (RatFunc k) (DK k C) (RatFunc.X : RatFunc k)) := rfl

@[simp] theorem bigTheta_C (P : algebra (k := k) (R := C)) :
    bigTheta (Polynomial.C P) = bcHom P := by
  rw [bigTheta_apply, Polynomial.eval₂_C]

@[simp] theorem bigTheta_X :
    bigTheta (k := k) (C := C) Polynomial.X =
      algebraMap (RatFunc k) (DK k C) (RatFunc.X : RatFunc k) := by
  rw [bigTheta_apply, Polynomial.eval₂_X]

/-- **`Θ_scalar`** (`PLAN.md` WP-16.3): `Θ` sends the scalar polynomial `scalarPoly h` to the
central element `algebraMap K DK (aeval t h)`. -/
theorem bigTheta_scalarPoly (h : Polynomial k) :
    bigTheta (GlobalStafford.Conjugation.scalarPoly (D := algebra (k := k) (R := C)) h) =
      algebraMap (RatFunc k) (DK k C)
        (Polynomial.aeval (RatFunc.X : RatFunc k) h) := by
  have hcomp : (bcHom (k := k) (C := C)).comp
      (algebraMap k (algebra (k := k) (R := C))) =
      (algebraMap (RatFunc k) (DK k C)).comp (algebraMap k (RatFunc k)) := by
    exact RingHom.ext fun c => bcHom_algebraMap (k := k) (C := C) c
  have hs : GlobalStafford.Conjugation.scalarPoly (D := algebra (k := k) (R := C)) h =
      h.map (algebraMap k (algebra (k := k) (R := C))) := rfl
  rw [hs, bigTheta_apply, Polynomial.eval₂_map, hcomp, Polynomial.aeval_def,
    Polynomial.hom_eval₂]

/-- **`aeval_ne_zero`** (`PLAN.md` WP-16.6): `t = RatFunc.X` is transcendental over `k`. -/
theorem aeval_X_ne_zero (h : Polynomial k) (hh : h ≠ 0) :
    Polynomial.aeval (RatFunc.X : RatFunc k) h ≠ 0 := by
  rw [RatFunc.aeval_X_left_eq_algebraMap]
  intro h0
  exact hh (RatFunc.algebraMap_injective k (by rw [h0, map_zero]))

/-! ## 3. Injectivity of `Θ` -/

/-- The powers of `t` are `k`-linearly independent in `C_K` in the strong sense that a finite
combination `∑ t^i ⊗ y i` vanishes only if every coefficient `y i` vanishes. The `k`-linear map
`k[X] → K`, `X ↦ t`, is injective, `C` is flat (indeed free) over the field `k`, so the base
change `k[X] ⊗ C → K ⊗ C` is injective; and `k[X] ⊗[k] C ≃ C[X]` (`polyEquivTensor`) reads off
the coefficients. -/
theorem eq_zero_of_sum_tmul_pow_eq_zero (s : Finset ℕ) (y : ℕ → C)
    (hy : ∑ i ∈ s, ((RatFunc.X : RatFunc k) ^ i) ⊗ₜ[k] y i = (0 : CK k C)) :
    ∀ i ∈ s, y i = 0 := by
  classical
  set f : Polynomial k →ₗ[k] RatFunc k :=
    (Polynomial.aeval (RatFunc.X : RatFunc k)).toLinearMap with hfdef
  have hfapp : ∀ a : Polynomial k, f a = algebraMap (Polynomial k) (RatFunc k) a := by
    intro a
    show Polynomial.aeval (RatFunc.X : RatFunc k) a = _
    rw [RatFunc.aeval_X_left_eq_algebraMap]
  have hfinj : Function.Injective f := by
    intro a b hab
    exact RatFunc.algebraMap_injective k (by rw [← hfapp, ← hfapp, hab])
  have hrinj : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hfinj
  have hmap : (f.rTensor C) (∑ i ∈ s, ((Polynomial.X : Polynomial k) ^ i) ⊗ₜ[k] y i) = 0 := by
    rw [map_sum, ← hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.rTensor_tmul]
    congr 1
    rw [hfapp, map_pow, RatFunc.algebraMap_X]
  have h0 : ∑ i ∈ s, ((Polynomial.X : Polynomial k) ^ i) ⊗ₜ[k] y i = 0 :=
    hrinj (by rw [hmap, map_zero])
  set Ψ : (Polynomial k) ⊗[k] C →ₗ[k] Polynomial C :=
    (polyEquivTensor k C).symm.toLinearMap ∘ₗ
      (TensorProduct.comm k (Polynomial k) C).toLinearMap with hΨdef
  have hΨ : ∀ (i : ℕ) (c : C),
      Ψ (((Polynomial.X : Polynomial k) ^ i) ⊗ₜ[k] c) = Polynomial.monomial i c := by
    intro i c
    show (polyEquivTensor k C).symm (c ⊗ₜ[k] ((Polynomial.X : Polynomial k) ^ i)) = _
    rw [polyEquivTensor_symm_apply_tmul_eq_smul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
  have hsum : ∑ i ∈ s, Polynomial.monomial i (y i) = (0 : Polynomial C) := by
    have hall := congrArg Ψ h0
    rw [map_sum, map_zero] at hall
    rw [← hall]
    exact Finset.sum_congr rfl fun i _ => (hΨ i (y i)).symm
  intro j hj
  have hcoeff := congrArg (fun q : Polynomial C => q.coeff j) hsum
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hcoeff
  rwa [Finset.sum_ite_eq' s j y, if_pos hj] at hcoeff

/-- The scalars of `K` inside `C_K`. -/
@[simp] theorem algebraMap_CK (κ : RatFunc k) :
    algebraMap (RatFunc k) (CK k C) κ = κ ⊗ₜ[k] (1 : C) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

/-- The scalars of `K` inside `D_K(C_K)` are the corresponding multiplication operators. -/
theorem coe_algebraMap_DK (κ : RatFunc k) :
    ((algebraMap (RatFunc k) (DK k C) κ : DK k C) : Module.End (RatFunc k) (CK k C)) =
      multiplication (algebraMap (RatFunc k) (CK k C) κ) := by
  rw [algebraMap_eq_multiplicationD, GlobalStafford.Operators.coe_multiplicationD]

/-- Value of `Θ p` on the pure tensor `1 ⊗ c`: it reads off the coefficients of `p`. -/
theorem bigTheta_apply_one_tmul (p : Polynomial (algebra (k := k) (R := C))) (c : C) :
    ((bigTheta p : DK k C) : Module.End (RatFunc k) (CK k C)) ((1 : RatFunc k) ⊗ₜ[k] c) =
      ∑ i ∈ p.support,
        ((RatFunc.X : RatFunc k) ^ i) ⊗ₜ[k] ((p.coeff i : Module.End k C) c) := by
  classical
  have hterm : ∀ i : ℕ,
      (((bcHom (p.coeff i) * algebraMap (RatFunc k) (DK k C) (RatFunc.X : RatFunc k) ^ i :
          DK k C)) : Module.End (RatFunc k) (CK k C)) ((1 : RatFunc k) ⊗ₜ[k] c) =
        ((RatFunc.X : RatFunc k) ^ i) ⊗ₜ[k] ((p.coeff i : Module.End k C) c) := by
    intro i
    rw [Subalgebra.coe_mul, ← map_pow, Module.End.mul_apply, coe_algebraMap_DK, coe_bcHom,
      multiplication_apply, algebraMap_CK, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      baseChangeEnd_tmul]
  rw [bigTheta_apply, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [show ((∑ i ∈ p.support, bcHom (p.coeff i) *
        algebraMap (RatFunc k) (DK k C) (RatFunc.X : RatFunc k) ^ i : DK k C) :
        Module.End (RatFunc k) (CK k C)) =
      ∑ i ∈ p.support, (((bcHom (p.coeff i) *
        algebraMap (RatFunc k) (DK k C) (RatFunc.X : RatFunc k) ^ i : DK k C)) :
        Module.End (RatFunc k) (CK k C)) from
      map_sum (DK k C).val _ _]
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hterm i

/-- `Θ` has trivial kernel. -/
theorem bigTheta_eq_zero (p : Polynomial (algebra (k := k) (R := C)))
    (hp : bigTheta p = 0) : p = 0 := by
  classical
  by_contra hne
  obtain ⟨j, hj⟩ : p.support.Nonempty := Polynomial.support_nonempty.mpr hne
  have hcoeff : ∀ c : C, (p.coeff j : Module.End k C) c = 0 := by
    intro c
    refine eq_zero_of_sum_tmul_pow_eq_zero (k := k) p.support
      (fun i => (p.coeff i : Module.End k C) c) ?_ j hj
    rw [← bigTheta_apply_one_tmul p c, hp]
    rfl
  exact (Polynomial.mem_support_iff.mp hj)
    (Subtype.ext (LinearMap.ext fun c => by rw [hcoeff c]; rfl))

/-- The same, summing over any finite set containing the support of `p`. -/
theorem bigTheta_apply_one_tmul' (p : Polynomial (algebra (k := k) (R := C))) (s : Finset ℕ)
    (hs : p.support ⊆ s) (c : C) :
    ((bigTheta p : DK k C) : Module.End (RatFunc k) (CK k C)) ((1 : RatFunc k) ⊗ₜ[k] c) =
      ∑ i ∈ s, ((RatFunc.X : RatFunc k) ^ i) ⊗ₜ[k] ((p.coeff i : Module.End k C) c) := by
  rw [bigTheta_apply_one_tmul]
  refine Finset.sum_subset hs fun i _ hi => ?_
  rw [Polynomial.notMem_support_iff.mp hi, Subalgebra.coe_zero, LinearMap.zero_apply,
    TensorProduct.tmul_zero]

/-- **`Θ_injective`** (`PLAN.md` WP-16.4): `Θ` is injective, because the powers `t^i` of the
scalar `t` are `k`-linearly independent in `K` and `C` is free over `k`. -/
theorem bigTheta_injective :
    Function.Injective (bigTheta (k := k) (C := C)) := by
  classical
  intro p q hpq
  refine Polynomial.ext fun i => Subtype.ext (LinearMap.ext fun c => ?_)
  set s : Finset ℕ := p.support ∪ q.support with hsdef
  have h1 := bigTheta_apply_one_tmul' p s Finset.subset_union_left c
  have h2 := bigTheta_apply_one_tmul' q s Finset.subset_union_right c
  have hsum : ∑ j ∈ s, ((RatFunc.X : RatFunc k) ^ j) ⊗ₜ[k]
      ((p.coeff j : Module.End k C) c - (q.coeff j : Module.End k C) c) = (0 : CK k C) := by
    simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib, ← h1, ← h2, hpq, sub_self]
  have hz := eq_zero_of_sum_tmul_pow_eq_zero (k := k) s _ hsum
  by_cases hi : i ∈ s
  · exact sub_eq_zero.mp (hz i hi)
  · have hp0 : p.coeff i = 0 :=
      Polynomial.notMem_support_iff.mp fun h => hi (Finset.mem_union_left _ h)
    have hq0 : q.coeff i = 0 :=
      Polynomial.notMem_support_iff.mp fun h => hi (Finset.mem_union_right _ h)
    rw [hp0, hq0]

end

end GlobalStafford.Chart
