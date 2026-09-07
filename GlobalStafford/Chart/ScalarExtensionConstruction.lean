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

/-! ## 4. Base change of derivations -/

/-- Leibniz rule for the base change of a derivation. -/
theorem baseChangeEnd_leibniz (δ : Derivation k C C) (a b : CK k C) :
    baseChangeEnd δ.toLinearMap (a * b) =
      a * baseChangeEnd δ.toLinearMap b + b * baseChangeEnd δ.toLinearMap a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul κ c =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul μ d =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, baseChangeEnd_tmul, baseChangeEnd_tmul,
            baseChangeEnd_tmul]
          show (κ * μ) ⊗ₜ[k] (δ (c * d)) =
            (κ ⊗ₜ[k] c) * (μ ⊗ₜ[k] (δ d)) + (μ ⊗ₜ[k] d) * (κ ⊗ₜ[k] (δ c))
          rw [δ.leibniz, Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul, smul_eq_mul, TensorProduct.tmul_add,
            mul_comm μ κ]
      | add b₁ b₂ h₁ h₂ =>
          rw [mul_add, map_add, h₁, h₂, map_add, mul_add, add_mul]
          abel
  | add a₁ a₂ h₁ h₂ =>
      rw [add_mul, map_add, h₁, h₂, map_add, add_mul, mul_add]
      abel

/-- The base change to `K` of a `k`-derivation of `C`, as a `K`-derivation of `C_K`. -/
def baseChangeDerivation (δ : Derivation k C C) : Derivation (RatFunc k) (CK k C) (CK k C) where
  toLinearMap := baseChangeEnd δ.toLinearMap
  map_one_eq_zero' := by
    show baseChangeEnd δ.toLinearMap (1 : CK k C) = 0
    rw [Algebra.TensorProduct.one_def, baseChangeEnd_tmul]
    show (1 : RatFunc k) ⊗ₜ[k] (δ 1) = 0
    rw [δ.map_one_eq_zero, TensorProduct.tmul_zero]
  leibniz' a b := by
    simpa only [smul_eq_mul] using baseChangeEnd_leibniz δ a b

@[simp] theorem baseChangeDerivation_tmul (δ : Derivation k C C) (κ : RatFunc k) (c : C) :
    baseChangeDerivation δ (κ ⊗ₜ[k] c) = κ ⊗ₜ[k] (δ c) := rfl

@[simp] theorem coe_baseChangeDerivation (δ : Derivation k C C) :
    (baseChangeDerivation δ).toLinearMap = baseChangeEnd δ.toLinearMap := rfl

/-! ## 5. Contractions along `k`-linear functionals of `K` -/

/-- Contraction of `C_K = K ⊗_k C` along a `k`-linear functional of `K`. -/
def contract (φ : RatFunc k →ₗ[k] k) : CK k C →ₗ[k] C :=
  (TensorProduct.lid k C).toLinearMap ∘ₗ LinearMap.rTensor C φ

@[simp] theorem contract_tmul (φ : RatFunc k →ₗ[k] k) (κ : RatFunc k) (c : C) :
    contract φ (κ ⊗ₜ[k] c) = φ κ • c := rfl

/-- Contraction is `C`-linear for the right tensor factor. -/
theorem contract_one_tmul_mul (φ : RatFunc k →ₗ[k] k) (c : C) (z : CK k C) :
    contract φ (((1 : RatFunc k) ⊗ₜ[k] c) * z) = c * contract φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul μ d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, contract_tmul, contract_tmul,
        mul_smul_comm]
  | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]

/-- The contractions separate the points of `C_K`: a `K`-basis of `C_K` obtained by base change
from a `k`-basis of `C` has coordinates that are detected by the functionals of `K`. -/
theorem eq_zero_of_forall_contract (y : CK k C)
    (h : ∀ φ : RatFunc k →ₗ[k] k, contract φ y = 0) : y = 0 := by
  classical
  set bC := Module.Basis.ofVectorSpace k C with hbC
  set b := bC.baseChange (RatFunc k) with hb
  have hy : ∑ i ∈ (b.repr y).support, (b.repr y i) • b i = y := by
    conv_rhs => rw [← b.linearCombination_repr y]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hzero : ∀ i ∈ (b.repr y).support, b.repr y i = 0 := by
    intro i hi
    rw [← Module.forall_dual_apply_eq_zero_iff k (b.repr y i)]
    intro φ
    have hcy : contract (C := C) φ y =
        ∑ j ∈ (b.repr y).support, φ (b.repr y j) • bC j := by
      conv_lhs => rw [← hy]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hbj : (b.repr y j) • b j = (b.repr y j) ⊗ₜ[k] bC j := by
        rw [hb, Module.Basis.baseChange_apply, smul_tmul_CK, mul_one]
      rw [hbj, contract_tmul]
    rw [h φ] at hcy
    exact linearIndependent_iff'.mp bC.linearIndependent _ _ hcy.symm i hi
  conv_lhs => rw [← hy]
  exact Finset.sum_eq_zero fun i hi => by rw [hzero i hi, zero_smul]

/-- Contracting a `K`-derivation of `C_K` along a functional of `K` gives a `k`-derivation
of `C`. -/
def contractDerivation (φ : RatFunc k →ₗ[k] k)
    (δ : Derivation (RatFunc k) (CK k C) (CK k C)) : Derivation k C C where
  toLinearMap :=
    { toFun := fun c => contract φ (δ ((1 : RatFunc k) ⊗ₜ[k] c))
      map_add' := fun c c' => by
        show contract φ (δ ((1 : RatFunc k) ⊗ₜ[k] (c + c'))) = _
        rw [TensorProduct.tmul_add, map_add, map_add]
      map_smul' := fun a c => by
        show contract φ (δ ((1 : RatFunc k) ⊗ₜ[k] (a • c))) = a • _
        rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul (RatFunc k) a,
          δ.map_smul, IsScalarTower.algebraMap_smul, map_smul] }
  map_one_eq_zero' := by
    show contract φ (δ ((1 : RatFunc k) ⊗ₜ[k] (1 : C))) = 0
    rw [← Algebra.TensorProduct.one_def, δ.map_one_eq_zero, map_zero]
  leibniz' := fun a b => by
    show contract φ (δ ((1 : RatFunc k) ⊗ₜ[k] (a * b))) = a • _ + b • _
    have h1 : (1 : RatFunc k) ⊗ₜ[k] (a * b) =
        ((1 : RatFunc k) ⊗ₜ[k] a) * ((1 : RatFunc k) ⊗ₜ[k] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [h1, δ.leibniz, smul_eq_mul, smul_eq_mul, map_add, contract_one_tmul_mul,
      contract_one_tmul_mul, smul_eq_mul, smul_eq_mul]
    rfl

@[simp] theorem contractDerivation_apply (φ : RatFunc k →ₗ[k] k)
    (δ : Derivation (RatFunc k) (CK k C) (CK k C)) (c : C) :
    contractDerivation φ δ c = contract φ (δ ((1 : RatFunc k) ⊗ₜ[k] c)) := rfl

/-! ## 6. Coordinate rigidity over `K` -/

variable [CharZero k] {n : ℕ} [Algebra (B k n) C] [IsScalarTower k (B k n) C]
  [Algebra.FormallyEtale (B k n) C]

/-- The image of the coordinate `x_i` in `C_K`. -/
def xCK (k : Type u) [Field k] (n : ℕ) (C : Type u) [CommRing C] [Algebra k C]
    [Algebra (B k n) C] (i : Fin n) : CK k C :=
  (1 : RatFunc k) ⊗ₜ[k] xC k n C i

/-- **Derivation rigidity over `K`**: a `K`-derivation of `C_K` killing every coordinate is
zero. Contracting along the `k`-linear functionals of `K` reduces this to the corresponding
statement over `k`, `derivation_eq_zero_of_algebraMap`, which holds because `C` is formally
étale over `B = k[x_1,…,x_n]`. -/
theorem derivationK_eq_zero_of_coord (δ : Derivation (RatFunc k) (CK k C) (CK k C))
    (hx : ∀ i, δ (xCK k n C i) = 0) : δ = 0 := by
  have hcontract : ∀ (φ : RatFunc k →ₗ[k] k) (c : C),
      contract φ (δ ((1 : RatFunc k) ⊗ₜ[k] c)) = 0 := by
    intro φ
    have hzero : contractDerivation φ δ = 0 := by
      refine derivation_eq_zero_of_algebraMap (k := k) (n := n) (C := C) _ ?_
      intro b
      induction b using MvPolynomial.induction_on with
      | C c =>
          have hcB : algebraMap (B k n) C (MvPolynomial.C c) = algebraMap k C c := by
            calc
              algebraMap (B k n) C (MvPolynomial.C c)
                  = algebraMap (B k n) C (algebraMap k (B k n) c) := by
                    rw [MvPolynomial.algebraMap_eq]
              _ = algebraMap k C c := (IsScalarTower.algebraMap_apply k (B k n) C c).symm
          rw [hcB, Derivation.map_algebraMap]
      | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
      | mul_X f i hf =>
          have hmulX : algebraMap (B k n) C (f * MvPolynomial.X i) =
              algebraMap (B k n) C f * xC k n C i := by
            rw [map_mul]; rfl
          have hxi : contractDerivation φ δ (xC k n C i) = 0 := by
            rw [contractDerivation_apply]
            show contract φ (δ (xCK k n C i)) = 0
            rw [hx i, map_zero]
          rw [hmulX, Derivation.leibniz, hf, hxi, smul_zero, smul_zero, add_zero]
    intro c
    have := DFunLike.congr_fun hzero c
    simpa using this
  have hone : ∀ c : C, δ ((1 : RatFunc k) ⊗ₜ[k] c) = 0 := fun c =>
    eq_zero_of_forall_contract _ fun φ => hcontract φ c
  refine Derivation.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul κ c =>
      have hk : (κ ⊗ₜ[k] c : CK k C) = κ • ((1 : RatFunc k) ⊗ₜ[k] c) := by
        rw [smul_tmul_CK, mul_one]
      rw [hk, δ.map_smul, hone c, smul_zero]
      rfl
  | add y z hy hz =>
      rw [map_add, hy, hz]
      simp

section GenericRigidity

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]

theorem commutator_mul_right' (P : Module.End F R) (a b : R) :
    commutator P (a * b) =
      commutator P a * multiplication b + multiplication a * commutator P b := by
  ext z
  simp only [commutator_apply, Module.End.mul_apply, multiplication_apply, LinearMap.add_apply]
  ring_nf

theorem commutator_commutator_comm' (P : Module.End F R) (c x : R) :
    commutator (commutator P c) x = commutator (commutator P x) c := by
  ext z
  simp only [commutator_apply]
  ring_nf

theorem commutator_zero_left' (a : R) : commutator (0 : Module.End F R) a = 0 := by
  ext z; simp [commutator_apply]

/-- **Coordinate rigidity from derivation rigidity**: if the only `F`-derivation of `R` killing
all the coordinates `x i` is zero, then a finite-order operator commuting with every coordinate
is a multiplication operator. This is the generic form of `coordinateRigidity`
(`Chart/EtaleDerivations.lean`), with the étale input isolated in the hypothesis `hder`. -/
theorem coordinateRigidity_of_derivations {m : ℕ} (x : Fin m → R)
    (hder : ∀ δ : Derivation F R R, (∀ i, δ (x i) = 0) → δ = 0) :
    ∀ (r : ℕ) (P : Module.End F R), P ∈ order (k := F) (R := R) r →
      (∀ i, commutator P (x i) = 0) → P = multiplication (P 1) := by
  intro r
  induction r with
  | zero =>
      intro P hP _
      exact (mem_order_zero_iff_eq_multiplication P).mp hP
  | succ r IH =>
      intro P hPm hcomm
      set μ : R → R := fun c => P c - c * P 1 with hμdef
      have hrep : ∀ c : R, commutator P c = multiplication (μ c) := by
        intro c
        have hQorder : commutator P c ∈ order (k := F) (R := R) r := hPm c
        have hQcomm : ∀ i, commutator (commutator P c) (x i) = 0 := by
          intro i
          rw [commutator_commutator_comm', hcomm i, commutator_zero_left']
        have hQeq := IH (commutator P c) hQorder hQcomm
        rw [hQeq]
        congr 1
        show P (c * 1) - c * P 1 = μ c
        rw [mul_one]
      have hμadd : ∀ a b, μ (a + b) = μ a + μ b := by
        intro a b; simp only [hμdef, map_add, add_mul]; ring
      have hμsmul : ∀ (s : F) (a : R), μ (s • a) = s • μ a := by
        intro s a; simp only [hμdef, P.map_smul, smul_mul_assoc, smul_sub]
      have hμone : μ 1 = 0 := by simp [hμdef]
      have hμleibniz : ∀ a b : R, μ (a * b) = a • μ b + b • μ a := by
        intro a b
        have e1 := hrep (a * b)
        have e2 := commutator_mul_right' P a b
        rw [e1] at e2
        have e3 := congrArg (fun T : Module.End F R => T 1) e2
        simp only [multiplication_apply, mul_one, LinearMap.add_apply, Module.End.mul_apply] at e3
        rw [hrep a, hrep b] at e3
        simp only [multiplication_apply] at e3
        rw [e3, smul_eq_mul, smul_eq_mul]
        ring
      let μL : R →ₗ[F] R :=
        { toFun := μ, map_add' := hμadd, map_smul' := by intro s a; simpa using hμsmul s a }
      let μD : Derivation F R R :=
        { toLinearMap := μL, map_one_eq_zero' := hμone, leibniz' := hμleibniz }
      have hμcoord : ∀ i, μD (x i) = 0 := by
        intro i
        show μ (x i) = 0
        have h0 : multiplication (k := F) (μ (x i)) = (0 : Module.End F R) := by
          rw [← hrep (x i), hcomm i]
        have h1 := congrArg (fun T : Module.End F R => T 1) h0
        simpa [multiplication_apply] using h1
      have hμDzero : μD = 0 := hder μD hμcoord
      have hzero : ∀ c, commutator P c = 0 := by
        intro c
        have : μ c = 0 := DFunLike.congr_fun hμDzero c
        rw [hrep c, this]
        ext z; simp [multiplication_apply]
      exact (mem_order_zero_iff_eq_multiplication P).mp ((mem_order_zero_iff P).mpr hzero)

end GenericRigidity

/-- **Coordinate rigidity over `K`** for `C_K`. -/
theorem coordinateRigidityK (P : Module.End (RatFunc k) (CK k C))
    (hP : P ∈ algebra (k := RatFunc k) (R := CK k C))
    (hcomm : ∀ i, commutator P (xCK k n C i) = 0) : P = multiplication (P 1) := by
  obtain ⟨r, hr⟩ := hP
  exact coordinateRigidity_of_derivations (xCK k n C)
    (fun δ hδ => derivationK_eq_zero_of_coord δ hδ) r P hr hcomm

end

end GlobalStafford.Chart
