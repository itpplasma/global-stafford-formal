import GlobalStafford.Chart.ScalarExtension
import GlobalStafford.Chart.EtaleDerivations
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Flat.Basic

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

end

end GlobalStafford.Chart
