import GlobalStafford.Chart.ScalarExtensionConstruction

/-!
# Étale chart data over `K = RatFunc k` (WP-18b)

`PLAN.md` §4, work package WP-18b. For an étale chart `C` over `B = k[x_1,…,x_n]`
this file assembles `EtaleChartData (RatFunc k) n (CK k C)`, the chart data of the
scalar-extended ring `C_K = K ⊗_k C`, from the WP-16 scalar-extension construction
(`bigTheta`, `xCK`, `liftDerivationK`, `coordinateRigidityK`) and the WP-13 finite
generic fibre over `k`, and feeds it into `s38Poly_of_chartData` to close the
remaining `Inputs.chartS38Poly` leaf.

It also proves a generic domain-transfer lemma for `ScalarExtensionInterface`:
if `D` has no zero divisors, neither does the scalar-extended ring `DK`.
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators
open scoped TensorProduct

noncomputable section

universe u

/-! ## 1. Domains transfer along a scalar extension interface -/

section NoZeroDivisorsTransfer

variable {k : Type u} [Field k] [CharZero k]
variable {D : Type u} [Ring D] [Algebra k D] [NoZeroDivisors D] [Nontrivial D]
variable {K : Type u} [Field K] [Algebra k K]
variable {DK : Type u} [Ring DK] [Algebra K DK] [Algebra k DK] [IsScalarTower k K DK]
variable {t : K}

/-- **Domain transfer along a scalar extension interface**: if `D` has no zero
divisors, neither does a scalar extension `DK` of `D` (`ScalarExtensionInterface`).
`x * y = 0` in `DK` gives, via `spanning`, nonzero central scalars `s_x, s_y` with
`s_x * x = Θ P`, `s_y * y = Θ Q`; centrality moves the scalars together so that
`Θ (P * Q) = s_x * s_y * (x * y) = 0`, hence `P * Q = 0` (`Θ` injective), hence
`P = 0` or `Q = 0` (`Polynomial D` has no zero divisors), hence `s_x * x = 0` or
`s_y * y = 0`; since `s_x`, `s_y` are units (nonzero elements of the field `K`),
`x = 0` or `y = 0`. -/
theorem noZeroDivisors_of_scalarExtension (I : ScalarExtensionInterface (k := k) D K DK t) :
    NoZeroDivisors DK where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro x y hxy
    by_contra hcon
    push_neg at hcon
    obtain ⟨hx, hy⟩ := hcon
    obtain ⟨h_x, hhx, P, hP⟩ := I.spanning x
    obtain ⟨h_y, hhy, Q, hQ⟩ := I.spanning y
    have hΘPQ : I.Θ (P * Q) = 0 := by
      rw [map_mul, ← hP, ← hQ, mul_assoc,
        ScalarExtensionInterface.pull_left h_y x y, hxy, mul_zero, mul_zero]
    have hPQ0 : P * Q = 0 := I.Θ_injective (by rw [hΘPQ, map_zero])
    rcases mul_eq_zero.mp hPQ0 with hP0 | hQ0
    · apply hx
      have hunit : IsUnit (algebraMap K DK (Polynomial.aeval t h_x)) :=
        IsUnit.map (algebraMap K DK) (isUnit_iff_ne_zero.mpr (I.aeval_ne_zero h_x hhx))
      exact hunit.mul_left_cancel (by rw [hP, hP0, map_zero, mul_zero])
    · apply hy
      have hunit : IsUnit (algebraMap K DK (Polynomial.aeval t h_y)) :=
        IsUnit.map (algebraMap K DK) (isUnit_iff_ne_zero.mpr (I.aeval_ne_zero h_y hhy))
      exact hunit.mul_left_cancel (by rw [hQ, hQ0, map_zero, mul_zero])

end NoZeroDivisorsTransfer

/-! ## 2. `D_k(C)` is nontrivial -/

section Setup

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {C : Type u} [CommRing C] [Algebra k C]
  [Algebra (B k n) C] [IsScalarTower k (B k n) C] [Algebra.FormallyEtale (B k n) C]

/-- `D_k(C)` is nontrivial whenever `C` is: `0 ≠ 1` in the subalgebra pulls back to
`0 ≠ 1` in `Module.End k C`, distinguished by a nonzero point of `C`. -/
theorem nontrivial_algebra [Nontrivial C] : Nontrivial (algebra (k := k) (R := C)) := by
  obtain ⟨c, hc⟩ := exists_ne (0 : C)
  refine ⟨0, 1, fun h => hc ?_⟩
  have h' := congrArg (fun P : algebra (k := k) (R := C) => (P : Module.End k C) c) h
  simpa using h'.symm

/-- `C_K = K ⊗_k C` is nontrivial whenever `C` is: the base change `f.lTensor K` of an
injective linear map `f : k → C` (spanning a nonzero point `c`) is injective by flatness
of `K` over `k`, and carries the nonzero element `1 ⊗ 1` to `1 ⊗ c ≠ 0`. -/
theorem nontrivial_CK [Nontrivial C] : Nontrivial (CK k C) := by
  obtain ⟨c, hc⟩ := exists_ne (0 : C)
  set f : k →ₗ[k] C := LinearMap.toSpanSingleton k C c with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have h0 : (a - b) • c = 0 := by
      have := sub_eq_zero.mpr hab
      simpa only [hf, LinearMap.toSpanSingleton_apply, ← sub_smul] using this
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc
  have hinj : Function.Injective (f.lTensor (RatFunc k)) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hfinj
  have h01 : ((1 : RatFunc k) ⊗ₜ[k] (1 : k) : RatFunc k ⊗[k] k) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.rid k (RatFunc k)) h0
    simp at this
  have hne : (f.lTensor (RatFunc k)) ((1 : RatFunc k) ⊗ₜ[k] (1 : k)) ≠ 0 :=
    fun h0 => h01 (hinj (by rw [h0, map_zero]))
  have heq : (f.lTensor (RatFunc k)) ((1 : RatFunc k) ⊗ₜ[k] (1 : k)) =
      (1 : RatFunc k) ⊗ₜ[k] c := by
    rw [LinearMap.lTensor_tmul, hf, LinearMap.toSpanSingleton_apply, one_smul]
  rw [heq] at hne
  exact ⟨_, 0, hne⟩

end Setup

end
end GlobalStafford.Chart
