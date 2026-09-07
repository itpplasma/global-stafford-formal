import GlobalStafford.Chart.ScalarExtensionConstruction
import GlobalStafford.Chart.GenericFibre

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

/-! ## 3. `MvPolynomial (Fin n) K` acts on `C_K` through `xCK` -/

section AlgebraBK

variable {k : Type u} [Field k] {n : ℕ} {C : Type u} [CommRing C] [Algebra k C]
  [Algebra (B k n) C] [IsScalarTower k (B k n) C]

/-- `MvPolynomial (Fin n) K` acts on `C_K = K ⊗_k C` through the coordinates `xCK`,
i.e. `X i ↦ xCK i`. This supplies the `Algebra (B K n) (C_K)` instance required by
`EtaleChartData K n (C_K)`; there is no pre-existing such instance (only
`Algebra (B k n) C` and `Algebra K (C_K)` are given), so registering it as a plain
`instance` is safe. -/
noncomputable instance instAlgebraBK : Algebra (B (RatFunc k) n) (CK k C) :=
  ((MvPolynomial.aeval (xCK k n C)).toRingHom).toAlgebra

theorem algebraMap_BK_X (i : Fin n) :
    algebraMap (B (RatFunc k) n) (CK k C) (MvPolynomial.X i) = xCK k n C i :=
  MvPolynomial.aeval_X (xCK k n C) i

theorem algebraMap_BK_apply (q : B (RatFunc k) n) :
    algebraMap (B (RatFunc k) n) (CK k C) q = MvPolynomial.aeval (xCK k n C) q := rfl

/-- `K` acts as scalars compatibly through `B K n = MvPolynomial (Fin n) K`: `aeval xCK` is
a `K`-algebra homomorphism, so it commutes with the algebra map from `K`. -/
instance instIsScalarTowerBK : IsScalarTower (RatFunc k) (B (RatFunc k) n) (CK k C) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  rw [algebraMap_BK_apply]
  exact (AlgHom.commutes (MvPolynomial.aeval (xCK k n C)) x).symm

/-- The base-changed coefficient map `B k n → B K n`. -/
abbrev mapBK (b : B k n) : B (RatFunc k) n := MvPolynomial.map (algebraMap k (RatFunc k)) b

theorem mapBK_ne_zero {b : B k n} (hb : b ≠ 0) : mapBK (k := k) (n := n) b ≠ 0 := by
  have hinj : Function.Injective (MvPolynomial.map (algebraMap k (RatFunc k)) :
      B k n → B (RatFunc k) n) :=
    MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective k (RatFunc k))
  exact fun h0 => hb (hinj (h0.trans (map_zero _).symm))

/-- The base-changed coefficient map, followed by `algebraMap (B K n) C_K`, is `1 ⊗ (algebraMap
(B k n) C -)`: expand by induction on `b` following the pattern of `exists_weylAction_eq_multiplicationD`
and `commutator_algebraMap`. -/
theorem algebraMap_BK_mapBK (b : B k n) :
    algebraMap (B (RatFunc k) n) (CK k C) (mapBK b) =
      (1 : RatFunc k) ⊗ₜ[k] (algebraMap (B k n) C b) := by
  induction b using MvPolynomial.induction_on with
  | C c =>
      have hcB : algebraMap (B k n) C (MvPolynomial.C c) = algebraMap k C c := by
        calc
          algebraMap (B k n) C (MvPolynomial.C c)
              = algebraMap (B k n) C (algebraMap k (B k n) c) := by
                rw [MvPolynomial.algebraMap_eq]
          _ = algebraMap k C c := (IsScalarTower.algebraMap_apply k (B k n) C c).symm
      have hmapC : mapBK (k := k) (n := n) (MvPolynomial.C c) =
          MvPolynomial.C (algebraMap k (RatFunc k) c) := MvPolynomial.map_C _ _
      have hCeq : algebraMap (RatFunc k) (B (RatFunc k) n) (algebraMap k (RatFunc k) c) =
          MvPolynomial.C (algebraMap k (RatFunc k) c) := by
        rw [MvPolynomial.algebraMap_eq]
      rw [hmapC, ← hCeq, algebraMap_BK_apply, AlgHom.commutes, hcB, one_tmul_algebraMap,
        ← IsScalarTower.algebraMap_apply k (RatFunc k) (CK k C)]
  | add f g hf hg =>
      have hmapadd : mapBK (k := k) (n := n) (f + g) = mapBK f + mapBK g := map_add _ _ _
      rw [hmapadd, map_add, map_add, hf, hg, TensorProduct.tmul_add]
  | mul_X f i hf =>
      have hmapX : mapBK (k := k) (n := n) (f * MvPolynomial.X i) =
          mapBK f * MvPolynomial.X i := by
        show MvPolynomial.map (algebraMap k (RatFunc k)) (f * MvPolynomial.X i) = _
        rw [map_mul, MvPolynomial.map_X]
      have hfX : algebraMap (B k n) C (f * MvPolynomial.X i) =
          algebraMap (B k n) C f * xC k n C i := by rw [map_mul]; rfl
      rw [hmapX, map_mul, algebraMap_BK_X, hf, hfX, xCK,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end AlgebraBK

/-! ## 4. The coordinate derivations of `C_K` commute -/

section DerivationsComm

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {C : Type u} [CommRing C] [Algebra k C]
  [Algebra (B k n) C] [IsScalarTower k (B k n) C] [Algebra.FormallyEtale (B k n) C]

/-- **`«∂_comm»` over `K`**: the coordinate derivations `liftDerivationK i` of `C_K` commute,
by base change of `liftDerivation_comm` (base change is a ring homomorphism on
`Module.End k C`, `baseChangeEnd_mul`). -/
theorem liftDerivationK_comm (i j : Fin n) :
    (liftDerivationK (k := k) (n := n) (C := C) i).toLinearMap *
        (liftDerivationK j).toLinearMap =
      (liftDerivationK j).toLinearMap * (liftDerivationK i).toLinearMap := by
  show baseChangeEnd (liftDerivation (k := k) (C := C) i).toLinearMap *
      baseChangeEnd (liftDerivation j).toLinearMap =
    baseChangeEnd (liftDerivation j).toLinearMap * baseChangeEnd (liftDerivation i).toLinearMap
  rw [← baseChangeEnd_mul, ← baseChangeEnd_mul, liftDerivation_comm]

end DerivationsComm

/-! ## 5. `algebraMap_ne_zero` over `K` -/

section AlgebraMapNeZero

variable {k : Type u} [Field k] {n : ℕ} {C : Type u} [CommRing C] [IsDomain C] [Algebra k C]
  [Algebra (B k n) C] [IsScalarTower k (B k n) C] [Algebra.Etale (B k n) C]

/-- The `k`-linear map underlying `algebraMap (B k n) C`. -/
def algebraMapBLinear : B k n →ₗ[k] C := (IsScalarTower.toAlgHom k (B k n) C).toLinearMap

theorem algebraMapBLinear_apply (b : B k n) :
    algebraMapBLinear (k := k) (n := n) (C := C) b = algebraMap (B k n) C b := rfl

theorem algebraMapBLinear_injective :
    Function.Injective (algebraMapBLinear (k := k) (n := n) (C := C)) :=
  algebraMap_injective_of_etale

/-- The image in `C` of the monomial `X^α`. -/
def xpow (α : Fin n →₀ ℕ) : C := algebraMap (B k n) C (MvPolynomial.monomial α (1 : k))

theorem algebraMap_B_eq_aeval_xC (b : B k n) :
    algebraMap (B k n) C b = MvPolynomial.aeval (xC k n C) b := by
  induction b using MvPolynomial.induction_on with
  | C c =>
      have hcB : algebraMap (B k n) C (MvPolynomial.C c) = algebraMap k C c := by
        calc
          algebraMap (B k n) C (MvPolynomial.C c)
              = algebraMap (B k n) C (algebraMap k (B k n) c) := by
                rw [MvPolynomial.algebraMap_eq]
          _ = algebraMap k C c := (IsScalarTower.algebraMap_apply k (B k n) C c).symm
      rw [hcB, show (MvPolynomial.C c : B k n) = algebraMap k (B k n) c by
        rw [MvPolynomial.algebraMap_eq], AlgHom.commutes]
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | mul_X f i hf =>
      have hL : algebraMap (B k n) C (f * MvPolynomial.X i) =
          algebraMap (B k n) C f * xC k n C i := by rw [map_mul]; rfl
      rw [hL, hf, map_mul, MvPolynomial.aeval_X]

theorem xpow_eq_prod (α : Fin n →₀ ℕ) :
    xpow (k := k) (n := n) (C := C) α = α.prod (fun i e => xC k n C i ^ e) := by
  rw [xpow, algebraMap_B_eq_aeval_xC, MvPolynomial.aeval_monomial, map_one, one_mul]

/-- `aeval xCK` sends the monomial `α ↦ κ` to `κ ⊗ xpow α`: expand `xCK i = includeRight (xC i)`,
push `includeRight` through the finite product (`map_prod`), and collect the resulting scalar. -/
theorem aeval_xCK_monomial (α : Fin n →₀ ℕ) (κ : RatFunc k) :
    MvPolynomial.aeval (xCK k n C) (MvPolynomial.monomial α κ) =
      κ ⊗ₜ[k] (xpow (k := k) (n := n) (C := C) α) := by
  classical
  rw [MvPolynomial.aeval_monomial]
  have hxCKprod : α.prod (fun i e => xCK k n C i ^ e) =
      Algebra.TensorProduct.includeRight (α.prod (fun i e => xC k n C i ^ e) : C) := by
    have hstep : ∀ i ∈ α.support, xCK k n C i ^ α i =
        Algebra.TensorProduct.includeRight (xC k n C i ^ α i : C) := by
      intro i _
      rw [map_pow, Algebra.TensorProduct.includeRight_apply]; rfl
    rw [Finsupp.prod, Finsupp.prod, map_prod]
    exact Finset.prod_congr rfl hstep
  rw [hxCKprod, ← xpow_eq_prod]
  show (algebraMap (RatFunc k) (CK k C)) κ * _ = _
  rw [algebraMap_CK, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The monomial family `xpow` is `k`-linearly independent in `C`, because `MvPolynomial.basisMonomials`
is a basis of `B k n` and `algebraMap (B k n) C` is injective (`algebraMap_injective_of_etale`). -/
theorem xpow_linearIndependent :
    LinearIndependent k (xpow (k := k) (n := n) (C := C)) := by
  have hinj : Function.Injective (algebraMapBLinear (k := k) (n := n) (C := C)) :=
    algebraMapBLinear_injective
  have hbasis := (MvPolynomial.basisMonomials (Fin n) k).linearIndependent
  have hmap := hbasis.map (f := algebraMapBLinear (k := k) (n := n) (C := C))
    (show Disjoint _ (LinearMap.ker (algebraMapBLinear (k := k) (n := n) (C := C))) by
      rw [LinearMap.ker_eq_bot.mpr hinj]; exact disjoint_bot_right)
  have heq : (xpow (k := k) (n := n) (C := C)) =
      algebraMapBLinear ∘ (MvPolynomial.basisMonomials (Fin n) k) := by
    funext α
    show xpow α = algebraMapBLinear (MvPolynomial.monomial α (1 : k))
    rw [algebraMapBLinear_apply]; rfl
  rw [heq]
  exact hmap

/-- **`eq_zero_of_sum_tmul_monomial_eq_zero`**: a finite `K`-combination of the monomials
`xpow α` that vanishes in `C_K` has every coefficient zero. Analogue of
`eq_zero_of_sum_tmul_pow_eq_zero` for the monomial family `xpow`, using the `k`-basis
`(MvPolynomial.basisMonomials (Fin n) k).baseChange K` of `C_K` obtained by base change. -/
theorem eq_zero_of_sum_tmul_monomial_eq_zero (s : Finset (Fin n →₀ ℕ)) (y : (Fin n →₀ ℕ) → RatFunc k)
    (hy : ∑ α ∈ s, (y α) ⊗ₜ[k] (xpow (k := k) (n := n) (C := C) α) = (0 : CK k C)) :
    ∀ α ∈ s, y α = 0 := by
  classical
  set f : B k n →ₗ[k] C := algebraMapBLinear (k := k) (n := n) (C := C) with hf
  have hfinj : Function.Injective f := algebraMapBLinear_injective
  have hrinj : Function.Injective (f.lTensor (RatFunc k)) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hfinj
  set z : RatFunc k ⊗[k] (B k n) := ∑ α ∈ s, (y α) ⊗ₜ[k] (MvPolynomial.monomial α (1 : k))
    with hzdef
  have hmap : (f.lTensor (RatFunc k)) z = 0 := by
    rw [hzdef, map_sum, ← hy]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [LinearMap.lTensor_tmul, hf, algebraMapBLinear_apply, ← xpow]
  have hz0 : z = 0 := hrinj (by rw [hmap, map_zero])
  set bB := MvPolynomial.basisMonomials (Fin n) k with hbB
  set b := bB.baseChange (RatFunc k) with hb
  have hzcoord : z = ∑ α ∈ s, (y α) • b α := by
    rw [hzdef]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hb, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, hbB,
      MvPolynomial.coe_basisMonomials]
  intro α hα
  have hsum0 : ∑ α ∈ s, (y α) • b α = 0 := by rw [← hzcoord, hz0]
  exact linearIndependent_iff'.mp b.linearIndependent s y hsum0 α hα

/-- **`algebraMap_ne_zero` over `K`**: `algebraMap (B K n) (C_K)` is injective on nonzero
elements. Expand `q` as a sum of monomials (`MvPolynomial.as_sum`), rewrite each term via
`aeval_xCK_monomial`, and apply `eq_zero_of_sum_tmul_monomial_eq_zero` to the leading
coefficient. -/
theorem algebraMap_ne_zero_K (q : B (RatFunc k) n) (hq : q ≠ 0) :
    algebraMap (B (RatFunc k) n) (CK k C) q ≠ 0 := by
  classical
  intro h0
  obtain ⟨j, hj⟩ : q.support.Nonempty := MvPolynomial.support_nonempty.mpr hq
  rw [algebraMap_BK_apply] at h0
  have hsum : ∑ α ∈ q.support, (q.coeff α) ⊗ₜ[k]
      (xpow (k := k) (n := n) (C := C) α) = (0 : CK k C) := by
    rw [← h0]
    conv_lhs => rw [← Finset.sum_congr rfl (fun α (_ : α ∈ q.support) => aeval_xCK_monomial α (q.coeff α))]
    rw [← map_sum, ← q.as_sum]
  exact (MvPolynomial.mem_support_iff.mp hj)
    (eq_zero_of_sum_tmul_monomial_eq_zero q.support (fun α => q.coeff α) hsum j hj)

end AlgebraMapNeZero

end
end GlobalStafford.Chart
