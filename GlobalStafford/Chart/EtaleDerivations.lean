import GlobalStafford.Chart.EtaleChartData
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Derivation.Lie

/-!
# Étale derivations, commutation, and coordinate rigidity

`PLAN.md` §4, work package WP-12 (`Chart/EtaleDerivations.lean`). For `C` étale over
`B = k[x_1,…,x_n]`, this file builds the `n` coordinate derivations `«∂»_i` of `C`
(`liftDerivation`, dual to the coordinates `x_i` by `liftDerivation_coord`) via
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` and
`KaehlerDifferential.mvPolynomialBasis`, proves that a `k`-derivation of `C` vanishing on the
image of `B` is zero (`derivation_eq_zero_of_algebraMap`, from `Ω[C⁄B]` being a subsingleton
under `Algebra.FormallyEtale`), deduces that the coordinate derivations commute
(`liftDerivation_comm`), and proves coordinate rigidity: a finite-order operator commuting with
every coordinate is a multiplication operator (`coordinateRigidity`). These assemble into the
derivation-and-rigidity fields of `EtaleChartData` (`etaleChartData_of_fields`); the remaining
fields (finiteness of the generic fibre, injectivity of `B → C`, `D_k(C)` a domain) are supplied
by WP-13 and WP-14.
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators
open KaehlerDifferential
open scoped TensorProduct

noncomputable section

universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {C : Type u} [CommRing C] [Algebra k C]
  [Algebra (B k n) C] [IsScalarTower k (B k n) C] [Algebra.FormallyEtale (B k n) C]

/-! ## 1. The coordinate derivations -/

/-- The `C`-linear functional `Ω[C⁄k] → C` reading off the coefficient of `dX_i` after
transporting along `tensorKaehlerEquivOfFormallyEtale` and the polynomial basis of `Ω[B⁄k]`. -/
def liftFunctional (i : Fin n) : Ω[C⁄k] →ₗ[C] C :=
  (LinearMap.liftBaseChange C
      ((Algebra.linearMap (B k n) C).comp
        ((Finsupp.lapply i).comp (mvPolynomialBasis k (Fin n)).repr.toLinearMap))) ∘ₗ
    (tensorKaehlerEquivOfFormallyEtale k (B k n) C).symm.toLinearMap

/-- The `i`-th coordinate derivation of `C`, dual to `x_i` (`liftDerivation_coord`) and
extending `∂/∂x_i` on `B` (`liftDerivation_algebraMap`). -/
noncomputable def liftDerivation (i : Fin n) : Derivation k C C :=
  KaehlerDifferential.linearMapEquivDerivation k C (liftFunctional i)

theorem liftDerivation_algebraMap (i : Fin n) (b : B k n) :
    liftDerivation (k := k) (C := C) i (algebraMap (B k n) C b) =
      algebraMap (B k n) C (MvPolynomial.pderiv i b) := by
  show liftFunctional (k := k) (C := C) i (D k C (algebraMap (B k n) C b)) = _
  unfold liftFunctional
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  rw [LinearMap.liftBaseChange_tmul]
  simp [Algebra.linearMap]

/-- **`∂_coord`**: `liftDerivation i` is dual to the coordinate `x_j`. -/
theorem liftDerivation_coord (i j : Fin n) :
    liftDerivation (k := k) (C := C) i (xC k n C j) = if i = j then 1 else 0 := by
  unfold GlobalStafford.Chart.xC
  rw [liftDerivation_algebraMap]
  by_cases h : i = j
  · subst h; simp [MvPolynomial.pderiv_X]
  · simp [MvPolynomial.pderiv_X, h]

/-! ## 2. Uniqueness of derivations vanishing on `B` -/

/-- A `k`-derivation of `C` vanishing on `B` is `B`-linear, hence a `B`-derivation. -/
def toDerivationB (δ : Derivation k C C) (h : ∀ b : B k n, δ (algebraMap (B k n) C b) = 0) :
    Derivation (B k n) C C where
  toLinearMap :=
    { toFun := δ
      map_add' := δ.map_add
      map_smul' := fun b x => by
        show δ (b • x) = b • δ x
        rw [Algebra.smul_def, Algebra.smul_def, δ.leibniz, h b, smul_zero, add_zero, smul_eq_mul] }
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

/-- Any `k`-derivation of `C` vanishing on the image of `B` is zero, because `Ω[C⁄B]` is a
subsingleton (`C` is formally unramified over `B`, being formally étale over it). -/
theorem derivation_eq_zero_of_algebraMap (δ : Derivation k C C)
    (h : ∀ b : B k n, δ (algebraMap (B k n) C b) = 0) : δ = 0 := by
  haveI hsub : Subsingleton (Ω[C⁄(B k n)] →ₗ[C] C) := by
    constructor
    intro f g
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim x 0
    rw [hx, map_zero, map_zero]
  set Cδ := toDerivationB (k := k) (C := C) δ h with hCδ
  have hd0 : (KaehlerDifferential.linearMapEquivDerivation (B k n) C).symm Cδ =
      (KaehlerDifferential.linearMapEquivDerivation (B k n) C).symm 0 :=
    Subsingleton.elim _ _
  have hd : Cδ = 0 :=
    (KaehlerDifferential.linearMapEquivDerivation (B k n) C).symm.injective hd0
  apply Derivation.ext
  intro x
  have hx := congrArg (fun D => D.toLinearMap x) hd
  simpa [hCδ, toDerivationB] using hx

/-! ## 3. The coordinate derivations commute -/

/-- **`∂_comm`**: the coordinate derivations of `C` commute, because their Lie-bracket
derivation (`⁅D₁, D₂⁆ a = D₁ (D₂ a) - D₂ (D₁ a)`) vanishes on `B` (`∂/∂x_i` commute on `B`),
hence is zero by `derivation_eq_zero_of_algebraMap`. -/
theorem liftDerivation_comm (i j : Fin n) :
    (liftDerivation (k := k) (C := C) i).toLinearMap *
        (liftDerivation (k := k) (C := C) j).toLinearMap =
      (liftDerivation (k := k) (C := C) j).toLinearMap *
        (liftDerivation (k := k) (C := C) i).toLinearMap := by
  have hzero : (⁅liftDerivation (k := k) (C := C) i, liftDerivation (k := k) (C := C) j⁆ :
      Derivation k C C) = 0 := by
    apply derivation_eq_zero_of_algebraMap (k := k) (n := n) (C := C)
    intro b
    have hcomm : MvPolynomial.pderiv i (MvPolynomial.pderiv j b) =
        MvPolynomial.pderiv j (MvPolynomial.pderiv i b) := by
      classical
      induction b using MvPolynomial.induction_on with
      | C c => simp
      | add p q hp hq =>
          simp only [Derivation.map_add, hp, hq]
      | mul_X p m ih =>
          simp only [Derivation.map_add, Derivation.leibniz, MvPolynomial.pderiv_X,
            smul_eq_mul, ih, Pi.single_apply]
          split_ifs <;> simp [map_zero, map_one] <;> ring
    simp only [Derivation.commutator_apply, liftDerivation_algebraMap, hcomm, sub_self]
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hzero x
  rw [Derivation.commutator_apply] at hx
  simp only [Module.End.mul_apply]
  exact sub_eq_zero.mp hx

/-! ## 4. Coordinate rigidity -/

/-- The commutator of an operator with a product distributes: this is a purely algebraic
identity (no order or commutation hypothesis on `P`). -/
theorem commutator_add_right (P : Module.End k C) (a b : C) :
    commutator P (a + b) = commutator P a + commutator P b := by
  ext z
  simp only [commutator_apply, LinearMap.add_apply, mul_add, add_mul, map_add]
  ring

theorem commutator_mul_right (P : Module.End k C) (a b : C) :
    commutator P (a * b) = commutator P a * multiplication b + multiplication a * commutator P b := by
  ext z
  simp only [commutator_apply, Module.End.mul_apply, multiplication_apply, LinearMap.add_apply]
  ring_nf

theorem commutator_smul_right (P : Module.End k C) (a : C) (r : k) :
    commutator P (r • a) = r • commutator P a := by
  ext z
  simp only [commutator_apply, LinearMap.smul_apply, smul_mul_assoc]
  rw [P.map_smul, smul_sub]

/-- Any operator commuting with every coordinate commutes with every element in the image of
`B` (by `MvPolynomial.induction_on` and `commutator_add_right` / `commutator_mul_right`). -/
theorem commutator_algebraMap (P : Module.End k C) (hx : ∀ i, commutator P (xC k n C i) = 0) :
    ∀ b : B k n, commutator P (algebraMap (B k n) C b) = 0 := by
  intro b
  induction b using MvPolynomial.induction_on with
  | C c =>
      have hcB : algebraMap (B k n) C (MvPolynomial.C c) = algebraMap k C c := by
        calc
          algebraMap (B k n) C (MvPolynomial.C c)
              = algebraMap (B k n) C (algebraMap k (B k n) c) := by
                rw [MvPolynomial.algebraMap_eq]
          _ = algebraMap k C c := (IsScalarTower.algebraMap_apply k (B k n) C c).symm
      rw [hcB]
      ext z
      rw [commutator_apply, ← Algebra.smul_def, ← Algebra.smul_def, P.map_smul, sub_self]
      rfl
  | add f g hf hg =>
      rw [map_add, commutator_add_right, hf, hg, add_zero]
  | mul_X f i hf =>
      have hmulX : algebraMap (B k n) C (f * MvPolynomial.X i) =
          algebraMap (B k n) C f * xC k n C i := by
        rw [map_mul]; rfl
      rw [hmulX, commutator_mul_right, hf, hx i]
      simp

/-- Jacobi-type identity for the mixed operator/scalar commutator: since multiplication by `c`
and by `x` commute (`C` is commutative), the two ways of iterating `commutator` agree. -/
theorem commutator_commutator_comm (P : Module.End k C) (c x : C) :
    commutator (commutator P c) x = commutator (commutator P x) c := by
  ext z
  simp only [commutator_apply]
  ring_nf

theorem commutator_zero_left (a : C) : commutator (0 : Module.End k C) a = 0 := by
  ext z; simp [commutator_apply]

/-- Auxiliary induction for `coordinateRigidity`, on the explicit order bound `m`. -/
theorem coordinateRigidity_aux : ∀ (m : ℕ) (P : Module.End k C),
    P ∈ order (k := k) (R := C) m → (∀ i, commutator P (xC k n C i) = 0) →
      P = multiplication (P 1) := by
  intro m
  induction m with
  | zero =>
      intro P hPm _
      exact (mem_order_zero_iff_eq_multiplication P).mp hPm
  | succ m IH =>
      intro P hPm hcomm
      have hB : ∀ b : B k n, commutator P (algebraMap (B k n) C b) = 0 :=
        commutator_algebraMap P hcomm
      -- `μ c := P c - c * P 1` is the candidate derivation witnessing `commutator P c`.
      set μ : C → C := fun c => P c - c * P 1 with hμdef
      have hrep : ∀ c : C, commutator P c = multiplication (μ c) := by
        intro c
        have hQorder : commutator P c ∈ order (k := k) (R := C) m := hPm c
        have hQcomm : ∀ i, commutator (commutator P c) (xC k n C i) = 0 := by
          intro i
          rw [commutator_commutator_comm, hcomm i, commutator_zero_left]
        have hQeq := IH (commutator P c) hQorder hQcomm
        rw [hQeq]
        congr 1
        show P (c * 1) - c * P 1 = μ c
        rw [mul_one]
      have hμadd : ∀ a b, μ (a + b) = μ a + μ b := by
        intro a b; simp only [hμdef, map_add, add_mul]; ring
      have hμsmul : ∀ (r : k) (a : C), μ (r • a) = r • μ a := by
        intro r a; simp only [hμdef, P.map_smul, smul_mul_assoc, smul_sub]
      have hμone : μ 1 = 0 := by simp [hμdef]
      have hμleibniz : ∀ a b : C, μ (a * b) = a • μ b + b • μ a := by
        intro a b
        have e1 := hrep (a * b)
        have e2 := commutator_mul_right P a b
        rw [e1] at e2
        have e3 := congrArg (fun T : Module.End k C => T 1) e2
        simp only [multiplication_apply, mul_one, LinearMap.add_apply, Module.End.mul_apply] at e3
        rw [hrep a, hrep b] at e3
        simp only [multiplication_apply] at e3
        rw [e3, smul_eq_mul, smul_eq_mul]
        ring
      let μL : C →ₗ[k] C :=
        { toFun := μ, map_add' := hμadd, map_smul' := by intro r a; simpa using hμsmul r a }
      let μD : Derivation k C C :=
        { toLinearMap := μL, map_one_eq_zero' := hμone, leibniz' := hμleibniz }
      have hμzero : ∀ b : B k n, μD (algebraMap (B k n) C b) = 0 := by
        intro b
        show μ (algebraMap (B k n) C b) = 0
        have hb := hB b
        rw [hrep] at hb
        have hb0 : multiplication (k := k) (μ (algebraMap (B k n) C b)) = (0 : Module.End k C) := hb
        have hb1 := congrArg (fun T : Module.End k C => T 1) hb0
        simpa [multiplication_apply] using hb1
      have hμDzero : μD = 0 := derivation_eq_zero_of_algebraMap (k := k) (n := n) (C := C) μD hμzero
      have hμallzero : ∀ c, μ c = 0 := by
        intro c
        exact DFunLike.congr_fun hμDzero c
      have hzero : ∀ c, commutator P c = 0 := by
        intro c
        rw [hrep c, hμallzero c]
        ext z; simp [multiplication_apply]
      have horder0 : P ∈ order (k := k) (R := C) 0 := by
        rw [mem_order_zero_iff]; exact hzero
      exact (mem_order_zero_iff_eq_multiplication P).mp horder0

/-- **`coordinateRigidity`**: a finite-order operator commuting with every coordinate is a
multiplication operator. -/
theorem coordinateRigidity (P : Module.End k C) (hP : P ∈ algebra (k := k) (R := C))
    (hcomm : ∀ i, commutator P (xC k n C i) = 0) : P = multiplication (P 1) := by
  obtain ⟨m, hPm⟩ := hP
  exact coordinateRigidity_aux m P hPm hcomm

/-! ## 5. Assembly -/

/-- Assembles the derivation-and-rigidity fields (`«∂»`, `«∂_coord»`, `«∂_comm»`,
`coordinateRigidity`) of `EtaleChartData` built in this file with the remaining geometric
fields (`finiteGenericFibre`, `algebraMap_ne_zero`, `noZeroDivisors`) supplied by WP-13/WP-14. -/
theorem etaleChartData_of_fields
    (hfin : ∃ (m : ℕ) (c : Fin m → C), ∀ x : C, ∃ b : B k n, b ≠ 0 ∧
        ∃ t : Fin m → B k n, algebraMap (B k n) C b * x = ∑ i, c i * algebraMap (B k n) C (t i))
    (hne : ∀ b : B k n, b ≠ 0 → algebraMap (B k n) C b ≠ 0)
    (hdom : NoZeroDivisors (algebra (k := k) (R := C))) :
    Nonempty (EtaleChartData k n C) :=
  ⟨{ «∂» := liftDerivation
     «∂_coord» := liftDerivation_coord
     «∂_comm» := liftDerivation_comm
     coordinateRigidity := coordinateRigidity
     finiteGenericFibre := hfin
     algebraMap_ne_zero := hne
     noZeroDivisors := hdom }⟩

end
end GlobalStafford.Chart

#print axioms GlobalStafford.Chart.liftDerivation_algebraMap
#print axioms GlobalStafford.Chart.liftDerivation_coord
#print axioms GlobalStafford.Chart.derivation_eq_zero_of_algebraMap
#print axioms GlobalStafford.Chart.liftDerivation_comm
#print axioms GlobalStafford.Chart.coordinateRigidity
#print axioms GlobalStafford.Chart.etaleChartData_of_fields
