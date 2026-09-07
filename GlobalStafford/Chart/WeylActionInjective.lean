import GlobalStafford.Chart.ChartDomain.NormalForm
import Stafford38.Weyl.PBW

/-!
# Injectivity of the Weyl action on an étale chart (WP-18a)

`PLAN.md` §4 (WP-18), sub-package WP-18a. For an étale chart `E : EtaleChartData k n C` whose
derivations are the lifted coordinate derivations of `Chart/EtaleDerivations.lean`
(`hE : ∀ i, E.«∂» i = liftDerivation i`) and whose ambient coordinate ring `B k n → C` is
injective, this file proves `weylAction_injective`: the induced algebra homomorphism
`weylAction E : PresentedWeyl k n →ₐ[k] algebra k C` is injective. This discharges the
`hinj` hypothesis of `Chart/EtaleChartData.lean`'s `rightOre_chart`, completing the chart-level
right Ore transfer (`PLAN.md` §7, "Global domain and right Ore").

## Proof outline

* `presentedOrderedMonomial_eq_ncp`: purely inside `PresentedWeyl k n`, the recursively
  built ordered monomial `presentedOrderedMonomial k n a p`
  (`Stafford38.WeylPBW.presentedOrderedMonomial`, read off `IteratedEquivalence.lean`'s
  `previousWeylEmbedding`, `presentedCoordinate`, `presentedMomentum`) equals the product of a
  coordinate-generator `Finset.noncommProd` and a momentum-generator `Finset.noncommProd`, by
  induction on `n` using `previousWeylEmbedding`'s compatibility with the generators
  (`previousWeylEmbedding_generator`) and the generic reindexing lemma `noncommProd_univ_succ`
  (peeling the newest `Fin (n+1)` index off a commuting `Finset.univ.noncommProd`, built from
  `Fin.univ_succ` and a `Finset.map`/`noncommProd` bridge, `noncommProd_finset_map`).
* `weylAction_orderedMonomial`: applying the algebra homomorphism `weylAction E` to
  `presentedOrderedMonomial_eq_ncp` and using `weylAction_X`, `weylAction_D`, and `hE` identifies
  the coordinate factor with `Operators.multiplicationD (∏ i, x_i ^ a i)` (via the bundled
  monoid hom `multiplicationDHom` and `C`'s commutativity, `Finset.noncommProd_eq_prod`) and the
  momentum factor with `partialMonomial` (`Chart/ChartDomain/Monomials.lean`), matching the
  `noncommProd` in `partialMonomial`'s own definition termwise.
* `weylAction_injective`: expand `z : PresentedWeyl k n` in the PBW basis
  (`Stafford38.WeylPBW.presentedPBWBasis`, `Basis.linearCombination_repr`), group the terms by
  their momentum exponent (`Finset.sum_fiberwise_of_maps_to`), and apply
  `weylAction_orderedMonomial` termwise to write `weylAction E z` (coerced to `Module.End k C`)
  as `∑ j, Q j • partialMonomial j` for `Q j : C` a `B k n`-coefficient combination. Vanishing of
  `weylAction E z` forces every `Q j = 0` (`linearIndependent_partialMonomial`,
  `Chart/ChartDomain/NormalForm.lean`), and `Q j = 0` forces every relevant PBW coefficient of
  `z` to vanish (injectivity of `algebraMap (B k n) C`, `MvPolynomial.coeff` reading off a
  distinguished monomial coefficient), hence `z = 0`.
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators
open Stafford38.WeylUniversal Stafford38.WeylIteratedEquivalence Stafford38.WeylPBW
open Stafford38.Characteristic (PhaseVar)
open Finset
open scoped nonZeroDivisors

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

variable {k : Type u} [Field k] [CharZero k]

/-! ## 1. Generic `Finset.noncommProd` reindexing lemmas -/

/-- `Finset.noncommProd` over `s.map e` (an injective embedding `e`) equals `Finset.noncommProd`
over `s` of the precomposed family. -/
theorem noncommProd_finset_map {α β R : Type*} [Monoid R] (e : α ↪ β) (s : Finset α)
    (g : β → R) (comm) :
    (s.map e).noncommProd g comm = s.noncommProd (fun i => g (e i))
      (fun x hx y hy hxy => comm (Finset.mem_map_of_mem e hx) (Finset.mem_map_of_mem e hy)
        (fun h => hxy (e.injective h))) := by
  simp [Finset.noncommProd, Finset.map_val, Multiset.map_map, Function.comp]

/-- Peel the newest (`0`) index off a `Finset.univ.noncommProd` over `Fin (m + 1)`, from
`Fin.univ_succ` and `noncommProd_finset_map`. -/
theorem noncommProd_univ_succ {R : Type*} [Monoid R] {m : ℕ} (g : Fin (m + 1) → R)
    (comm : ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))).Pairwise
      (Function.onFun Commute g)) :
    ∃ comm' : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).Pairwise
        (Function.onFun Commute (fun i => g i.succ)),
      (Finset.univ : Finset (Fin (m + 1))).noncommProd g comm =
        g 0 * (Finset.univ : Finset (Fin m)).noncommProd (fun i => g i.succ) comm' := by
  classical
  refine ⟨fun i _ j _ hij => comm (Finset.mem_univ _) (Finset.mem_univ _)
    (fun h => hij (Fin.succ_injective _ h)), ?_⟩
  have huniv : (Finset.univ : Finset (Fin (m + 1))) =
      Finset.cons 0 ((Finset.univ : Finset (Fin m)).map ⟨Fin.succ, Fin.succ_injective _⟩)
        (by simp) :=
    Fin.univ_succ m
  have step := Finset.noncommProd_congr huniv (f := g) (fun _ _ => rfl) comm
  rw [step, Finset.noncommProd_cons, noncommProd_finset_map]
  rfl

/-! ## 2. Commutation of the presentation generators, from the values of `Matrix.J` -/

theorem J_val_zero_coord_coord (n : ℕ) (i j : Fin n) :
    Matrix.J (Fin n) k (Sum.inl i) (Sum.inl j) = 0 := by simp [Matrix.J, Matrix.fromBlocks]

theorem J_val_zero_mom_mom (n : ℕ) (i j : Fin n) :
    Matrix.J (Fin n) k (Sum.inr i) (Sum.inr j) = 0 := by simp [Matrix.J, Matrix.fromBlocks]

theorem J_val_zero_coord_mom (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    Matrix.J (Fin n) k (Sum.inl i) (Sum.inr j) = 0 := by simp [Matrix.J, Matrix.fromBlocks, h]

theorem J_val_zero_mom_coord (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    Matrix.J (Fin n) k (Sum.inr i) (Sum.inl j) = 0 := by simp [Matrix.J, Matrix.fromBlocks, h]

theorem commute_of_commutator_zero {n : ℕ} {u v : PresentedWeyl k n}
    (h : Stafford.commutator u v = 0) : Commute u v := sub_eq_zero.mp h

theorem presentedCoordGen_comm (n : ℕ) :
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Commute
        (fun i => Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inl i))) := by
  intro i _ j _ _
  exact commute_of_commutator_zero
    (by rw [Stafford.freeWeylGenerator_commutator, J_val_zero_coord_coord, map_zero])

theorem presentedMomGen_comm (n : ℕ) :
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
      (Function.onFun Commute
        (fun i => Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i))) := by
  intro i _ j _ _
  exact commute_of_commutator_zero
    (by rw [Stafford.freeWeylGenerator_commutator, J_val_zero_mom_mom, map_zero])

theorem presentedCoordMom_comm_ne (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    Commute (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inl i))
      (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr j)) :=
  commute_of_commutator_zero
    (by rw [Stafford.freeWeylGenerator_commutator, J_val_zero_coord_mom _ _ _ h, map_zero])

theorem presentedMomCoord_comm_ne (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    Commute (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i))
      (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inl j)) :=
  commute_of_commutator_zero
    (by rw [Stafford.freeWeylGenerator_commutator, J_val_zero_mom_coord _ _ _ h, map_zero])

/-! ## 3. `presentedOrderedMonomial` as a product of a coordinate and a momentum `noncommProd` -/

/-- The ordered product `∏ i, X_i ^ a i` of coordinate generators. -/
def coordNCP (n : ℕ) (a : Fin n → ℕ) : PresentedWeyl k n :=
  Finset.univ.noncommProd
    (fun i => Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inl i) ^ a i)
    (fun i hi j hj hij => (presentedCoordGen_comm (k := k) n hi hj hij).pow_pow _ _)

/-- The ordered product `∏ i, ∂_i ^ p i` of momentum generators. -/
def momNCP (n : ℕ) (p : Fin n → ℕ) : PresentedWeyl k n :=
  Finset.univ.noncommProd
    (fun i => Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i) ^ p i)
    (fun i hi j hj hij => (presentedMomGen_comm (k := k) n hi hj hij).pow_pow _ _)

/-- **`presentedOrderedMonomial_eq_ncp`**: the recursively defined ordered monomial
`presentedOrderedMonomial k n a p` (`x^a * ∂^p`, coordinates on the left) equals the product of
the coordinate-generator and momentum-generator `noncommProd`s, proved by induction on `n`
mirroring the recursive definition and using `previousWeylEmbedding`'s compatibility with the
generators. -/
theorem presentedOrderedMonomial_eq_ncp (n : ℕ) (a p : Fin n → ℕ) :
    presentedOrderedMonomial k n a p = coordNCP (k := k) n a * momNCP (k := k) n p := by
  induction n with
  | zero =>
      simp [presentedOrderedMonomial, coordNCP, momNCP]
  | succ n ih =>
      set a' : Fin n → ℕ := fun i => a i.succ with ha'
      set p' : Fin n → ℕ := fun i => p i.succ with hp'
      have hsplitC := noncommProd_univ_succ
        (g := fun i : Fin (n + 1) =>
          Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl i) ^ a i)
        (fun i hi j hj hij => (presentedCoordGen_comm (k := k) (n + 1) hi hj hij).pow_pow _ _)
      have hsplitM := noncommProd_univ_succ
        (g := fun i : Fin (n + 1) =>
          Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr i) ^ p i)
        (fun i hi j hj hij => (presentedMomGen_comm (k := k) (n + 1) hi hj hij).pow_pow _ _)
      obtain ⟨commC, hC⟩ := hsplitC
      obtain ⟨commM, hM⟩ := hsplitM
      set shiftC : PresentedWeyl k (n + 1) :=
        Finset.univ.noncommProd
          (fun i : Fin n =>
            Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl i.succ) ^ a i.succ)
          commC with hshiftC
      set shiftM : PresentedWeyl k (n + 1) :=
        Finset.univ.noncommProd
          (fun i : Fin n =>
            Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr i.succ) ^ p i.succ)
          commM with hshiftM
      -- `previousWeylEmbedding` takes `coordNCP n a'` to `shiftC`, and `momNCP n p'` to `shiftM`.
      have hembC : previousWeylEmbedding k n (coordNCP (k := k) n a') = shiftC := by
        rw [coordNCP, map_noncommProd, hshiftC]
        apply Finset.noncommProd_congr rfl
        intro i _
        rw [map_pow, previousWeylEmbedding_generator]
        rfl
      have hembM : previousWeylEmbedding k n (momNCP (k := k) n p') = shiftM := by
        rw [momNCP, map_noncommProd, hshiftM]
        apply Finset.noncommProd_congr rfl
        intro i _
        rw [map_pow, previousWeylEmbedding_generator]
        rfl
      rw [presentedOrderedMonomial, ih a' p', map_mul, hembC, hembM]
      show shiftC * shiftM * presentedCoordinate k n ^ a 0 * presentedMomentum k n ^ p 0 = _
      have hXcoord :
          presentedCoordinate k n = Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k)
            (Sum.inl 0) := rfl
      have hPmom :
          presentedMomentum k n = Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k)
            (Sum.inr 0) := rfl
      have hCeq : coordNCP (k := k) (n + 1) a =
          Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl 0) ^ a 0 * shiftC := by
        show Finset.univ.noncommProd
          (fun i => Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl i) ^ a i) _ = _
        exact hC
      have hMeq : momNCP (k := k) (n + 1) p =
          Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr 0) ^ p 0 * shiftM := by
        show Finset.univ.noncommProd
          (fun i => Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr i) ^ p i) _ = _
        exact hM
      rw [hXcoord, hPmom, hCeq, hMeq]
      -- The two shifted products commute with the newest coordinate/momentum generator, except
      -- across a matching pair (avoided since `shiftC`/`shiftM` only use `i.succ ≠ 0`).
      have hcs : Commute shiftC
          (Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl (0 : Fin (n + 1))) ^
            a 0) := by
        apply Commute.pow_right
        rw [hshiftC]
        refine (Finset.noncommProd_commute _ _ _ _ ?_).symm
        intro i _
        exact ((presentedCoordGen_comm (k := k) (n + 1)
          (Finset.mem_univ (0 : Fin (n + 1))) (Finset.mem_univ i.succ)
          (Fin.succ_ne_zero i).symm)).pow_right _
      have hcp : Commute shiftC
          (Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr (0 : Fin (n + 1))) ^
            p 0) := by
        apply Commute.pow_right
        rw [hshiftC]
        refine (Finset.noncommProd_commute _ _ _ _ ?_).symm
        intro i _
        exact (presentedMomCoord_comm_ne (k := k) (n + 1) 0 i.succ
          (Fin.succ_ne_zero i).symm).pow_right _
      have hms : Commute shiftM
          (Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl (0 : Fin (n + 1))) ^
            a 0) := by
        apply Commute.pow_right
        rw [hshiftM]
        refine (Finset.noncommProd_commute _ _ _ _ ?_).symm
        intro i _
        exact (presentedCoordMom_comm_ne (k := k) (n + 1) 0 i.succ
          (Fin.succ_ne_zero i).symm).pow_right _
      have hmp : Commute shiftM
          (Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr (0 : Fin (n + 1))) ^
            p 0) := by
        apply Commute.pow_right
        rw [hshiftM]
        refine (Finset.noncommProd_commute _ _ _ _ ?_).symm
        intro i _
        exact ((presentedMomGen_comm (k := k) (n + 1)
          (Finset.mem_univ (0 : Fin (n + 1))) (Finset.mem_univ i.succ)
          (Fin.succ_ne_zero i).symm)).pow_right _
      calc shiftC * shiftM *
            Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl (0 : Fin (n + 1))) ^
              a 0 *
            Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr (0 : Fin (n + 1))) ^
              p 0
          = shiftC * (shiftM *
              Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl (0 : Fin (n + 1))) ^
                a 0) *
              Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr (0 : Fin (n + 1))) ^
                p 0 := by
              rw [mul_assoc shiftC shiftM]
        _ = shiftC * (Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k)
              (Sum.inl (0 : Fin (n + 1))) ^ a 0 * shiftM) *
              Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr (0 : Fin (n + 1))) ^
                p 0 := by
              rw [hms]
        _ = (shiftC * Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k)
              (Sum.inl (0 : Fin (n + 1))) ^ a 0) *
              (shiftM * Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k)
                (Sum.inr (0 : Fin (n + 1))) ^ p 0) := by
              simp only [mul_assoc]
        _ = (Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inl (0 : Fin (n + 1))) ^
              a 0 * shiftC) *
              (Stafford.freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (Sum.inr (0 : Fin (n + 1))) ^
                p 0 * shiftM) := by
              rw [hcs, hmp, mul_assoc]
        _ = _ := by
              rw [← hCeq, ← hMeq]

variable {n : ℕ} {C : Type u} [CommRing C] [IsDomain C]
  [Algebra k C] [Algebra (B k n) C] [IsScalarTower k (B k n) C]
  [Algebra.FormallyEtale (B k n) C]

/-! ## 4. `weylAction` of an ordered monomial -/

/-- `Operators.multiplicationD`, bundled as a `MonoidHom`. -/
def multiplicationDHom : C →* algebra (k := k) (R := C) where
  toFun := Operators.multiplicationD
  map_one' := Operators.multiplicationD_one
  map_mul' := fun a b => (Operators.multiplicationD_mul a b).symm

/-- **`weylAction_orderedMonomial`**: `weylAction E` sends the ordered monomial
`presentedOrderedMonomial k n a p` (`x^a * ∂^p`) to `multiplicationD(∏ x_i^{a i}) * partialMonomial p`,
provided `E`'s derivations are the lifted coordinate derivations (`hE`). -/
theorem weylAction_orderedMonomial (E : EtaleChartData k n C)
    (hE : ∀ i, E.«∂» i = liftDerivation i) (a p : Fin n → ℕ) :
    weylAction E (presentedOrderedMonomial k n a p) =
      Operators.multiplicationD (∏ i, xC k n C i ^ a i) *
        (⟨partialMonomial (Finsupp.equivFunOnFinite.symm p), partialMonomial_mem_algebra _⟩ :
          algebra (k := k) (R := C)) := by
  rw [presentedOrderedMonomial_eq_ncp, map_mul]
  congr 1
  · -- Coordinate factor: `weylAction E` of the coordinate-generator product is
    -- `multiplicationD (∏ i, x_i ^ a i)`, using `weylAction_X` and `C`'s commutativity.
    rw [coordNCP, map_noncommProd]
    have hcommD : ∀ x y : C, Commute (multiplicationDHom (k := k) (C := C) x)
        (multiplicationDHom (k := k) (C := C) y) := by
      intro x y
      show multiplicationDHom x * multiplicationDHom y = multiplicationDHom y * multiplicationDHom x
      rw [← map_mul, ← map_mul, mul_comm x y]
    have hthis : (Finset.univ : Finset (Fin n)).noncommProd
        (fun i => (weylAction E) (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inl i) ^
          a i))
        (fun i hi j hj hij =>
          (((presentedCoordGen_comm (k := k) n hi hj hij).pow_pow _ _)).map (weylAction E)) =
        (Finset.univ : Finset (Fin n)).noncommProd
        (fun i => multiplicationDHom (xC k n C i) ^ a i)
        (fun i hi j hj hij => (hcommD (xC k n C i) (xC k n C j)).pow_pow _ _) := by
      apply Finset.noncommProd_congr rfl
      intro i _
      rw [map_pow, weylAction_X]
      rfl
    rw [hthis]
    have hpow : ∀ i, multiplicationDHom (k := k) (C := C) (xC k n C i) ^ a i =
        multiplicationDHom (xC k n C i ^ a i) := fun i => by rw [← map_pow]
    simp only [hpow]
    rw [show (Finset.univ : Finset (Fin n)).noncommProd
      (fun i => multiplicationDHom (k := k) (C := C) (xC k n C i ^ a i)) _ =
      multiplicationDHom (Finset.univ.noncommProd (fun i => xC k n C i ^ a i)
        (fun i _ j _ _ => mul_comm _ _)) from
      (map_noncommProd _ _ _ multiplicationDHom).symm]
    congr 1
    rw [Finset.noncommProd_eq_prod]
    rfl
  · -- Momentum factor: `weylAction E` of the momentum-generator product coerces (via
    -- `Subalgebra.val`) to `partialMonomial p`, matching `partialMonomial`'s own definition
    -- termwise (using `hE`).
    apply Subtype.ext
    set ψ : PresentedWeyl k n →ₐ[k] Module.End k C :=
      (Subalgebra.val (algebra (k := k) (R := C))).comp (weylAction E) with hψ
    show (ψ (momNCP (k := k) n p) : Module.End k C) = _
    rw [momNCP]
    have hval := map_noncommProd (Finset.univ : Finset (Fin n))
      (fun i => Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i) ^ p i)
      (fun i hi j hj hij => (presentedMomGen_comm (k := k) n hi hj hij).pow_pow _ _)
      ψ
    rw [hval]
    show (Finset.univ : Finset (Fin n)).noncommProd
      (fun i => ψ (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i) ^ p i)) _ =
      partialMonomial (k := k) (C := C) (Finsupp.equivFunOnFinite.symm p)
    unfold partialMonomial
    apply Finset.noncommProd_congr rfl
    intro i _
    show (ψ (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i) ^ p i) :
      Module.End k C) = _
    rw [hψ, AlgHom.comp_apply, map_pow, Subalgebra.val_apply, weylAction_D]
    show (momentumGeneratorD E i : Module.End k C) ^ p i = _
    rw [coe_momentumGeneratorD, hE]
    rfl

/-! ## 5. Injectivity of `weylAction` -/

theorem monomial_one_eq_prod_X (α : Fin n →₀ ℕ) :
    MvPolynomial.monomial α (1 : k) = ∏ i, MvPolynomial.X i ^ α i := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

theorem algebraMap_monomial_one (α : Fin n →₀ ℕ) :
    algebraMap (B k n) C (MvPolynomial.monomial α (1 : k)) = ∏ i, xC k n C i ^ α i := by
  rw [monomial_one_eq_prod_X, map_prod (algebraMap (B k n) C)]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow]
  rfl

theorem algebraMap_smul_monomial (r : k) (α : Fin n →₀ ℕ) :
    algebraMap (B k n) C (r • MvPolynomial.monomial α (1 : k)) = r • ∏ i, xC k n C i ^ α i := by
  rw [Algebra.smul_def (R := k) (A := B k n), map_mul, algebraMap_monomial_one,
    show algebraMap (B k n) C (algebraMap k (B k n) r) = algebraMap k C r from
      (IsScalarTower.algebraMap_apply k (B k n) C r).symm,
    ← Algebra.smul_def]

/-- **`weylAction_injective`** (WP-18a): for an étale chart `E` whose derivations are the lifted
coordinate derivations of `Chart/EtaleDerivations.lean`, and whose coordinate ring `B k n → C` is
injective, `weylAction E : PresentedWeyl k n →ₐ[k] algebra k C` is injective. -/
theorem weylAction_injective (E : EtaleChartData k n C) (hE : ∀ i, E.«∂» i = liftDerivation i)
    (hinj : Function.Injective (algebraMap (B k n) C)) :
    Function.Injective (weylAction E) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  set c : (PhaseVar n →₀ ℕ) →₀ k := (presentedPBWBasis k n).repr z with hc
  have hzrepr : z = ∑ m ∈ c.support, c m • presentedPBWBasis k n m := by
    conv_lhs => rw [← (presentedPBWBasis k n).linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, ← hc]
  set g : (PhaseVar n →₀ ℕ) → (Fin n →₀ ℕ) :=
    fun m => Finsupp.equivFunOnFinite.symm (fun i => m (Sum.inr i)) with hg
  set t : Finset (Fin n →₀ ℕ) := c.support.image g with ht
  have hmaps : ∀ m ∈ c.support, g m ∈ t := fun m hm => Finset.mem_image_of_mem g hm
  set Q : (Fin n →₀ ℕ) → C :=
    fun j => ∑ m ∈ c.support with g m = j, c m • ∏ i, xC k n C i ^ m (Sum.inl i)
    with hQ
  have hsum0 : (weylAction E z : Module.End k C) = 0 := by rw [hz]; rfl
  have hexpand : (weylAction E z : Module.End k C) =
      ∑ j ∈ t, Q j • partialMonomial (k := k) (C := C) j := by
    rw [hzrepr]
    simp only [map_sum, map_smul, AddSubmonoidClass.coe_finsetSum]
    have hterm : ∀ m ∈ c.support,
        ((c m • weylAction E (presentedPBWBasis k n m) : algebra (k := k) (R := C)) :
            Module.End k C) =
          (c m • ∏ i, xC k n C i ^ m (Sum.inl i)) •
            partialMonomial (k := k) (C := C) (g m) := by
      intro m _
      rw [presentedPBWBasis_apply, weylAction_orderedMonomial (E := E) (hE := hE)]
      have hgm : (g m : Fin n →₀ ℕ) = Finsupp.equivFunOnFinite.symm (fun i => m (Sum.inr i)) :=
        rfl
      rw [← hgm]
      apply LinearMap.ext
      intro x
      simp only [Subalgebra.coe_smul, Subalgebra.coe_mul, Operators.coe_multiplicationD,
        Module.End.mul_apply, LinearMap.smul_apply, multiplication_apply,
        Algebra.smul_def (R := k) (A := C)]
      ring
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun m => (c m • ∏ i, xC k n C i ^ m (Sum.inl i)) •
        partialMonomial (k := k) (C := C) (g m))]
    apply Finset.sum_congr rfl
    intro j _
    rw [hQ, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [hm.2]
  rw [hsum0] at hexpand
  have hQzero : ∀ j ∈ t, Q j = 0 :=
    (linearIndependent_iff'.mp (linearIndependent_partialMonomial (k := k) (C := C)))
      t Q hexpand.symm
  have hcm0 : ∀ m ∈ c.support, c m = 0 := by
    intro m0 hm0
    have hj := hQzero (g m0) (hmaps m0 hm0)
    rw [hQ] at hj
    have hpoly : (algebraMap (B k n) C)
        (∑ m ∈ c.support with g m = g m0,
          c m • MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => m (Sum.inl i)))
            (1 : k)) = 0 := by
      rw [map_sum, ← hj]
      apply Finset.sum_congr rfl
      intro m _
      exact algebraMap_smul_monomial (c m) _
    have hpoly0 : (∑ m ∈ c.support with g m = g m0,
        c m • MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => m (Sum.inl i)))
          (1 : k)) = 0 :=
      hinj (by rw [hpoly, map_zero])
    have hcoeff := congrArg (MvPolynomial.coeff
      (Finsupp.equivFunOnFinite.symm (fun i => m0 (Sum.inl i)))) hpoly0
    rw [MvPolynomial.coeff_sum] at hcoeff
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul] at hcoeff
    rw [Finset.sum_eq_single m0] at hcoeff
    · simpa using hcoeff
    · intro m hm hne
      rw [Finset.mem_filter] at hm
      have hane : (Finsupp.equivFunOnFinite.symm (fun i => m (Sum.inl i)) :
          Fin n →₀ ℕ) ≠ Finsupp.equivFunOnFinite.symm (fun i => m0 (Sum.inl i)) := by
        intro heq
        apply hne
        have haeq : (fun i => m (Sum.inl i)) = (fun i => m0 (Sum.inl i)) := by
          have := congrArg (DFunLike.coe (α := Fin n) (β := fun _ => ℕ)) heq
          simpa using this
        have hpeq : g m = g m0 := hm.2
        have hgeq : (fun i => m (Sum.inr i)) = (fun i => m0 (Sum.inr i)) := by
          have := congrArg (DFunLike.coe (α := Fin n) (β := fun _ => ℕ)) hpeq
          simpa [hg, Finsupp.equivFunOnFinite] using this
        ext i
        cases i with
        | inl i => exact congrFun haeq i
        | inr i => exact congrFun hgeq i
      simp [hane]
    · intro hcontra
      exact (hcontra (Finset.mem_filter.mpr ⟨hm0, rfl⟩)).elim
  have hc0 : c = 0 := by
    ext m
    by_cases hm : m ∈ c.support
    · simpa using hcm0 m hm
    · simpa using Finsupp.notMem_support_iff.mp hm
  have hz0 : (presentedPBWBasis k n).repr z = 0 := hc0
  exact (presentedPBWBasis k n).repr.injective (by rw [hz0]; simp)

end
end GlobalStafford.Chart

#print axioms GlobalStafford.Chart.presentedOrderedMonomial_eq_ncp
#print axioms GlobalStafford.Chart.weylAction_orderedMonomial
#print axioms GlobalStafford.Chart.weylAction_injective
