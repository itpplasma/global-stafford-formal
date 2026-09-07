import GlobalStafford.Operators.Basic
import GlobalStafford.Chart.FiniteRankAscent
import AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration
import Stafford38.Weyl.Universal
import Stafford38.Weyl.IteratedEquivalence
import Stafford38.FoundationClosure
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Étale chart data, Weyl action, and chart S38 (Lemma 6.1 / Lemma 6.2, chart case)

`PLAN.md` §1 Section 6, work package WP-8 (`Chart/EtaleChartData.lean`). Packages
the geometric data of an integral affine `C` étale over `B = k[x_1,…,x_n]` (the
`n` coordinate derivations `«∂»_i`, coordinate rigidity, finiteness of the generic
fibre, and `D_k(C)` being a domain) into `EtaleChartData`, constructs the induced
action `weylAction` of the presented rank-`n` Weyl algebra `T = A_n(k)` on
`D_k(C)` (mirroring `Stafford38.LocalizedWeylAction`), and proves Lemma 6.1
(`finiteRightSpan_weylAction`, via
`AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration.mem_submodule_of_coordinates'`)
and its two consequences: the two-generator identity `S38` transfers from `T` to
`D_k(C)` (`twoGeneratorIdentity_chart`, and `twoGeneratorIdentity_chart_of_weyl`
using `Stafford38.universalStatement`), and the right Ore condition transfers as
well (`rightOre_chart`).
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators
open AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration
open Stafford38.WeylUniversal Stafford38.WeylIteratedEquivalence
open scoped nonZeroDivisors

noncomputable section

universe u

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-- The coordinate polynomial ring `k[x_1,…,x_n]`. -/
abbrev B : Type u := MvPolynomial (Fin n) k

variable (C : Type u) [CommRing C] [Nontrivial C] [Algebra k C]
  [Algebra (B k n) C] [IsScalarTower k (B k n) C]

/-- The image of the coordinate `x_i` in `C`. -/
def xC (i : Fin n) : C := algebraMap (B k n) C (MvPolynomial.X i)

/-- The presented rank-`n` Weyl algebra `A_n(k)`. -/
abbrev T : Type u := PresentedWeyl k n

/-- Data for an integral affine `C`, étale over `B = k[x_1,…,x_n]` (`PLAN.md`
Section 6, "chart input"): a family of `n` commuting `k`-derivations `«∂»_i` of
`C` dual to the coordinates `x_i`, coordinate rigidity for finite-order
operators, finiteness of the generic fibre up to a nonzero coefficient of `B`,
injectivity of `B → C` on nonzero elements, and `D_k(C)` being a domain. -/
structure EtaleChartData where
  /-- The `n` coordinate derivations. -/
  «∂» : Fin n → Derivation k C C
  /-- `«∂»_i` is dual to the coordinate `x_j`. -/
  «∂_coord» : ∀ i j, «∂» i (xC k n C j) = if i = j then 1 else 0
  /-- The coordinate derivations commute. -/
  «∂_comm» : ∀ i j, («∂» i).toLinearMap * («∂» j).toLinearMap = («∂» j).toLinearMap * («∂» i).toLinearMap
  /-- A finite-order operator commuting with every coordinate is a multiplication
  operator. -/
  coordinateRigidity : ∀ P : Module.End k C, P ∈ algebra (k := k) (R := C) →
      (∀ i, commutator P (xC k n C i) = 0) → P = multiplication (P 1)
  /-- The generic fibre `C ⊗_B Frac(B)` is finitely generated: every `x : C`
  becomes a finite `C`-combination of finitely many fixed elements `c i` after
  clearing a nonzero coefficient of `B` on the left. -/
  finiteGenericFibre : ∃ (m : ℕ) (c : Fin m → C), ∀ x : C, ∃ b : B k n, b ≠ 0 ∧
      ∃ t : Fin m → B k n, algebraMap (B k n) C b * x = ∑ i, c i * algebraMap (B k n) C (t i)
  /-- `B → C` is injective on nonzero elements. -/
  algebraMap_ne_zero : ∀ b : B k n, b ≠ 0 → algebraMap (B k n) C b ≠ 0
  /-- `D_k(C)` is a domain. -/
  noZeroDivisors : NoZeroDivisors (algebra (k := k) (R := C))

variable {k n C}

/-- The `k`-linear endomorphism of `C` given by multiplication by `x_i`, packaged
as an order-zero operator of `D_k(C)`. -/
def coordinateGeneratorD (i : Fin n) : algebra (k := k) (R := C) :=
  Operators.multiplicationD (xC k n C i)

theorem momentumGenerator_mem_order_one (E : EtaleChartData k n C) (i : Fin n) :
    (E.«∂» i).toLinearMap ∈ order (k := k) (R := C) 1 := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, mem_order_succ_iff]
  intro a
  rw [mem_order_zero_iff_eq_multiplication]
  apply LinearMap.ext
  intro x
  change (E.«∂» i) (a * x) - a * (E.«∂» i) x = _
  rw [(E.«∂» i).leibniz]
  simp [multiplication_apply, mul_comm, add_comm]

/-- The momentum generator `«∂»_i`, packaged as an order-one operator of
`D_k(C)`. -/
def momentumGeneratorD (E : EtaleChartData k n C) (i : Fin n) : algebra (k := k) (R := C) :=
  ⟨(E.«∂» i).toLinearMap, 1, momentumGenerator_mem_order_one E i⟩

/-- The joint family of coordinate and momentum generators of `D_k(C)`, indexed
by `Fin n ⊕ Fin n` (mirroring `Stafford38.LocalizedWeylAction.differentialGenerator`). -/
def differentialGenerator (E : EtaleChartData k n C) :
    (Fin n ⊕ Fin n) → algebra (k := k) (R := C)
  | .inl i => coordinateGeneratorD i
  | .inr i => momentumGeneratorD E i

@[simp] theorem coe_coordinateGeneratorD (i : Fin n) :
    (coordinateGeneratorD (k := k) (n := n) (C := C) i : Module.End k C) =
      multiplication (xC k n C i) := rfl

@[simp] theorem coe_momentumGeneratorD (E : EtaleChartData k n C) (i : Fin n) :
    (momentumGeneratorD E i : Module.End k C) = (E.«∂» i).toLinearMap := rfl

theorem differentialGenerator_commutator (E : EtaleChartData k n C)
    (i j : Fin n ⊕ Fin n) :
    Stafford.commutator (differentialGenerator E i) (differentialGenerator E j) =
      algebraMap k (algebra (k := k) (R := C)) (Matrix.J (Fin n) k i j) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  rcases i with i | i <;> rcases j with j | j
  · -- coordinate, coordinate
    simp [Stafford.commutator, differentialGenerator, Subalgebra.coe_algebraMap,
      Module.End.mul_apply, Matrix.J, multiplication_apply, mul_comm, mul_assoc,
      mul_left_comm]
  · -- coordinate i, momentum j
    by_cases h : i = j
    · subst h
      have hd := E.«∂_coord» i i
      simp only [if_pos rfl] at hd
      simp [Stafford.commutator, differentialGenerator, Subalgebra.coe_algebraMap,
        Module.End.mul_apply, Matrix.J, multiplication_apply,
        Derivation.leibniz, hd, mul_comm]
    · have hd := E.«∂_coord» j i
      simp only [if_neg (Ne.symm h)] at hd
      simp [Stafford.commutator, differentialGenerator, Subalgebra.coe_algebraMap,
        Module.End.mul_apply, Matrix.J, multiplication_apply,
        Derivation.leibniz, hd, h, Ne.symm h, mul_comm]
  · -- momentum i, coordinate j
    by_cases h : i = j
    · subst j
      have hd := E.«∂_coord» i i
      simp only [if_pos rfl] at hd
      simp [Stafford.commutator, differentialGenerator, Subalgebra.coe_algebraMap,
        Module.End.mul_apply, Matrix.J, multiplication_apply,
        Derivation.leibniz, hd, mul_comm]
    · have hd := E.«∂_coord» i j
      simp only [if_neg h] at hd
      simp [Stafford.commutator, differentialGenerator, Subalgebra.coe_algebraMap,
        Module.End.mul_apply, Matrix.J, multiplication_apply,
        Derivation.leibniz, hd, h, Ne.symm h, mul_comm]
  · -- momentum, momentum
    have hc := E.«∂_comm» i j
    have hcf := LinearMap.congr_fun hc f
    simpa [Stafford.commutator, differentialGenerator, Subalgebra.coe_algebraMap,
      Module.End.mul_apply, Matrix.J] using (sub_eq_zero.mpr hcf)

/-- **Lemma 6.2 input**: the action of the presented rank-`n` Weyl algebra on
`D_k(C)` induced by the coordinate and momentum generators (mirroring
`Stafford38.LocalizedWeylAction.localizedWeylAction`). -/
def weylAction (E : EtaleChartData k n C) :
    PresentedWeyl k n →ₐ[k] algebra (k := k) (R := C) :=
  freeWeylLift (Matrix.J (Fin n) k) (differentialGenerator E)
    (differentialGenerator_commutator E)

@[simp] theorem weylAction_X (E : EtaleChartData k n C) (i : Fin n) :
    weylAction E (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inl i)) =
      coordinateGeneratorD i :=
  freeWeylLift_generator _ _ _ (Sum.inl i)

@[simp] theorem weylAction_D (E : EtaleChartData k n C) (i : Fin n) :
    weylAction E (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i)) =
      momentumGeneratorD E i :=
  freeWeylLift_generator _ _ _ (Sum.inr i)

/-- Raw multiplication operators distribute over finite sums. -/
theorem multiplication_finsetSum {ι : Type*} (s : Finset ι) (a : ι → C) :
    multiplication (k := k) (∑ i ∈ s, a i) = ∑ i ∈ s, multiplication (k := k) (a i) := by
  classical
  induction s using Finset.induction with
  | empty => ext z; simp [multiplication_apply]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]
      ext z; simp [multiplication_apply, add_mul]

/-- `MvPolynomial.aeval` needs a *commutative* codomain and `PresentedWeyl k n` is
not commutative, so `polynomialToWeyl` cannot be built as a bundled algebra map
(unlike the plan sketch); instead we prove directly, by induction on `b` exactly
as in `Stafford38.LocalizedWeylAction.multiplication_algebraMap_mem_range`, that
every multiplication operator with a `B`-coefficient is *some* value of
`weylAction E`. This is all `finiteRightSpan_weylAction` needs. -/
theorem multiplicationD_algebraMap (c : k) :
    Operators.multiplicationD (k := k) (A := C) (algebraMap k C c) =
      algebraMap k (algebra (k := k) (R := C)) c := by
  apply Subtype.ext
  rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]
  ext x
  simp [Operators.multiplicationD, multiplication_apply, Algebra.smul_def]

/-- **Lemma 6.2 input**: every multiplication operator by (the image of) an
element `b : B` lies in the range of `weylAction E`. -/
theorem exists_weylAction_eq_multiplicationD (E : EtaleChartData k n C) (b : B k n) :
    ∃ τ : PresentedWeyl k n,
      weylAction E τ = Operators.multiplicationD (algebraMap (B k n) C b) := by
  induction b using MvPolynomial.induction_on with
  | C c =>
      have hcB : algebraMap (B k n) C (MvPolynomial.C c) = algebraMap k C c := by
        calc
          algebraMap (B k n) C (MvPolynomial.C c)
              = algebraMap (B k n) C (algebraMap k (B k n) c) := by
                rw [MvPolynomial.algebraMap_eq]
          _ = algebraMap k C c := (IsScalarTower.algebraMap_apply k (B k n) C c).symm
      refine ⟨algebraMap k (PresentedWeyl k n) c, ?_⟩
      rw [hcB, AlgHom.commutes, multiplicationD_algebraMap]
  | add f g hf hg =>
      obtain ⟨τf, hτf⟩ := hf
      obtain ⟨τg, hτg⟩ := hg
      refine ⟨τf + τg, ?_⟩
      rw [map_add, hτf, hτg, ← Operators.multiplicationD_add, ← map_add]
  | mul_X f i hf =>
      obtain ⟨τf, hτf⟩ := hf
      refine ⟨τf * Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inl i), ?_⟩
      rw [map_mul, hτf, weylAction_X, coordinateGeneratorD, Operators.multiplicationD_mul]
      congr 1
      show algebraMap (B k n) C f * xC k n C i = algebraMap (B k n) C (f * MvPolynomial.X i)
      rw [map_mul, xC]

/-- The right Ore condition on `T = PresentedWeyl k n`, specialised from
`rightOre_of_oreSet`. -/
theorem weyl_rightOre [Nontrivial (PresentedWeyl k n)] [NoZeroDivisors (PresentedWeyl k n)]
    [OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰] :
    ∀ τ₁ τ₂ : PresentedWeyl k n, τ₁ ≠ 0 → τ₂ ≠ 0 →
      ∃ σ₁ σ₂ : PresentedWeyl k n, σ₁ ≠ 0 ∧ τ₁ * σ₁ = τ₂ * σ₂ :=
  rightOre_of_oreSet

/-- The presented rank-`n` Weyl algebra is nontrivial whenever it maps, by an
algebra homomorphism, into a nontrivial ring (here `D_k(C)`, nontrivial because
`C` is). -/
theorem nontrivial_presentedWeyl_of_weylAction (E : EtaleChartData k n C) :
    Nontrivial (PresentedWeyl k n) :=
  domain_nontrivial (fun z => ((weylAction E z : algebra (k := k) (R := C)) : Module.End k C))
    (by simp) (by simp)

theorem momentumGenerator_weyl_ne_zero (E : EtaleChartData k n C) (i : Fin n) :
    (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i) : PresentedWeyl k n) ≠ 0 := by
  intro h
  have hval : ((E.«∂» i).toLinearMap) = (0 : Module.End k C) := by
    have := congrArg (fun z => ((weylAction E z : algebra (k := k) (R := C)) : Module.End k C)) h
    simpa using this
  have h1 : (E.«∂» i) (xC k n C i) = 0 := by
    have := congrFun (congrArg (DFunLike.coe (α := C) (β := fun _ => C)) hval) (xC k n C i)
    simpa using this
  have h2 : (E.«∂» i) (xC k n C i) = 1 := by
    have := E.«∂_coord» i i
    simpa using this
  rw [h2] at h1
  exact one_ne_zero h1

/-- **Lemma 6.1** for étale chart data: `D_k(C)`, as a right `T`-module through
`weylAction E`, is finitely spanned by the multiplication operators `c i`
witnessing `finiteGenericFibre`. -/
theorem finiteRightSpan_weylAction [OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰]
    [NoZeroDivisors (PresentedWeyl k n)] (E : EtaleChartData k n C) :
    FiniteRightSpan (T := PresentedWeyl k n) (S := algebra (k := k) (R := C))
      (weylAction E).toRingHom := by
  classical
  have := nontrivial_presentedWeyl_of_weylAction E
  obtain ⟨m, c, hfibre⟩ := E.finiteGenericFibre
  set φ : PresentedWeyl k n →+* algebra (k := k) (R := C) := (weylAction E).toRingHom with hφ
  have hφapp : ∀ τ, (φ τ : Module.End k C) = (weylAction E τ : Module.End k C) := fun _ => rfl
  let Hcarrier : Set (Module.End k C) := {P | ∃ τ : PresentedWeyl k n, τ ≠ 0 ∧
      ∃ t : Fin m → PresentedWeyl k n,
        P * (φ τ : Module.End k C) =
          ∑ i, multiplication (c i) * (φ (t i) : Module.End k C)}
  have hzero : (0 : Module.End k C) ∈ Hcarrier := by
    refine ⟨1, one_ne_zero, fun _ => 0, ?_⟩
    simp
  have hadd : ∀ P Q, P ∈ Hcarrier → Q ∈ Hcarrier → P + Q ∈ Hcarrier := by
    rintro P Q ⟨τ, hτ, t, ht⟩ ⟨τ', hτ', t', ht'⟩
    obtain ⟨σ₁, σ₂, hσ₁, hστ⟩ := weyl_rightOre τ τ' hτ hτ'
    refine ⟨τ * σ₁, mul_ne_zero hτ hσ₁, fun i => t i * σ₁ + t' i * σ₂, ?_⟩
    calc
      (P + Q) * (φ (τ * σ₁) : Module.End k C)
          = P * (φ (τ * σ₁) : Module.End k C) + Q * (φ (τ * σ₁) : Module.End k C) := by
            rw [add_mul]
      _ = P * ((φ τ : Module.End k C) * (φ σ₁ : Module.End k C)) +
            Q * ((φ τ' : Module.End k C) * (φ σ₂ : Module.End k C)) := by
            congr 1
            · rw [map_mul]; rfl
            · rw [hστ, map_mul]; rfl
      _ = (P * (φ τ : Module.End k C)) * (φ σ₁ : Module.End k C) +
            (Q * (φ τ' : Module.End k C)) * (φ σ₂ : Module.End k C) := by
            rw [mul_assoc, mul_assoc]
      _ = (∑ i, multiplication (c i) * (φ (t i) : Module.End k C)) * (φ σ₁ : Module.End k C) +
            (∑ i, multiplication (c i) * (φ (t' i) : Module.End k C)) * (φ σ₂ : Module.End k C) := by
            rw [ht, ht']
      _ = ∑ i, multiplication (c i) * ((φ (t i) : Module.End k C) * (φ σ₁ : Module.End k C)) +
            ∑ i, multiplication (c i) * ((φ (t' i) : Module.End k C) * (φ σ₂ : Module.End k C)) := by
            simp only [Finset.sum_mul, mul_assoc]
      _ = ∑ i, multiplication (c i) * (φ (t i * σ₁) : Module.End k C) +
            ∑ i, multiplication (c i) * (φ (t' i * σ₂) : Module.End k C) := by
            congr 1 <;> · apply Finset.sum_congr rfl; intro i _
                          congr 1; rw [map_mul]; rfl
      _ = ∑ i, multiplication (c i) * (φ (t i * σ₁ + t' i * σ₂) : Module.End k C) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            rw [map_add]
            show _ = multiplication (c i) *
              ((φ (t i * σ₁) : Module.End k C) + (φ (t' i * σ₂) : Module.End k C))
            rw [mul_add]
  have hsmul : ∀ (r : k) P, P ∈ Hcarrier → r • P ∈ Hcarrier := by
    rintro r P ⟨τ, hτ, t, ht⟩
    refine ⟨τ, hτ, fun i => r • t i, ?_⟩
    calc
      (r • P) * (φ τ : Module.End k C) = r • (P * (φ τ : Module.End k C)) := by
        rw [smul_mul_assoc]
      _ = r • (∑ i, multiplication (c i) * (φ (t i) : Module.End k C)) := by rw [ht]
      _ = ∑ i, r • (multiplication (c i) * (φ (t i) : Module.End k C)) := by
        rw [Finset.smul_sum]
      _ = ∑ i, multiplication (c i) * (r • (φ (t i) : Module.End k C)) := by
        apply Finset.sum_congr rfl; intro i _; rw [mul_smul_comm]
      _ = ∑ i, multiplication (c i) * (φ (r • t i) : Module.End k C) := by
        apply Finset.sum_congr rfl; intro i _
        congr 1
        show r • (weylAction E (t i) : Module.End k C) =
          ((weylAction E (r • t i) : algebra (k := k) (R := C)) : Module.End k C)
        rw [map_smul]
        rfl
  let H : Submodule k (Module.End k C) :=
    { carrier := Hcarrier
      zero_mem' := hzero
      add_mem' := fun {P Q} hP hQ => hadd P Q hP hQ
      smul_mem' := fun r {P} hP => hsmul r P hP }
  have hmul : ∀ x : C, multiplication (k := k) x ∈ H := by
    intro x
    obtain ⟨b, hb, t, hbx⟩ := hfibre x
    have hbne : Operators.multiplicationD (k := k) (A := C)
        (algebraMap (B k n) C b) ≠ 0 := by
      intro h0
      have := congrArg (fun P => (P : algebra (k := k) (R := C)).val 1) h0
      simp only [Operators.multiplicationD] at this
      simp [multiplication_apply] at this
      exact E.algebraMap_ne_zero b hb this
    obtain ⟨τ, hτ⟩ := exists_weylAction_eq_multiplicationD E b
    choose t' ht' using fun i => exists_weylAction_eq_multiplicationD E (t i)
    refine ⟨τ, ?_, t', ?_⟩
    · intro h0
      apply hbne
      rw [← hτ, h0, map_zero]
    · have hφb : (φ τ : Module.End k C) = multiplication (algebraMap (B k n) C b) := by
        rw [hφapp, hτ]; rfl
      have hφt : ∀ i, (φ (t' i) : Module.End k C) =
          multiplication (algebraMap (B k n) C (t i)) := by
        intro i
        rw [hφapp, ht' i]; rfl
      rw [hφb]
      have hmulmul : multiplication (k := k) x *
          multiplication (k := k) (algebraMap (B k n) C b) =
          multiplication (k := k) (x * algebraMap (B k n) C b) := by
        ext z; simp [multiplication_apply, mul_assoc]
      rw [hmulmul, mul_comm x, hbx]
      rw [multiplication_finsetSum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hφt i]
      ext z
      simp [multiplication_apply, mul_assoc]
  have hright : ∀ i (Q : Module.End k C), Q ∈ H → Q * (E.«∂» i).toLinearMap ∈ H := by
    rintro i Q ⟨τ, hτ, t, ht⟩
    have hine : (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i) : PresentedWeyl k n) ≠ 0 :=
      momentumGenerator_weyl_ne_zero E i
    obtain ⟨σ₁, σ₂, hσ₁, hστ⟩ :=
      weyl_rightOre (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i)) τ hine hτ
    refine ⟨σ₁, hσ₁, fun j => t j * σ₂, ?_⟩
    have hD : (E.«∂» i).toLinearMap =
        (φ (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i)) : Module.End k C) := by
      rw [hφapp, weylAction_D]; rfl
    calc
      Q * (E.«∂» i).toLinearMap * (φ σ₁ : Module.End k C)
          = Q * ((E.«∂» i).toLinearMap * (φ σ₁ : Module.End k C)) := by rw [mul_assoc]
      _ = Q * ((φ (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i)) : Module.End k C) *
            (φ σ₁ : Module.End k C)) := by rw [hD]
      _ = Q * (φ (Stafford.freeWeylGenerator (Matrix.J (Fin n) k) (Sum.inr i) * σ₁) : Module.End k C) := by
            rw [map_mul]; rfl
      _ = Q * (φ (τ * σ₂) : Module.End k C) := by rw [hστ]
      _ = Q * ((φ τ : Module.End k C) * (φ σ₂ : Module.End k C)) := by
            rw [map_mul]; rfl
      _ = (Q * (φ τ : Module.End k C)) * (φ σ₂ : Module.End k C) := by rw [mul_assoc]
      _ = (∑ i, multiplication (c i) * (φ (t i) : Module.End k C)) * (φ σ₂ : Module.End k C) := by
            rw [ht]
      _ = ∑ i_1, multiplication (c i_1) *
            ((φ (t i_1) : Module.End k C) * (φ σ₂ : Module.End k C)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro j _; rw [mul_assoc]
      _ = ∑ i_1, multiplication (c i_1) * (φ (t i_1 * σ₂) : Module.End k C) := by
            apply Finset.sum_congr rfl; intro j _
            congr 1; rw [map_mul]; rfl
  refine ⟨m, fun i => Operators.multiplicationD (c i), ?_⟩
  intro x
  have hmem : (x : Module.End k C) ∈ H :=
    mem_submodule_of_coordinates' (xC k n C) E.«∂» E.«∂_coord»
      (fun P hP h => E.coordinateRigidity P hP h) H hmul hright x.val x.property
  obtain ⟨τ, hτ, t, ht⟩ := hmem
  refine ⟨τ, hτ, t, ?_⟩
  apply Subtype.ext
  show (x : Module.End k C) * (φ τ : Module.End k C) =
    (∑ i, Operators.multiplicationD (c i) * φ (t i) : algebra (k := k) (R := C)).val
  rw [ht]
  rw [Submodule.coe_sum (p := (algebra (k := k) (R := C)).toSubmodule)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Subalgebra.coe_mul, Operators.coe_multiplicationD]

/-- **Lemma 6.2, chart case**: `S38` transfers from `T = A_n(k)` to `D_k(C)`. -/
theorem twoGeneratorIdentity_chart [OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰]
    [NoZeroDivisors (PresentedWeyl k n)] (E : EtaleChartData k n C)
    (hW : AlgebraicAnalysis.TwoGeneratorIdentity (PresentedWeyl k n)) :
    AlgebraicAnalysis.TwoGeneratorIdentity (algebra (k := k) (R := C)) := by
  have := nontrivial_presentedWeyl_of_weylAction E
  have := E.noZeroDivisors
  exact twoGeneratorIdentity_of_finiteRightSpan (finiteRightSpan_weylAction E) hW

/-- **Lemma 6.2, chart case, from the universal Stafford 3.8 statement**: `S38`
holds for `D_k(C)` for every étale chart, using `Stafford38.universalStatement`
directly. -/
theorem twoGeneratorIdentity_chart_of_weyl
    [OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰]
    [NoZeroDivisors (PresentedWeyl k n)] (E : EtaleChartData k n C) :
    AlgebraicAnalysis.TwoGeneratorIdentity (algebra (k := k) (R := C)) :=
  twoGeneratorIdentity_chart E (Stafford38.universalStatement.{u} k n)

/-- **Lemma 6.1, right-Ore transfer, chart case**: the right Ore condition
transfers from `T = A_n(k)` to `D_k(C)`, given injectivity of `weylAction E`. -/
theorem rightOre_chart [OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰]
    [NoZeroDivisors (PresentedWeyl k n)] (E : EtaleChartData k n C)
    (hinj : Function.Injective (weylAction E)) :
    ∀ x y : algebra (k := k) (R := C), x ≠ 0 → y ≠ 0 → ∃ a b, a ≠ 0 ∧ x * a = y * b := by
  have := nontrivial_presentedWeyl_of_weylAction E
  have := E.noZeroDivisors
  exact rightOre_of_finiteRightSpan (finiteRightSpan_weylAction E) hinj

end
end GlobalStafford.Chart

#print axioms GlobalStafford.Chart.finiteRightSpan_weylAction
#print axioms GlobalStafford.Chart.twoGeneratorIdentity_chart
#print axioms GlobalStafford.Chart.twoGeneratorIdentity_chart_of_weyl
#print axioms GlobalStafford.Chart.rightOre_chart
