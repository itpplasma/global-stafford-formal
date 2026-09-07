import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import AlgebraicAnalysis.Module.RankTorsion
import AlgebraicAnalysis.Ore.Localization
import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity

/-!
# Finite-right-span ascent (Lemma 6.1)

`PLAN.md` §1 Section 6, Lemma 6.1: if `S` is spanned as a right `T`-module (via a ring
homomorphism `φ : T →+* S`) by finitely many elements of `S`, up to clearing a nonzero
denominator through `φ`, then every nonzero `d ∈ S` admits `y ∈ S`, `a ∈ T` nonzero with
`d * y = φ a`. Consequently the two-generator identity (`S38`) transfers from `T` to `S`
(`twoGeneratorIdentity_of_finiteRightSpan`), and the right Ore condition transfers from
`T` to `S` as well (`rightOre_of_finiteRightSpan`), using the right Ore condition
witnessed for `T` by `[OreLocalization.OreSet (Tᵐᵒᵖ)⁰]` (`rightOre_of_oreSet`).

Proof of the finite-rank-ascent theorem, following Handover Packet 2
(`AlgebraicAnalysis.Module.RankTorsion`): `S` is regarded as a left `Tᵐᵒᵖ`-module `M`
(`RightModule φ`, a one-field wrapper structure around `S`) via `op τ • x := x * φ τ`, the
standard opposite-module encoding of a right module; `M` is localized to a vector space
`V` over the division ring `Q := FractionRingOp T`. `FiniteRightSpan` makes `V`
finite-dimensional over `Q` (`Module.Finite`); left multiplication by `d` is
`Tᵐᵒᵖ`-linear on `M`, hence extends to a `Q`-linear endomorphism `Ld` of `V`; `Ld` is
injective because `d ≠ 0` and `S` has no zero divisors, hence (finite dimension)
surjective; unwinding a preimage of `1 /ₒ 1` produces the required `y, a`.
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.RankTorsion OreLocalization
open scoped nonZeroDivisors

variable {T S : Type*} [Ring T] [Nontrivial T] [NoZeroDivisors T]
  [OreLocalization.OreSet (Tᵐᵒᵖ)⁰] [Ring S] [Nontrivial S] [NoZeroDivisors S]

/-- `S` is spanned, as a right `T`-module through `φ`, by finitely many elements
`s : Fin m → S`: every `x : S` becomes a right `T`-combination of the `s i` after
clearing a nonzero denominator `τ ∈ T` on the right through `φ`. -/
def FiniteRightSpan (φ : T →+* S) : Prop :=
  ∃ (m : ℕ) (s : Fin m → S), ∀ x : S, ∃ τ : T, τ ≠ 0 ∧ ∃ t : Fin m → T,
    x * φ τ = ∑ i, s i * φ (t i)

section Construction

variable (φ : T →+* S)

/-- `S`, regarded as a left `Tᵐᵒᵖ`-module via `op τ • x := x * φ τ`: the standard
opposite-module encoding of the right `T`-module structure that `φ` induces on `S`. A
one-field wrapper around `S`, so that this module structure does not clash with the ring
structure already carried by `S`. -/
structure RightModule (φ : T →+* S) : Type _ where
  /-- The underlying element of `S`. -/
  v : S

namespace RightModule

@[ext] lemma ext {x y : RightModule φ} (h : x.v = y.v) : x = y := by
  cases x; cases y; cases h; rfl

instance : Add (RightModule φ) := ⟨fun x y => ⟨x.v + y.v⟩⟩
instance : Zero (RightModule φ) := ⟨⟨0⟩⟩
instance : Neg (RightModule φ) := ⟨fun x => ⟨-x.v⟩⟩
instance : Sub (RightModule φ) := ⟨fun x y => ⟨x.v - y.v⟩⟩

@[simp] lemma add_v (x y : RightModule φ) : (x + y).v = x.v + y.v := rfl
@[simp] lemma zero_v : (0 : RightModule φ).v = 0 := rfl
@[simp] lemma neg_v (x : RightModule φ) : (-x).v = -x.v := rfl
@[simp] lemma sub_v (x y : RightModule φ) : (x - y).v = x.v - y.v := rfl

instance : AddCommGroup (RightModule φ) where
  add_assoc x y z := by ext; simp [add_assoc]
  zero_add x := by ext; simp
  add_zero x := by ext; simp
  neg_add_cancel x := by ext; simp
  add_comm x y := by ext; simp [add_comm]
  sub_eq_add_neg x y := by ext; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : SMul Tᵐᵒᵖ (RightModule φ) := ⟨fun τ x => ⟨x.v * φ τ.unop⟩⟩

@[simp] lemma smul_v (τ : Tᵐᵒᵖ) (x : RightModule φ) : (τ • x).v = x.v * φ τ.unop := rfl

instance : Module Tᵐᵒᵖ (RightModule φ) where
  one_smul x := by ext; simp
  mul_smul a b x := by ext; simp [MulOpposite.unop_mul, map_mul, mul_assoc]
  smul_zero τ := by ext; simp
  smul_add τ x y := by ext; simp [add_mul]
  add_smul a b x := by ext; simp [MulOpposite.unop_add, map_add, mul_add]
  zero_smul x := by ext; simp

end RightModule

/-- The division ring of fractions of `Tᵐᵒᵖ`, over which the localized module of part
(a) is a vector space. -/
noncomputable abbrev Q (T : Type*) [Ring T] [Nontrivial T] [NoZeroDivisors T]
    [OreLocalization.OreSet (Tᵐᵒᵖ)⁰] := FractionRingOp T

/-- The Ore localization of the right `T`-module `S` (encoded by `RightModule φ`), a
`Q`-vector space. -/
noncomputable abbrev V := LocalizedRightModule T (RightModule φ)

/-- The `AddMonoidHom` sending `x : RightModule φ` to `x /ₒ 1`; used to commute finite
sums with `/ₒ (1 : (Tᵐᵒᵖ)⁰)`. -/
noncomputable def numHom : RightModule φ →+ V φ where
  toFun x := x /ₒ (1 : (Tᵐᵒᵖ)⁰)
  map_zero' := OreLocalization.zero_oreDiv 1
  map_add' _ _ := (OreLocalization.add_oreDiv).symm

@[simp] lemma numHom_apply (x : RightModule φ) :
    numHom φ x = x /ₒ (1 : (Tᵐᵒᵖ)⁰) := rfl

/-- `(τ /ₒ 1) • (x /ₒ 1) = (τ • x) /ₒ 1`: the module action with both fraction
denominators equal to `1` reduces to the `Tᵐᵒᵖ`-action on `RightModule φ`. -/
lemma smul_oreDiv_one (τ : Tᵐᵒᵖ) (x : RightModule φ) :
    (τ /ₒ (1 : (Tᵐᵒᵖ)⁰) : Q T) • (x /ₒ (1 : (Tᵐᵒᵖ)⁰) : V φ) = (τ • x) /ₒ (1 : (Tᵐᵒᵖ)⁰) := by
  rw [OreLocalization.oreDiv_smul_char τ x 1 1 τ 1 (by simp)]
  simp

/-- `(1 /ₒ s) • (x /ₒ 1) = x /ₒ s`: dividing a numerator-`1` fraction is the same as
scaling by the corresponding inverse-denominator scalar. -/
lemma one_oreDiv_smul (s : (Tᵐᵒᵖ)⁰) (x : RightModule φ) :
    ((1 : Tᵐᵒᵖ) /ₒ s : Q T) • (x /ₒ (1 : (Tᵐᵒᵖ)⁰) : V φ) = x /ₒ s := by
  rw [OreLocalization.oreDiv_smul_char (1 : Tᵐᵒᵖ) x s 1 1 1 (by simp)]
  simp

lemma one_oreDiv_ne_zero (s : (Tᵐᵒᵖ)⁰) : ((1 : Tᵐᵒᵖ) /ₒ s : Q T) ≠ 0 := by
  intro hcontra
  rw [← OreLocalization.zero_oreDiv' (1 : (Tᵐᵒᵖ)⁰), OreLocalization.oreDiv_eq_iff] at hcontra
  obtain ⟨u, v, huv1, huv2⟩ := hcontra
  simp only [Submonoid.smul_def, smul_eq_mul, mul_zero, Submonoid.coe_one, mul_one] at huv1 huv2
  rw [← huv1, zero_mul] at huv2
  exact (nonZeroDivisors.ne_zero u.2) huv2

/-- Zero criterion for a fraction with arbitrary denominator: `r /ₒ s = 0` iff some
nonzero-divisor annihilates the numerator `r`. -/
lemma oreDiv_eq_zero_iff {r : RightModule φ} {s : (Tᵐᵒᵖ)⁰} :
    (r /ₒ s : V φ) = 0 ↔ ∃ u : (Tᵐᵒᵖ)⁰, (u : Tᵐᵒᵖ) • r = 0 := by
  rw [← OreLocalization.zero_oreDiv s, OreLocalization.oreDiv_eq_iff]
  constructor
  · rintro ⟨u, v, h1, h2⟩
    have hs0 : (s : Tᵐᵒᵖ) ≠ 0 := nonZeroDivisors.ne_zero s.2
    have hv : (u : Tᵐᵒᵖ) = v := mul_right_cancel₀ hs0 h2
    refine ⟨u, ?_⟩
    rw [hv]
    simpa using h1.symm
  · rintro ⟨u, hu⟩
    exact ⟨u, (u : Tᵐᵒᵖ), by simpa using hu.symm, rfl⟩

/-- Left multiplication by `d`, as a function on the localized module `V φ`. -/
noncomputable def LdFun (d : S) : V φ → V φ :=
  OreLocalization.liftExpand
    (fun (x : RightModule φ) (den : (Tᵐᵒᵖ)⁰) => (⟨d * x.v⟩ : RightModule φ) /ₒ den)
    (by
      intro x t den ht
      have hcomm : (⟨d * (t • x).v⟩ : RightModule φ) = t • (⟨d * x.v⟩ : RightModule φ) := by
        ext; simp [mul_assoc]
      show (⟨d * x.v⟩ : RightModule φ) /ₒ den =
          (⟨d * (t • x).v⟩ : RightModule φ) /ₒ ⟨t * den, ht⟩
      rw [hcomm]
      exact OreLocalization.expand (⟨d * x.v⟩ : RightModule φ) den t ht)

@[simp] lemma LdFun_oreDiv (d : S) (x : RightModule φ) (s : (Tᵐᵒᵖ)⁰) :
    LdFun φ d (x /ₒ s) = (⟨d * x.v⟩ : RightModule φ) /ₒ s := rfl

lemma LdFun_add (d : S) (v w : V φ) : LdFun φ d (v + w) = LdFun φ d v + LdFun φ d w := by
  induction v using OreLocalization.ind with
  | _ x s =>
    induction w using OreLocalization.ind with
    | _ x' s' =>
      obtain ⟨rb, sb, hb⟩ := OreLocalization.oreCondition (s : Tᵐᵒᵖ) s'
      rw [OreLocalization.oreDiv_add_char s s' rb sb hb]
      simp only [LdFun_oreDiv]
      rw [OreLocalization.oreDiv_add_char s s' rb sb hb]
      congr 1
      ext
      simp [Submonoid.smul_def, mul_add, mul_assoc]

lemma LdFun_smul (d : S) (c : Q T) (v : V φ) : LdFun φ d (c • v) = c • LdFun φ d v := by
  induction v using OreLocalization.ind with
  | _ x s =>
    induction c using OreLocalization.ind with
    | _ a t =>
      rw [OreLocalization.oreDiv_smul_oreDiv, LdFun_oreDiv, LdFun_oreDiv,
        OreLocalization.oreDiv_smul_oreDiv]
      congr 1
      ext
      simp [Submonoid.smul_def, mul_assoc]

/-- Left multiplication by `d`, as a `Q`-linear endomorphism of the localized module
`V φ`. -/
noncomputable def Ld (d : S) : V φ →ₗ[Q T] V φ where
  toFun := LdFun φ d
  map_add' := LdFun_add φ d
  map_smul' := LdFun_smul φ d

@[simp] lemma Ld_oreDiv (d : S) (x : RightModule φ) (s : (Tᵐᵒᵖ)⁰) :
    Ld φ d (x /ₒ s) = (⟨d * x.v⟩ : RightModule φ) /ₒ s := rfl

lemma Ld_injective {d : S} (hd : d ≠ 0) : Function.Injective (Ld φ d) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  induction v using OreLocalization.ind with
  | _ x s =>
    rw [Ld_oreDiv, oreDiv_eq_zero_iff] at hv
    obtain ⟨u, hu⟩ := hv
    have h2 : (d * x.v) * φ (u : Tᵐᵒᵖ).unop = 0 := by
      simpa [RightModule.smul_v] using congrArg RightModule.v hu
    have hu' : d * ((u : Tᵐᵒᵖ) • x).v = 0 := by
      rw [RightModule.smul_v]; rw [← mul_assoc]; exact h2
    have hzero : ((u : Tᵐᵒᵖ) • x).v = 0 := (mul_eq_zero.mp hu').resolve_left hd
    have hux : (u : Tᵐᵒᵖ) • x = (0 : RightModule φ) := by
      ext; simpa using hzero
    show x /ₒ s = 0
    rw [oreDiv_eq_zero_iff]
    exact ⟨u, hux⟩

/-- Left multiplication by `d` on `V φ` is surjective whenever `V φ` is finite-dimensional
over `Q` (Lemma 6.1 step (d), after Module.Finite is established from `FiniteRightSpan`). -/
lemma Ld_surjective {d : S} (hd : d ≠ 0) [FiniteDimensional (Q T) (V φ)] :
    Function.Surjective (Ld φ d) :=
  LinearMap.injective_iff_surjective.mp (Ld_injective φ hd)

end Construction

end GlobalStafford.Chart
