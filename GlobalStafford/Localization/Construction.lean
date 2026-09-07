import GlobalStafford.Localization.Interface
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.FiniteType

/-!
# Construction of the localization interface (paper §1, WP-11)

`PLAN.md` §4, WP-11. Constructs `LocalizationInterface k A Af f` for a
finitely generated integral-domain `k`-algebra `A` and an `f`-power
localization `Af`, discharging the literature input recorded in
`Localization/Interface.lean` (WP-2).

The construction follows the eight-step plan in `PLAN.md`:

1. `ext_of_finite_order`: two finite-order operators on `A_f` that agree on
   the image of `A` are equal. Proved first; it drives every subsequent
   uniqueness argument in this file.
2. `extend`: the extension of a finite-order operator on `A` to `A_f`.
3. Its basic properties (restriction to the image, order bound,
   multiplicativity) and the packaged algebra map `ι`.
4. `clearance`.
-/

namespace GlobalStafford.Localization

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators

variable {k A Af : Type*} [CommRing k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A] [CommRing Af] [Algebra k Af] [Algebra A Af]
  [IsScalarTower k A Af] (f : A) (hf : f ≠ 0) [IsLocalization.Away f Af]

include f in
/-- **Uniqueness lemma** (`PLAN.md` WP-11 step 3): two finite-order
`k`-linear endomorphisms of `A_f` that agree on the image of `A` are equal.
Induction on the common order bound `r`: the difference `D` has order `≤ r`
and vanishes on the image of `A`; for `r = 0`, `D` is multiplication by
`D 1 = 0`; for `r = r' + 1`, `commutator D (algebraMap f)` has order `≤ r'`
and still vanishes on the image of `A` (since `f * a` is again in the image
of `A`), hence is `0` by the induction hypothesis, so `D` commutes with
multiplication by `algebraMap f` and, by induction on powers, with
multiplication by any `algebraMap (f^n)`; every element of `A_f` is
`a / f^n`-shaped, and `algebraMap (f^n)` is a unit, so `D` vanishes
everywhere. -/
theorem ext_of_finite_order {r : ℕ} (Q₁ Q₂ : Module.End k Af)
    (h₁ : Q₁ ∈ order (k := k) (R := Af) r) (h₂ : Q₂ ∈ order (k := k) (R := Af) r)
    (hA : ∀ a : A, Q₁ (algebraMap A Af a) = Q₂ (algebraMap A Af a)) : Q₁ = Q₂ := by
  induction r generalizing Q₁ Q₂ with
  | zero =>
      have hD : Q₁ - Q₂ ∈ order (k := k) (R := Af) 0 := (order (k := k) (R := Af) 0).sub_mem h₁ h₂
      rw [mem_order_zero_iff_eq_multiplication] at hD
      have h1 : (Q₁ - Q₂) 1 = 0 := by
        have h1' : Q₁ (1 : Af) = Q₂ (1 : Af) := by
          have := hA (1 : A)
          rwa [map_one] at this
        simp [LinearMap.sub_apply, h1']
      have hzero : Q₁ - Q₂ = 0 := by
        rw [hD, h1]
        ext x
        simp [multiplication_apply]
      exact sub_eq_zero.mp hzero
  | succ r' ih =>
      set D : Module.End k Af := Q₁ - Q₂ with hDdef
      have hD : D ∈ order (k := k) (R := Af) (r' + 1) := (order (k := k) (R := Af) (r' + 1)).sub_mem h₁ h₂
      have hDvanish : ∀ a : A, D (algebraMap A Af a) = 0 := by
        intro a
        simp only [hDdef, LinearMap.sub_apply]
        exact sub_eq_zero.mpr (hA a)
      have hcomm_ord : commutator D (algebraMap A Af f) ∈ order (k := k) (R := Af) r' :=
        (mem_order_succ_iff D r').1 hD (algebraMap A Af f)
      have hcomm_vanish : ∀ a : A, commutator D (algebraMap A Af f) (algebraMap A Af a) = 0 := by
        intro a
        rw [commutator_apply, ← map_mul, hDvanish (f * a), hDvanish a, mul_zero, sub_zero]
      have hcomm_zero : commutator D (algebraMap A Af f) = 0 :=
        ih (commutator D (algebraMap A Af f)) 0 hcomm_ord (order (k := k) (R := Af) r').zero_mem
          (fun a => by rw [hcomm_vanish a]; rfl)
      have hDcomm : ∀ x : Af, D (algebraMap A Af f * x) = algebraMap A Af f * D x := by
        intro x
        have h2 : commutator D (algebraMap A Af f) x = 0 := by rw [hcomm_zero]; rfl
        rw [commutator_apply] at h2
        exact sub_eq_zero.mp h2
      have hDcomm_pow : ∀ (n : ℕ) (x : Af),
          D (algebraMap A Af f ^ n * x) = algebraMap A Af f ^ n * D x := by
        intro n
        induction n with
        | zero => intro x; simp
        | succ n ihn =>
            intro x
            have hrw : algebraMap A Af f ^ (n + 1) * x =
                algebraMap A Af f * (algebraMap A Af f ^ n * x) := by ring
            rw [hrw, hDcomm, ihn]
            ring
      have hDzero : D = 0 := by
        ext x0
        obtain ⟨⟨a, m⟩, hz⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x0
        simp only at hz
        obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : A) f).1 m.2
        have hspec : algebraMap A Af (m : A) * IsLocalization.mk' Af a m = algebraMap A Af a :=
          IsLocalization.mk'_spec' Af a m
        rw [hz, ← hn, map_pow] at hspec
        have hDa : D (algebraMap A Af f ^ n * x0) = 0 := by
          rw [hspec]; exact hDvanish a
        rw [hDcomm_pow n x0] at hDa
        have hu : IsUnit (algebraMap A Af f ^ n) := (IsLocalization.Away.algebraMap_isUnit f).pow n
        have := (IsUnit.mul_right_eq_zero hu).1 hDa
        simpa using this
      exact sub_eq_zero.mp hDzero

/-! ## Step 2: the extension formula -/

/-- The submonoid element `f^n`, as a member of `Submonoid.powers f`. -/
def fPow (n : ℕ) : Submonoid.powers f :=
  ⟨f ^ n, (Submonoid.mem_powers_iff (f ^ n) f).2 ⟨n, rfl⟩⟩

@[simp] theorem coe_fPow (n : ℕ) : (fPow f n : A) = f ^ n := rfl

theorem fPow_mul (n m : ℕ) : fPow f n * fPow f m = fPow f (n + m) := by
  apply Subtype.ext
  show f ^ n * f ^ m = f ^ (n + m)
  rw [pow_add]

/-- Every `x : A_f` has a representative `mk' Af a (fPow f n)`. -/
theorem exists_fPow_rep (x : Af) : ∃ (a : A) (n : ℕ), IsLocalization.mk' Af a (fPow f n) = x := by
  obtain ⟨⟨a, m⟩, hz⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
  simp only at hz
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : A) f).1 m.2
  refine ⟨a, n, ?_⟩
  have hm : fPow f n = m := Subtype.ext hn
  rw [hm]
  exact hz

/-- Bridging identity: iterating `ad f` and evaluating at `f * a` splits off the
next iterate, from `commutator_apply` and `ad_iterate_succ`. -/
theorem ad_iterate_apply_mul (P : Module.End k A) (j : ℕ) (a : A) :
    ((ad (k := k) (A := A) f)^[j] P) (f * a) =
      f * (((ad (k := k) (A := A) f)^[j] P) a) + (((ad (k := k) (A := A) f)^[j + 1] P) a) := by
  have h : ((ad (k := k) (A := A) f)^[j] P) (f * a) -
      f * (((ad (k := k) (A := A) f)^[j] P) a) = (((ad (k := k) (A := A) f)^[j + 1] P) a) := by
    have heq := commutator_apply (k := k) (R := A) ((ad (k := k) (A := A) f)^[j] P) f a
    rw [show commutator (k := k) (R := A) ((ad (k := k) (A := A) f)^[j] P) f =
        (ad (k := k) (A := A) f)^[j + 1] P from
        (Function.iterate_succ_apply' (ad (k := k) (A := A) f) j P).symm] at heq
    exact heq.symm
  rw [← h]; ring

/-- One term of the extension sum: `Σ_{j ≤ r} choose(-(n:ℤ), j) • mk' Af ((ad f)^[j] P a) f^{n+j}`. -/
noncomputable def termFun (r : ℕ) (P : Module.End k A) (a : A) (n : ℕ) : Af :=
  ∑ j ∈ Finset.range (r + 1),
    (Ring.choose (-(n : ℤ)) j) •
      IsLocalization.mk' Af (((ad (k := k) (A := A) f)^[j] P) a) (fPow f (n + j))

end GlobalStafford.Localization

#print axioms GlobalStafford.Localization.ext_of_finite_order
