import GlobalStafford.Localization.Interface
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.LinearCombination

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

/-! ## Generic commutator identities

Companions to `AlgebraicAnalysis.DifferentialOperators.commutator_mul` (Leibniz
in the *first* argument): here we need the Leibniz rule in the *second*
argument, `commutator D (x * y)`, together with the resulting closure
properties of the set `{x | commutator D x ∈ order s}`. These reduce the order
bound of an operator on `A_f` to its commutators with the image of `A` and with
the inverse of `algebraMap f`, and they are what makes `extend_mem_order` a
finite computation. All statements are for an arbitrary commutative
`k`-algebra `R`; they are applied with `R := A` and `R := A_f`. -/

section GenericCommutator

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- `multiplication x` has order `0`. -/
theorem multiplication_mem_order_zero (x : R) :
    multiplication (k := k) x ∈ order (k := k) (R := R) 0 :=
  (mem_order_zero_iff_eq_multiplication _).2 (by ext w; simp [multiplication_apply])

/-- `[D, 1] = 0`. -/
theorem commutator_one (D : Module.End k R) : commutator D (1 : R) = 0 := by
  ext w; simp [commutator_apply]

/-- **Leibniz rule in the second argument**: `[D, x y] = x [D, y] + [D, x] y`. -/
theorem commutator_mul_right (D : Module.End k R) (x y : R) :
    commutator D (x * y) =
      multiplication (k := k) x * commutator D y + commutator D x * multiplication (k := k) y := by
  ext w
  simp only [commutator_apply, LinearMap.add_apply, Module.End.mul_apply, multiplication_apply]
  rw [show x * y * w = x * (y * w) from mul_assoc x y w]
  ring

/-- The set of `x` with `[D, x]` of order `≤ s` is closed under multiplication. -/
theorem commutator_mem_order_mul {D : Module.End k R} {s : ℕ} {x y : R}
    (hx : commutator D x ∈ order (k := k) (R := R) s)
    (hy : commutator D y ∈ order (k := k) (R := R) s) :
    commutator D (x * y) ∈ order (k := k) (R := R) s := by
  rw [commutator_mul_right]
  refine (order (k := k) (R := R) s).add_mem ?_ ?_
  · simpa using mul_mem_order (multiplication_mem_order_zero (k := k) x) hy
  · simpa using mul_mem_order hx (multiplication_mem_order_zero (k := k) y)

/-- The set of `x` with `[D, x]` of order `≤ s` is closed under inverses:
`[D, v] = -v [D, u] v` when `u v = 1`. -/
theorem commutator_mem_order_of_mul_eq_one {D : Module.End k R} {s : ℕ} {u v : R}
    (huv : u * v = 1) (hu : commutator D u ∈ order (k := k) (R := R) s) :
    commutator D v ∈ order (k := k) (R := R) s := by
  have hmul : multiplication (k := k) (R := R) v * multiplication (k := k) (R := R) u = 1 := by
    ext w
    simp only [Module.End.mul_apply, multiplication_apply, Module.End.one_apply]
    rw [← mul_assoc, mul_comm v u, huv, one_mul]
  have h0 : multiplication (k := k) (R := R) u * commutator D v +
      commutator D u * multiplication (k := k) (R := R) v = 0 := by
    rw [← commutator_mul_right, huv, commutator_one]
  have h1 : commutator D v +
      multiplication (k := k) (R := R) v * commutator D u *
        multiplication (k := k) (R := R) v = 0 := by
    have h2 := congrArg (fun T => multiplication (k := k) (R := R) v * T) h0
    simp only [mul_add, mul_zero] at h2
    rwa [← mul_assoc, hmul, one_mul, ← mul_assoc] at h2
  rw [add_eq_zero_iff_eq_neg] at h1
  rw [h1]
  refine (order (k := k) (R := R) s).neg_mem ?_
  have hstep := mul_mem_order
    (mul_mem_order (multiplication_mem_order_zero (k := k) v) hu)
    (multiplication_mem_order_zero (k := k) v)
  simpa using hstep

/-- **Jacobi-type commuting fact**: commutators with two elements of a
*commutative* algebra commute with each other. -/
theorem commutator_commutator_comm (D : Module.End k R) (x y : R) :
    commutator (commutator D x) y = commutator (commutator D y) x := by
  ext w
  simp only [commutator_apply]
  rw [show y * (x * w) = x * (y * w) from by ring]
  ring

end GenericCommutator

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

/-- `ad f` commutes with `commutator (·) a`, by `commutator_commutator_comm`. -/
theorem ad_commutator (a : A) (P : Module.End k A) :
    ad (k := k) (A := A) f (commutator P a) = commutator (ad (k := k) (A := A) f P) a :=
  commutator_commutator_comm P a f

/-- Iterates of `ad f` commute with `commutator (·) a`. -/
theorem ad_iterate_commutator (a : A) (P : Module.End k A) (j : ℕ) :
    (ad (k := k) (A := A) f)^[j] (commutator P a) =
      commutator ((ad (k := k) (A := A) f)^[j] P) a := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, ad_commutator, Function.iterate_succ_apply']

/-- One term of the extension sum: `Σ_{j ≤ r} choose(-(n:ℤ), j) • mk' Af ((ad f)^[j] P a) f^{n+j}`. -/
noncomputable def termFun (r : ℕ) (P : Module.End k A) (a : A) (n : ℕ) : Af :=
  ∑ j ∈ Finset.range (r + 1),
    (Ring.choose (-(n : ℤ)) j) •
      IsLocalization.mk' Af (((ad (k := k) (A := A) f)^[j] P) a) (fPow f (n + j))

/-- Pascal's identity for `Ring.choose` at negative integer arguments, shifting the
first argument by `1`, from `Ring.choose_succ_succ` (`ℤ` is a binomial ring). -/
private theorem choose_neg_succ_pascal (n j : ℕ) :
    Ring.choose (-(n : ℤ)) (j + 1) = Ring.choose (-((n : ℤ) + 1)) j + Ring.choose (-((n : ℤ) + 1)) (j + 1) := by
  have h := Ring.choose_succ_succ (R := ℤ) (-((n : ℤ) + 1)) j
  have heq : -((n : ℤ) + 1) + 1 = -(n : ℤ) := by ring
  rwa [heq] at h

/-- Same-denominator additivity of `mk'`, from `smul_mk'_one`. -/
theorem mk'_add_same_denom (x₁ x₂ : A) (y : Submonoid.powers f) :
    IsLocalization.mk' Af (x₁ + x₂) y = IsLocalization.mk' Af x₁ y + IsLocalization.mk' Af x₂ y := by
  have e1 : IsLocalization.mk' Af x₁ y = x₁ • IsLocalization.mk' Af (1 : A) y :=
    (IsLocalization.smul_mk'_one x₁ y).symm
  have e2 : IsLocalization.mk' Af x₂ y = x₂ • IsLocalization.mk' Af (1 : A) y :=
    (IsLocalization.smul_mk'_one x₂ y).symm
  have e3 : IsLocalization.mk' Af (x₁ + x₂) y = (x₁ + x₂) • IsLocalization.mk' Af (1 : A) y :=
    (IsLocalization.smul_mk'_one (x₁ + x₂) y).symm
  rw [e3, e1, e2, add_smul]

/-- The pure combinatorial identity underlying the shift step of the extension
formula: a Pascal-triangle recursion for `Ring.choose` on negative integers,
truncated using that `G` vanishes beyond `r` (mirroring `sum_pascal_shift` in
`Operators/Commutator.lean`, with `G`-vanishing playing the role that
`Nat.choose_eq_zero_of_lt` plays there). -/
private theorem pascal_neg_shift_sum (n r : ℕ) (G : ℕ → Af) (hvanish : ∀ j, r < j → G j = 0) :
    (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G j) +
        (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1)) =
      ∑ j ∈ Finset.range (r + 1), (Ring.choose (-(n : ℤ)) j) • G j := by
  have hpad1 :
      (∑ j ∈ Finset.range (r + 1 + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G j) =
        ∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G j := by
    rw [Finset.sum_range_succ, hvanish (r + 1) (by omega)]
    simp
  have hpad3 :
      (∑ j ∈ Finset.range (r + 1 + 1), (Ring.choose (-(n : ℤ)) j) • G j) =
        ∑ j ∈ Finset.range (r + 1), (Ring.choose (-(n : ℤ)) j) • G j := by
    rw [Finset.sum_range_succ, hvanish (r + 1) (by omega)]
    simp
  have hsplit :
      (∑ j ∈ Finset.range (r + 1 + 1), (Ring.choose (-(n : ℤ)) j) • G j) =
        (∑ j ∈ Finset.range (r + 1), (Ring.choose (-(n : ℤ)) (j + 1)) • G (j + 1)) + G 0 := by
    rw [Finset.sum_range_succ' (fun j => (Ring.choose (-(n : ℤ)) j) • G j) (r + 1),
      Ring.choose_zero_right, one_smul]
  have hchoose :
      (∑ j ∈ Finset.range (r + 1), (Ring.choose (-(n : ℤ)) (j + 1)) • G (j + 1)) =
        (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1)) +
          (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) (j + 1)) • G (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [choose_neg_succ_pascal n j, add_smul]
  have hkey :
      (∑ j ∈ Finset.range (r + 1 + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G j) =
        (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) (j + 1)) • G (j + 1)) + G 0 := by
    rw [Finset.sum_range_succ' (fun j => (Ring.choose (-((n : ℤ) + 1)) j) • G j) (r + 1),
      Ring.choose_zero_right, one_smul]
  calc (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G j) +
        (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1))
      = (∑ j ∈ Finset.range (r + 1 + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G j) +
          (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1)) := by rw [hpad1]
    _ = ((∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) (j + 1)) • G (j + 1)) + G 0) +
          (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1)) := by rw [hkey]
    _ = ((∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1)) +
          (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) (j + 1)) • G (j + 1))) + G 0 := by
          abel
    _ = (∑ j ∈ Finset.range (r + 1), (Ring.choose (-(n : ℤ)) (j + 1)) • G (j + 1)) + G 0 := by
          rw [← hchoose]
    _ = ∑ j ∈ Finset.range (r + 1 + 1), (Ring.choose (-(n : ℤ)) j) • G j := by rw [← hsplit]
    _ = ∑ j ∈ Finset.range (r + 1), (Ring.choose (-(n : ℤ)) j) • G j := hpad3

/-- Shifting numerator and denominator by `f` leaves `mk'` unchanged, from
`mk'_cancel`. -/
theorem mk'_shift_num_denom (b : A) (m : ℕ) :
    IsLocalization.mk' Af (f * b) (fPow f (m + 1)) = IsLocalization.mk' Af b (fPow f m) := by
  have hcancel : IsLocalization.mk' Af (b * (fPow f 1 : A)) (fPow f m * fPow f 1) =
      IsLocalization.mk' Af b (fPow f m) := IsLocalization.mk'_cancel b (fPow f m) (fPow f 1)
  rw [coe_fPow, pow_one, fPow_mul] at hcancel
  rw [← hcancel, mul_comm]

/-- The vanishing of `(ad f)^[j] P` applied to `a`, for `j` beyond the order
bound of `P`, transported through `mk'` to `Af`. -/
theorem termFun_summand_vanish {r : ℕ} {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) r)
    (a : A) (n : ℕ) {j : ℕ} (hj : r < j) :
    IsLocalization.mk' Af (((ad (k := k) (A := A) f)^[j] P) a) (fPow f (n + j)) = 0 := by
  have h0 : ((ad (k := k) (A := A) f)^[j] P) a = 0 := by
    rw [ad_iterate_eq_zero_of_lt hP hj]; rfl
  rw [h0]
  symm
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  simp

/-- **Extension formula, representative shift** (`PLAN.md` WP-11 step 1): the
value `termFun r P a n` is unchanged under shifting the representative
`(a, n) ↦ (f * a, n + 1)`. Combines `ad_iterate_apply_mul` (splitting the
iterate at `f * a`), `mk'_shift_num_denom` (absorbing the extra factor of
`f` into the denominator) and `pascal_neg_shift_sum` (the Pascal-identity
recombination, using that `P ∈ order r` kills the boundary term). -/
theorem termFun_shift {r : ℕ} {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) r)
    (a : A) (n : ℕ) : (termFun f r P a n : Af) = termFun f r P (f * a) (n + 1) := by
  set G : ℕ → Af := fun j =>
    IsLocalization.mk' Af (((ad (k := k) (A := A) f)^[j] P) a) (fPow f (n + j)) with hGdef
  have hvanish : ∀ j, r < j → G j = 0 := fun j hj => termFun_summand_vanish f hP a n hj
  have hstep : ∀ j ∈ Finset.range (r + 1),
      (Ring.choose (-((n : ℤ) + 1)) j) •
          IsLocalization.mk' Af (((ad (k := k) (A := A) f)^[j] P) (f * a)) (fPow f (n + 1 + j)) =
        (Ring.choose (-((n : ℤ) + 1)) j) • G j +
          (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1) := by
    intro j _
    rw [ad_iterate_apply_mul f P j a, mk'_add_same_denom]
    have hexp : n + 1 + j = n + j + 1 := by omega
    rw [hexp]
    have hshift : (IsLocalization.mk' Af (f * (((ad (k := k) (A := A) f)^[j] P) a))
          (fPow f (n + j + 1)) : Af) =
        IsLocalization.mk' Af (((ad (k := k) (A := A) f)^[j] P) a) (fPow f (n + j)) :=
      mk'_shift_num_denom f (((ad (k := k) (A := A) f)^[j] P) a) (n + j)
    rw [hshift, smul_add]
    congr 2
  calc (termFun f r P a n : Af)
      = ∑ j ∈ Finset.range (r + 1), (Ring.choose (-(n : ℤ)) j) • G j := rfl
    _ = (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G j) +
          (∑ j ∈ Finset.range (r + 1), (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1)) :=
        (pascal_neg_shift_sum n r G hvanish).symm
    _ = ∑ j ∈ Finset.range (r + 1),
          ((Ring.choose (-((n : ℤ) + 1)) j) • G j + (Ring.choose (-((n : ℤ) + 1)) j) • G (j + 1)) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ j ∈ Finset.range (r + 1),
          (Ring.choose (-((n : ℤ) + 1)) j) •
            IsLocalization.mk' Af (((ad (k := k) (A := A) f)^[j] P) (f * a)) (fPow f (n + 1 + j)) :=
        (Finset.sum_congr rfl hstep).symm
    _ = termFun f r P (f * a) (n + 1) := rfl

/-- Iterating `termFun_shift` `t` times: shifting the representative by `f^t`. -/
theorem termFun_shift_pow {r : ℕ} {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) r)
    (a : A) (n t : ℕ) : (termFun f r P a n : Af) = termFun f r P (f ^ t * a) (n + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [ih, show f ^ (t + 1) * a = f * (f ^ t * a) from by ring,
        show n + (t + 1) = (n + t) + 1 from by omega]
      exact termFun_shift f hP (f ^ t * a) (n + t)

include hf in
/-- `Submonoid.powers f` consists of nonzerodivisors: `A` is a domain and `f ≠ 0`. -/
theorem powers_le_nonZeroDivisors : Submonoid.powers f ≤ nonZeroDivisors A := by
  intro x hx
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff x f).1 hx
  rw [← hm]
  exact mem_nonZeroDivisors_iff_ne_zero.2 (pow_ne_zero m hf)

include hf in
/-- `algebraMap A Af` is injective: `A` is a domain, `f ≠ 0`. -/
theorem algebraMap_injective : Function.Injective (algebraMap A Af) :=
  IsLocalization.injective Af (powers_le_nonZeroDivisors f hf)

include hf in
/-- Two representatives with the *same* exponent and the same value in `Af` have the
same numerator, by cancelling the (nonzerodivisor) common denominator. -/
theorem eq_of_mk'_same_denom {a₁ a₂ : A} {n : ℕ}
    (h : (IsLocalization.mk' Af a₁ (fPow f n) : Af) = IsLocalization.mk' Af a₂ (fPow f n)) :
    a₁ = a₂ := by
  rw [IsLocalization.mk'_eq_iff_eq] at h
  have heq : (fPow f n : A) * a₁ = (fPow f n : A) * a₂ := algebraMap_injective f hf h
  rw [coe_fPow] at heq
  exact mul_left_cancel₀ (pow_ne_zero n hf) heq

/-- `mk' Af a (fPow f (n + t)) = mk' Af (f^t * a) (fPow f (n + t))`: scaling a representative's
numerator by `f^t` and its exponent by `t` leaves the represented element unchanged. -/
theorem mk'_shift_pow (a : A) (n t : ℕ) :
    (IsLocalization.mk' Af a (fPow f n) : Af) = IsLocalization.mk' Af (f ^ t * a) (fPow f (n + t)) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [ih, show f ^ (t + 1) * a = f * (f ^ t * a) from by ring,
        show n + (t + 1) = (n + t) + 1 from by omega, ← mk'_shift_num_denom f (f ^ t * a) (n + t)]

include hf in
/-- **Representative independence of `termFun`** (`PLAN.md` WP-11 step 1, general case):
if two representatives `(a₁, n₁)` and `(a₂, n₂)` denote the same element of `A_f`, they give
the same value of `termFun`. Shift both up to the common exponent `max n₁ n₂` (`mk'_shift_pow`,
`termFun_shift_pow`), then use that at a common exponent the numerators agree
(`eq_of_mk'_same_denom`, using that `A` is a domain). -/
theorem termFun_well_defined {r : ℕ} {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) r)
    {a₁ a₂ : A} {n₁ n₂ : ℕ}
    (h : (IsLocalization.mk' Af a₁ (fPow f n₁) : Af) = IsLocalization.mk' Af a₂ (fPow f n₂)) :
    (termFun f r P a₁ n₁ : Af) = termFun f r P a₂ n₂ := by
  set N := max n₁ n₂ with hN
  obtain ⟨t₁, ht₁⟩ : ∃ t, n₁ + t = N := ⟨N - n₁, by omega⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t, n₂ + t = N := ⟨N - n₂, by omega⟩
  have e1 : (IsLocalization.mk' Af a₁ (fPow f n₁) : Af) =
      IsLocalization.mk' Af (f ^ t₁ * a₁) (fPow f N) := by
    rw [← ht₁]; exact mk'_shift_pow f a₁ n₁ t₁
  have e2 : (IsLocalization.mk' Af a₂ (fPow f n₂) : Af) =
      IsLocalization.mk' Af (f ^ t₂ * a₂) (fPow f N) := by
    rw [← ht₂]; exact mk'_shift_pow f a₂ n₂ t₂
  have hnum : f ^ t₁ * a₁ = f ^ t₂ * a₂ := by
    apply eq_of_mk'_same_denom f hf (Af := Af) (n := N)
    rw [← e1, ← e2, h]
  calc (termFun f r P a₁ n₁ : Af)
      = termFun f r P (f ^ t₁ * a₁) (n₁ + t₁) := termFun_shift_pow f hP a₁ n₁ t₁
    _ = termFun f r P (f ^ t₂ * a₂) (n₂ + t₂) := by rw [hnum, ht₁, ht₂]
    _ = termFun f r P a₂ n₂ := (termFun_shift_pow f hP a₂ n₂ t₂).symm

/-! ## Step 2 (continued): the extension function -/

/-- The numerator of a chosen `fPow`-representative of `x`. -/
noncomputable def repA (x : Af) : A := (exists_fPow_rep f x).choose

/-- The exponent of a chosen `fPow`-representative of `x`. -/
noncomputable def repN (x : Af) : ℕ := (exists_fPow_rep f x).choose_spec.choose

theorem repSpec (x : Af) :
    (IsLocalization.mk' Af (repA f x) (fPow f (repN f x)) : Af) = x :=
  (exists_fPow_rep f x).choose_spec.choose_spec

/-- The extension of a finite-order operator `P` on `A` to `A_f` (`PLAN.md` WP-11 step 2),
via `termFun` at a chosen representative. -/
noncomputable def extend {r : ℕ} (P : Module.End k A) (hP : P ∈ order (k := k) (R := A) r)
    (x : Af) : Af :=
  termFun f r P (repA f x) (repN f x)

include hf in
/-- `extend` does not depend on the chosen representative: its value at
`mk' Af a (fPow f n)` is `termFun f r P a n`, by `termFun_well_defined`. -/
theorem extend_eq_termFun {r : ℕ} {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) r)
    (a : A) (n : ℕ) :
    (extend f P hP (IsLocalization.mk' Af a (fPow f n)) : Af) = termFun f r P a n := by
  unfold extend
  exact termFun_well_defined f hf hP (repSpec f _)

/-- `fPow f 0` is the identity element of `Submonoid.powers f`. -/
theorem fPow_zero : fPow f 0 = (1 : Submonoid.powers f) := by
  apply Subtype.ext
  show f ^ 0 = 1
  exact pow_zero f

/-- `Ring.choose (0 : ℤ) j` is `1` at `j = 0` and `0` otherwise. -/
theorem choose_zero_int (j : ℕ) : Ring.choose (0 : ℤ) j = if j = 0 then 1 else 0 :=
  Ring.choose_zero_ite ℤ j

include hf in
/-- **`extend` restricts to `P` on the image of `A`** (`PLAN.md` WP-11 step 2/`extend_algebraMap`):
only the `j = 0` term of `termFun f r P a 0` survives, since `Ring.choose (0:ℤ) j = 0` for `j ≠ 0`. -/
theorem extend_algebraMap {r : ℕ} {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) r)
    (a : A) : (extend f P hP (algebraMap A Af a) : Af) = algebraMap A Af (P a) := by
  have h1 : (algebraMap A Af a : Af) = IsLocalization.mk' Af a (fPow f 0) := by
    rw [fPow_zero, IsLocalization.mk'_one]
  rw [h1, extend_eq_termFun f hf hP]
  unfold termFun
  simp only [Nat.cast_zero, neg_zero]
  rw [Finset.sum_eq_single 0]
  · simp only [Function.iterate_zero, id_eq, add_zero, choose_zero_int, if_true, one_smul,
      fPow_zero, IsLocalization.mk'_one]
  · intro j _ hj
    rw [choose_zero_int, if_neg hj, zero_smul]
  · intro h0
    exact absurd (Finset.mem_range.2 (Nat.succ_pos r)) h0

/-! ## Step 4, part 1: linearity of `termFun` in the numerator -/

/-- `k`-scalars pass through `mk'`, using `IsScalarTower k A Af`. -/
theorem mk'_smul_k (c : k) (a : A) (y : Submonoid.powers f) :
    (IsLocalization.mk' Af (c • a) y : Af) = c • IsLocalization.mk' Af a y := by
  rw [Algebra.smul_def c a, Algebra.smul_def c (IsLocalization.mk' Af a y),
    IsScalarTower.algebraMap_apply k A Af, IsLocalization.mul_mk'_eq_mk'_of_mul]

/-- `termFun` is additive in the numerator of the representative. -/
theorem termFun_add_num (r : ℕ) (P : Module.End k A) (a b : A) (n : ℕ) :
    (termFun f r P (a + b) n : Af) = termFun f r P a n + termFun f r P b n := by
  unfold termFun
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, mk'_add_same_denom, smul_add]

/-- `termFun` is `k`-homogeneous in the numerator of the representative. -/
theorem termFun_smul_num (r : ℕ) (P : Module.End k A) (c : k) (a : A) (n : ℕ) :
    (termFun f r P (c • a) n : Af) = c • termFun f r P a n := by
  unfold termFun
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, mk'_smul_k, smul_comm]

/-- The truncation length of `termFun` may be raised above the order bound of
`P` without changing the value: the extra summands vanish. -/
theorem termFun_order_mono {r₁ r₂ : ℕ} {P : Module.End k A}
    (hP : P ∈ order (k := k) (R := A) r₁) (h : r₁ ≤ r₂) (a : A) (n : ℕ) :
    (termFun f r₂ P a n : Af) = termFun f r₁ P a n := by
  unfold termFun
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
  intro j _ hjnot
  have hgt : r₁ < j := by
    by_contra hc
    exact hjnot (Finset.mem_range.2 (by omega))
  rw [termFun_summand_vanish f hP a n hgt, smul_zero]

/-- **The commutator identity for `termFun`** (`PLAN.md` WP-11 step 4): moving a
factor `a : A` out of the numerator produces exactly the `termFun` of the
commutator `[P, a]`, at the *same* truncation length. Termwise consequence of
`commutator_apply` together with the Jacobi identity `ad_iterate_commutator`,
which is what lets `[P, a]` replace `P` under the iterated `ad f`. -/
theorem termFun_commutator (r : ℕ) (P : Module.End k A) (a b : A) (n : ℕ) :
    (termFun f r P (a * b) n : Af) =
      algebraMap A Af a * termFun f r P b n + termFun f r (commutator P a) b n := by
  unfold termFun
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsplit : ((ad (k := k) (A := A) f)^[j] P) (a * b) =
      a * (((ad (k := k) (A := A) f)^[j] P) b) +
        (((ad (k := k) (A := A) f)^[j] (commutator P a)) b) := by
    rw [ad_iterate_commutator f a P j, commutator_apply]
    ring
  rw [hsplit, mk'_add_same_denom, smul_add, ← IsLocalization.mul_mk'_eq_mk'_of_mul,
    mul_smul_comm]

/-! ## Step 4, part 2: `extend` as a `k`-linear endomorphism of `A_f` -/

/-- Two elements of `A_f` admit representatives with a common denominator. -/
theorem exists_common_rep (x y : Af) :
    ∃ (a b : A) (N : ℕ), (IsLocalization.mk' Af a (fPow f N) : Af) = x ∧
      (IsLocalization.mk' Af b (fPow f N) : Af) = y := by
  obtain ⟨a, n, ha⟩ := exists_fPow_rep f x
  obtain ⟨b, m, hb⟩ := exists_fPow_rep f y
  refine ⟨f ^ m * a, f ^ n * b, n + m, ?_, ?_⟩
  · rw [← mk'_shift_pow f a n m, ha]
  · rw [show n + m = m + n from by omega, ← mk'_shift_pow f b m n, hb]

include hf in
/-- `extend` is additive: reduce to a common denominator and use
`termFun_add_num`. -/
theorem extend_add {r : ℕ} {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) r) (x y : Af) :
    (extend f P hP (x + y) : Af) = extend f P hP x + extend f P hP y := by
  obtain ⟨a, b, N, hx, hy⟩ := exists_common_rep f x y
  rw [← hx, ← hy, ← mk'_add_same_denom, extend_eq_termFun f hf hP, extend_eq_termFun f hf hP,
    extend_eq_termFun f hf hP, termFun_add_num]

include hf in
/-- `extend` is `k`-homogeneous, by `termFun_smul_num`. -/
theorem extend_smul {r : ℕ} {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) r)
    (c : k) (x : Af) : (extend f P hP (c • x) : Af) = c • extend f P hP x := by
  obtain ⟨a, n, ha⟩ := exists_fPow_rep f x
  rw [← ha, ← mk'_smul_k, extend_eq_termFun f hf hP, extend_eq_termFun f hf hP, termFun_smul_num]

include hf in
/-- **The extension operator** (`PLAN.md` WP-11 step 2): `extend P` packaged as a
`k`-linear endomorphism of `A_f`. -/
noncomputable def extendₗ {r : ℕ} (P : Module.End k A) (hP : P ∈ order (k := k) (R := A) r) :
    Module.End k Af where
  toFun := extend f P hP
  map_add' := extend_add f hf hP
  map_smul' := fun c x => extend_smul f hf hP c x

include hf in
@[simp] theorem extendₗ_apply {r : ℕ} {P : Module.End k A}
    (hP : P ∈ order (k := k) (R := A) r) (x : Af) :
    (extendₗ f hf P hP : Module.End k Af) x = extend f P hP x := rfl

include hf in
/-- `extendₗ` restricts to `P` on the image of `A`. -/
theorem extendₗ_algebraMap {r : ℕ} {P : Module.End k A}
    (hP : P ∈ order (k := k) (R := A) r) (a : A) :
    (extendₗ f hf P hP : Module.End k Af) (algebraMap A Af a) = algebraMap A Af (P a) :=
  extend_algebraMap f hf hP a

include hf in
/-- `extendₗ` at a representative. -/
theorem extendₗ_mk' {r : ℕ} {P : Module.End k A}
    (hP : P ∈ order (k := k) (R := A) r) (a : A) (n : ℕ) :
    (extendₗ f hf P hP : Module.End k Af) (IsLocalization.mk' Af a (fPow f n)) =
      termFun f r P a n :=
  extend_eq_termFun f hf hP a n

/-! ## Step 4, part 3: the order bound -/

include hf in
/-- Base case of `extendₗ_mem_order`: an operator of order `0` on `A` is
multiplication by `P 1`, and its extension is multiplication by the image of
`P 1`. -/
theorem extendₗ_of_order_zero {P : Module.End k A} (hP : P ∈ order (k := k) (R := A) 0) :
    (extendₗ f hf P hP : Module.End k Af) =
      multiplication (k := k) (algebraMap A Af (P 1)) := by
  have hPa : ∀ b : A, P b = P 1 * b := by
    intro b
    have h := (mem_order_zero_iff_eq_multiplication P).1 hP
    conv_lhs => rw [h]
    simp [multiplication_apply]
  ext x
  obtain ⟨a, n, ha⟩ := exists_fPow_rep f x
  rw [← ha, extendₗ_mk' f hf hP, multiplication_apply]
  unfold termFun
  rw [Finset.sum_range_one]
  simp only [Function.iterate_zero, id_eq, add_zero, Ring.choose_zero_right, one_smul]
  rw [hPa a, ← IsLocalization.mul_mk'_eq_mk'_of_mul]

include hf in
/-- **Step 4b**: the commutator of `extendₗ P` with the image of `a : A` is the
extension of `[P, a]`. Pointwise on representatives this is
`termFun_commutator` plus `termFun_order_mono` (the two sides use truncation
lengths `r' + 1` and `r'`). -/
theorem extendₗ_commutator_algebraMap {r' : ℕ} {P : Module.End k A}
    (hP : P ∈ order (k := k) (R := A) (r' + 1)) (a : A) :
    commutator (extendₗ f hf P hP) (algebraMap A Af a) =
      extendₗ f hf (commutator P a) ((mem_order_succ_iff P r').1 hP a) := by
  have hQ : commutator P a ∈ order (k := k) (R := A) r' := (mem_order_succ_iff P r').1 hP a
  ext x
  obtain ⟨b, n, hb⟩ := exists_fPow_rep f x
  rw [← hb, commutator_apply, IsLocalization.mul_mk'_eq_mk'_of_mul, extendₗ_mk' f hf hP,
    extendₗ_mk' f hf hP, extendₗ_mk' f hf hQ, termFun_commutator,
    termFun_order_mono f hQ (Nat.le_succ r') b n]
  ring

include hf in
/-- **Step 4** (`PLAN.md` WP-11): the extension of an operator of order `≤ r` has
order `≤ r`. Induction on `r`. The base case is `extendₗ_of_order_zero`. In the
step, the set of `x : A_f` with `[extendₗ P, x]` of order `≤ r'` contains the
image of `A` (`extendₗ_commutator_algebraMap` plus the induction hypothesis) and
is closed under products and inverses (`commutator_mem_order_mul`,
`commutator_mem_order_of_mul_eq_one`); every `x : A_f` is
`algebraMap a * (algebraMap (f^n))⁻¹`. -/
theorem extendₗ_mem_order : ∀ (r : ℕ) (P : Module.End k A) (hP : P ∈ order (k := k) (R := A) r),
    (extendₗ f hf P hP : Module.End k Af) ∈ order (k := k) (R := Af) r := by
  intro r
  induction r with
  | zero =>
      intro P hP
      rw [extendₗ_of_order_zero f hf hP]
      exact multiplication_mem_order_zero (k := k) _
  | succ r' ih =>
      intro P hP
      rw [mem_order_succ_iff]
      intro z
      have hA : ∀ a : A, commutator (extendₗ f hf P hP) (algebraMap A Af a) ∈
          order (k := k) (R := Af) r' := by
        intro a
        rw [extendₗ_commutator_algebraMap f hf hP a]
        exact ih _ _
      obtain ⟨a, n, ha⟩ := exists_fPow_rep f z
      have hinv : (algebraMap A Af (f ^ n) : Af) * IsLocalization.mk' Af (1 : A) (fPow f n) = 1 := by
        have h := IsLocalization.mk'_spec' Af (1 : A) (fPow f n)
        rw [coe_fPow, map_one] at h
        exact h
      have hz : z = algebraMap A Af a * IsLocalization.mk' Af (1 : A) (fPow f n) := by
        rw [← ha]
        exact IsLocalization.mk'_eq_mul_mk'_one a (fPow f n)
      rw [hz]
      exact commutator_mem_order_mul (hA a)
        (commutator_mem_order_of_mul_eq_one hinv (hA (f ^ n)))

/-! ## Step 5: independence of the order bound, and multiplicativity -/

/-- `algebraMap A Af` is `k`-linear, by `IsScalarTower`. -/
theorem algebraMap_A_smul (c : k) (a : A) :
    algebraMap A Af (c • a) = c • algebraMap A Af a := by
  rw [Algebra.smul_def c a, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]

/-- `(1 : Module.End k R)` has order `0`. -/
theorem one_mem_order_zero {R : Type*} [CommRing R] [Algebra k R] :
    (1 : Module.End k R) ∈ order (k := k) (R := R) 0 :=
  (mem_order_zero_iff_eq_multiplication _).2 (by ext x; simp [multiplication_apply])

include hf in
/-- **The extension does not depend on the chosen order bound** (`PLAN.md` WP-11
step 5): both extensions have finite order and agree on the image of `A`. -/
theorem extendₗ_unique {r₁ r₂ : ℕ} {P : Module.End k A}
    (hP₁ : P ∈ order (k := k) (R := A) r₁) (hP₂ : P ∈ order (k := k) (R := A) r₂) :
    (extendₗ f hf P hP₁ : Module.End k Af) = extendₗ f hf P hP₂ := by
  refine ext_of_finite_order f (r := max r₁ r₂) _ _
    (order_mono (Nat.le_max_left r₁ r₂) (extendₗ_mem_order f hf r₁ P hP₁))
    (order_mono (Nat.le_max_right r₁ r₂) (extendₗ_mem_order f hf r₂ P hP₂)) (fun a => ?_)
  rw [extendₗ_algebraMap, extendₗ_algebraMap]

include hf in
/-- `extend` is multiplicative (`PLAN.md` WP-11 step 5). -/
theorem extendₗ_mul {r s t : ℕ} {P Q : Module.End k A}
    (hP : P ∈ order (k := k) (R := A) r) (hQ : Q ∈ order (k := k) (R := A) s)
    (hPQ : P * Q ∈ order (k := k) (R := A) t) :
    (extendₗ f hf (P * Q) hPQ : Module.End k Af) = extendₗ f hf P hP * extendₗ f hf Q hQ := by
  refine ext_of_finite_order f (r := max t (r + s)) _ _
    (order_mono (le_max_left _ _) (extendₗ_mem_order f hf t _ hPQ))
    (order_mono (le_max_right _ _)
      (mul_mem_order (extendₗ_mem_order f hf r P hP) (extendₗ_mem_order f hf s Q hQ)))
    (fun a => ?_)
  simp only [Module.End.mul_apply, extendₗ_algebraMap]

include hf in
/-- `extend` preserves `1` (`PLAN.md` WP-11 step 5). -/
theorem extendₗ_one {r : ℕ} (hP : (1 : Module.End k A) ∈ order (k := k) (R := A) r) :
    (extendₗ f hf (1 : Module.End k A) hP : Module.End k Af) = 1 := by
  refine ext_of_finite_order f (r := r) _ _ (extendₗ_mem_order f hf r _ hP)
    (order_mono (Nat.zero_le r) one_mem_order_zero) (fun a => ?_)
  rw [extendₗ_algebraMap]
  rfl

include hf in
/-- `extend` preserves `0`. -/
theorem extendₗ_zero {r : ℕ} (hP : (0 : Module.End k A) ∈ order (k := k) (R := A) r) :
    (extendₗ f hf (0 : Module.End k A) hP : Module.End k Af) = 0 := by
  refine ext_of_finite_order f (r := r) _ _ (extendₗ_mem_order f hf r _ hP)
    (order (k := k) (R := Af) r).zero_mem (fun a => ?_)
  rw [extendₗ_algebraMap]
  simp

include hf in
/-- `extend` is additive (`PLAN.md` WP-11 step 5). -/
theorem extendₗ_add {r s t : ℕ} {P Q : Module.End k A}
    (hP : P ∈ order (k := k) (R := A) r) (hQ : Q ∈ order (k := k) (R := A) s)
    (hPQ : P + Q ∈ order (k := k) (R := A) t) :
    (extendₗ f hf (P + Q) hPQ : Module.End k Af) = extendₗ f hf P hP + extendₗ f hf Q hQ := by
  refine ext_of_finite_order f (r := max t (max r s)) _ _
    (order_mono (le_max_left _ _) (extendₗ_mem_order f hf t _ hPQ))
    ((order (k := k) (R := Af) (max t (max r s))).add_mem
      (order_mono (le_trans (le_max_left r s) (le_max_right t _))
        (extendₗ_mem_order f hf r P hP))
      (order_mono (le_trans (le_max_right r s) (le_max_right t _))
        (extendₗ_mem_order f hf s Q hQ))) (fun a => ?_)
  simp only [LinearMap.add_apply, extendₗ_algebraMap, map_add]

include hf in
/-- `extend` is `k`-homogeneous (`PLAN.md` WP-11 step 5). -/
theorem extendₗ_smul_op {r s : ℕ} {P : Module.End k A} (c : k)
    (hP : P ∈ order (k := k) (R := A) r) (hcP : c • P ∈ order (k := k) (R := A) s) :
    (extendₗ f hf (c • P) hcP : Module.End k Af) = c • extendₗ f hf P hP := by
  refine ext_of_finite_order f (r := max s r) _ _
    (order_mono (le_max_left _ _) (extendₗ_mem_order f hf s _ hcP))
    ((order (k := k) (R := Af) (max s r)).smul_mem c
      (order_mono (le_max_right _ _) (extendₗ_mem_order f hf r P hP))) (fun a => ?_)
  simp only [LinearMap.smul_apply, extendₗ_algebraMap, algebraMap_A_smul]

include hf in
/-- `extend` of a multiplication operator is multiplication by the image. -/
theorem extendₗ_multiplication {r : ℕ} (a : A)
    (hP : multiplication (k := k) a ∈ order (k := k) (R := A) r) :
    (extendₗ f hf (multiplication (k := k) a) hP : Module.End k Af) =
      multiplication (k := k) (algebraMap A Af a) := by
  rw [extendₗ_unique f hf hP (multiplication_mem_order_zero (k := k) a),
    extendₗ_of_order_zero f hf (multiplication_mem_order_zero (k := k) a)]
  simp [multiplication_apply]

/-! ## Step 5 (continued): the packaged algebra map `ι` -/

/-- A chosen order bound for an element of `D_k(A)`. -/
noncomputable def ordOf (P : algebra (k := k) (R := A)) : ℕ := (exists_order P).choose

theorem ordOf_spec (P : algebra (k := k) (R := A)) :
    (P : Module.End k A) ∈ order (k := k) (R := A) (ordOf (k := k) (A := A) P) :=
  (exists_order P).choose_spec

include hf in
/-- The underlying function of `ι` (`PLAN.md` WP-11 step 5). -/
noncomputable def ιFun (P : algebra (k := k) (R := A)) : algebra (k := k) (R := Af) :=
  ⟨extendₗ f hf (P : Module.End k A) (ordOf_spec P),
    (mem_algebra_iff _).2 ⟨ordOf (k := k) (A := A) P,
      extendₗ_mem_order f hf _ _ (ordOf_spec P)⟩⟩

include hf in
/-- The coercion of `ιFun P` computed with *any* order bound of `P`. -/
theorem coe_ιFun {r : ℕ} (P : algebra (k := k) (R := A))
    (hP : (P : Module.End k A) ∈ order (k := k) (R := A) r) :
    ((ιFun f hf P : algebra (k := k) (R := Af)) : Module.End k Af) =
      extendₗ f hf (P : Module.End k A) hP :=
  extendₗ_unique f hf _ _

include hf in
/-- `ι` does not increase order (`PLAN.md` WP-11 step 6). -/
theorem ιFun_mem_order (r : ℕ) (P : algebra (k := k) (R := A))
    (hP : (P : Module.End k A) ∈ order (k := k) (R := A) r) :
    ((ιFun f hf P : algebra (k := k) (R := Af)) : Module.End k Af) ∈
      order (k := k) (R := Af) r := by
  rw [coe_ιFun f hf P hP]
  exact extendₗ_mem_order f hf r _ hP

include hf in
/-- `ι` restricts to `P` on the image of `A`. -/
theorem ιFun_algebraMap (P : algebra (k := k) (R := A)) (a : A) :
    ((ιFun f hf P : algebra (k := k) (R := Af)) : Module.End k Af) (algebraMap A Af a) =
      algebraMap A Af ((P : Module.End k A) a) := by
  rw [coe_ιFun f hf P (ordOf_spec P), extendₗ_algebraMap]

include hf in
theorem ιFun_one : ιFun f hf (Af := Af) (1 : algebra (k := k) (R := A)) = 1 := by
  apply Subtype.ext
  have h1 : ((1 : algebra (k := k) (R := A)) : Module.End k A) ∈ order (k := k) (R := A) 0 :=
    one_mem_order_zero
  show ((ιFun f hf (1 : algebra (k := k) (R := A)) : algebra (k := k) (R := Af)) :
      Module.End k Af) = (1 : Module.End k Af)
  rw [coe_ιFun f hf _ h1]
  exact extendₗ_one f hf h1

include hf in
theorem ιFun_zero : ιFun f hf (Af := Af) (0 : algebra (k := k) (R := A)) = 0 := by
  apply Subtype.ext
  have h0 : ((0 : algebra (k := k) (R := A)) : Module.End k A) ∈ order (k := k) (R := A) 0 :=
    (order (k := k) (R := A) 0).zero_mem
  show ((ιFun f hf (0 : algebra (k := k) (R := A)) : algebra (k := k) (R := Af)) :
      Module.End k Af) = (0 : Module.End k Af)
  rw [coe_ιFun f hf _ h0]
  exact extendₗ_zero f hf h0

include hf in
theorem ιFun_mul (P Q : algebra (k := k) (R := A)) :
    ιFun f hf (Af := Af) (P * Q) = ιFun f hf P * ιFun f hf Q := by
  apply Subtype.ext
  have hPQ : ((P * Q : algebra (k := k) (R := A)) : Module.End k A) ∈
      order (k := k) (R := A) (ordOf (k := k) (A := A) P + ordOf (k := k) (A := A) Q) :=
    mul_mem_order (ordOf_spec P) (ordOf_spec Q)
  show ((ιFun f hf (P * Q) : algebra (k := k) (R := Af)) : Module.End k Af) =
      ((ιFun f hf P : algebra (k := k) (R := Af)) : Module.End k Af) *
        ((ιFun f hf Q : algebra (k := k) (R := Af)) : Module.End k Af)
  rw [coe_ιFun f hf _ hPQ, coe_ιFun f hf P (ordOf_spec P), coe_ιFun f hf Q (ordOf_spec Q)]
  exact extendₗ_mul f hf (ordOf_spec P) (ordOf_spec Q) hPQ

include hf in
theorem ιFun_add (P Q : algebra (k := k) (R := A)) :
    ιFun f hf (Af := Af) (P + Q) = ιFun f hf P + ιFun f hf Q := by
  apply Subtype.ext
  have hPQ : ((P + Q : algebra (k := k) (R := A)) : Module.End k A) ∈
      order (k := k) (R := A)
        (max (ordOf (k := k) (A := A) P) (ordOf (k := k) (A := A) Q)) :=
    (order (k := k) (R := A) _).add_mem
      (order_mono (le_max_left _ _) (ordOf_spec P))
      (order_mono (le_max_right _ _) (ordOf_spec Q))
  show ((ιFun f hf (P + Q) : algebra (k := k) (R := Af)) : Module.End k Af) =
      ((ιFun f hf P : algebra (k := k) (R := Af)) : Module.End k Af) +
        ((ιFun f hf Q : algebra (k := k) (R := Af)) : Module.End k Af)
  rw [coe_ιFun f hf _ hPQ, coe_ιFun f hf P (ordOf_spec P), coe_ιFun f hf Q (ordOf_spec Q)]
  exact extendₗ_add f hf (ordOf_spec P) (ordOf_spec Q) hPQ

include hf in
theorem ιFun_smul (c : k) (P : algebra (k := k) (R := A)) :
    ιFun f hf (Af := Af) (c • P) = c • ιFun f hf P := by
  apply Subtype.ext
  have hcP : ((c • P : algebra (k := k) (R := A)) : Module.End k A) ∈
      order (k := k) (R := A) (ordOf (k := k) (A := A) P) :=
    (order (k := k) (R := A) _).smul_mem c (ordOf_spec P)
  show ((ιFun f hf (c • P) : algebra (k := k) (R := Af)) : Module.End k Af) =
      c • ((ιFun f hf P : algebra (k := k) (R := Af)) : Module.End k Af)
  rw [coe_ιFun f hf _ hcP, coe_ιFun f hf P (ordOf_spec P)]
  exact extendₗ_smul_op f hf c (ordOf_spec P) hcP

include hf in
/-- **The extension algebra map** `ι : D_k(A) → D_k(A_f)` (`PLAN.md` WP-11
step 5). -/
noncomputable def ιHom : algebra (k := k) (R := A) →ₐ[k] algebra (k := k) (R := Af) where
  toFun := ιFun f hf
  map_one' := ιFun_one f hf
  map_mul' := ιFun_mul f hf
  map_zero' := ιFun_zero f hf
  map_add' := ιFun_add f hf
  commutes' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ιFun_smul, ιFun_one]

include hf in
theorem ιHom_apply (P : algebra (k := k) (R := A)) :
    ιHom f hf (Af := Af) P = ιFun f hf P := rfl

include hf in
/-- `PLAN.md` WP-11 step 6: `ι` sends `multiplicationD a` to
`multiplicationD (algebraMap a)`. -/
theorem ιHom_multiplicationD (a : A) :
    ιHom f hf (multiplicationD (k := k) (A := A) a) =
      multiplicationD (k := k) (A := Af) (algebraMap A Af a) := by
  apply Subtype.ext
  have hm : ((multiplicationD (k := k) (A := A) a : algebra (k := k) (R := A)) :
      Module.End k A) ∈ order (k := k) (R := A) 0 := multiplicationD_mem_order_zero a
  show ((ιFun f hf (multiplicationD (k := k) (A := A) a) : algebra (k := k) (R := Af)) :
      Module.End k Af) = _
  rw [coe_ιFun f hf _ hm]
  exact extendₗ_multiplication f hf a hm

include hf in
/-- `PLAN.md` WP-11 step 7: `ι` is injective, since it restricts to `P` on the
image of `A` and `algebraMap A Af` is injective. -/
theorem ιHom_injective :
    Function.Injective (ιHom (k := k) (A := A) (Af := Af) f hf) := by
  intro P Q hPQ
  apply Subtype.ext
  ext a
  have h : ((ιFun f hf P : algebra (k := k) (R := Af)) : Module.End k Af) =
      ((ιFun f hf Q : algebra (k := k) (R := Af)) : Module.End k Af) :=
    congrArg (fun T : algebra (k := k) (R := Af) => (T : Module.End k Af)) hPQ
  have ha := congrArg (fun T : Module.End k Af => T (algebraMap A Af a)) h
  simp only [ιFun_algebraMap] at ha
  exact algebraMap_injective f hf ha

/-! ## Step 8: clearance -/

include hf in
/-- If an operator `P` on `A` is computed, through `algebraMap A Af`, by an
operator `Q` of order `≤ r` on `A_f`, then `P` has order `≤ r`. Induction on
`r`: the commutator `[P, c]` is computed the same way by
`[Q, algebraMap c]`. -/
theorem mem_order_of_algebraMap_comm :
    ∀ (r : ℕ) (P : Module.End k A) (Q : Module.End k Af), Q ∈ order (k := k) (R := Af) r →
      (∀ a : A, algebraMap A Af (P a) = Q (algebraMap A Af a)) →
      P ∈ order (k := k) (R := A) r := by
  intro r
  induction r with
  | zero =>
      intro P Q hQ hPQ
      rw [mem_order_zero_iff_eq_multiplication] at hQ
      rw [mem_order_zero_iff_eq_multiplication]
      have hQ1 : algebraMap A Af (P 1) = Q 1 := by rw [hPQ 1, map_one]
      ext a
      show P a = P 1 * a
      refine algebraMap_injective (Af := Af) f hf ?_
      rw [hPQ a, map_mul, hQ1]
      conv_lhs => rw [hQ]
      rw [multiplication_apply]
  | succ r ih =>
      intro P Q hQ hPQ
      rw [mem_order_succ_iff]
      intro c
      refine ih (commutator P c) (commutator Q (algebraMap A Af c))
        ((mem_order_succ_iff Q r).1 hQ (algebraMap A Af c)) (fun a => ?_)
      simp only [commutator_apply, map_sub, map_mul, hPQ]

include hf in
/-- **Finite-span lemma** (`PLAN.md` WP-11 step 8): the values of an operator of
order `≤ r` on the image of `A` lie in a *finitely generated* `A`-submodule of
`A_f`. Outer induction on `r`; the inner induction runs over a finite algebra
generating set `s` of `A` (`Algebra.FiniteType.out`), first over the multiplicative
closure of `s` by `Submonoid.closure_induction_left` — which only ever needs
commutators with the *generators* — and then over its `k`-span by
`Submodule.span_induction`, using `Algebra.adjoin_eq_span`. -/
theorem exists_span_of_order :
    ∀ (r : ℕ) (Q : Module.End k Af), Q ∈ order (k := k) (R := Af) r →
      ∃ V : Finset Af, ∀ a : A, Q (algebraMap A Af a) ∈ Submodule.span A (V : Set Af) := by
  classical
  intro r
  induction r with
  | zero =>
      intro Q hQ
      rw [mem_order_zero_iff_eq_multiplication] at hQ
      refine ⟨{Q 1}, fun a => ?_⟩
      have hval : Q (algebraMap A Af a) = a • Q 1 := by
        conv_lhs => rw [hQ]
        rw [multiplication_apply, Algebra.smul_def, mul_comm]
      rw [hval]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | succ r ih =>
      intro Q hQ
      obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
      have hcomm : ∀ g : A, ∃ V : Finset Af, ∀ b : A,
          (commutator Q (algebraMap A Af g)) (algebraMap A Af b) ∈
            Submodule.span A (V : Set Af) :=
        fun g => ih _ ((mem_order_succ_iff Q r).1 hQ (algebraMap A Af g))
      choose Vg hVg using hcomm
      refine ⟨insert (Q 1) (s.biUnion Vg), fun a => ?_⟩
      have hQ1 : Q 1 ∈ Submodule.span A
          ((insert (Q 1) (s.biUnion Vg) : Finset Af) : Set Af) :=
        Submodule.subset_span (by simp)
      have hgen : ∀ g ∈ s, ∀ b : A,
          (commutator Q (algebraMap A Af g)) (algebraMap A Af b) ∈
            Submodule.span A ((insert (Q 1) (s.biUnion Vg) : Finset Af) : Set Af) := by
        intro g hg b
        refine Submodule.span_mono ?_ (hVg g b)
        exact_mod_cast Finset.coe_subset.2
          (fun v hv => Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨g, hg, hv⟩))
      have hmem : a ∈ Submodule.span k ((Submonoid.closure (s : Set A) : Submonoid A) : Set A) := by
        have h1 : a ∈ Subalgebra.toSubmodule (Algebra.adjoin k (s : Set A)) := by
          rw [hs]; exact Submodule.mem_top
        rwa [Algebra.adjoin_eq_span] at h1
      induction hmem using Submodule.span_induction with
      | mem x hx =>
          induction hx using Submonoid.closure_induction_left with
          | one => simpa using hQ1
          | mul_left g hg y _ ihy =>
              have hstep : Q (algebraMap A Af (g * y)) =
                  g • Q (algebraMap A Af y) +
                    (commutator Q (algebraMap A Af g)) (algebraMap A Af y) := by
                rw [map_mul, commutator_apply, Algebra.smul_def]
                ring
              rw [hstep]
              exact Submodule.add_mem _ (Submodule.smul_mem _ g ihy) (hgen g hg y)
      | zero => simpa using Submodule.zero_mem _
      | add x y _ _ ihx ihy =>
          rw [map_add, map_add]
          exact Submodule.add_mem _ ihx ihy
      | smul c x _ ihx =>
          rw [algebraMap_A_smul, map_smul, algebra_compatible_smul A c]
          exact Submodule.smul_mem _ _ ihx

include hf in
/-- **Clearance** (`PLAN.md` WP-11 step 8): every operator on `A_f` becomes the
image of an operator on `A` after multiplication by a sufficiently high power of
multiplication by `f`. The finitely many values produced by
`exists_span_of_order` have a common denominator `f^l`
(`IsLocalization.exist_integer_multiples_of_finset`); the resulting operator maps
the image of `A` into itself, its restriction `P₀` is `k`-linear of order `≤ r`
(`mem_order_of_algebraMap_comm`), and `ext_of_finite_order` identifies its
extension with the cleared operator. -/
theorem ιHom_clearance (Q : algebra (k := k) (R := Af)) :
    ∃ (l : ℕ) (P : algebra (k := k) (R := A)),
      multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ l * Q = ιHom f hf P := by
  classical
  obtain ⟨r, hr⟩ := exists_order (k := k) (A := Af) Q
  obtain ⟨V, hV⟩ := exists_span_of_order f hf r (Q : Module.End k Af) hr
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (S := Af) (Submonoid.powers f) V
  obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff (b : A) f).1 b.2
  -- the values of `Q` on the image of `A` become integral after scaling by `f ^ l`
  have hspan : ∀ a : A, ∃ c : A, algebraMap A Af c =
      algebraMap A Af (f ^ l) * (Q : Module.End k Af) (algebraMap A Af a) := by
    intro a
    have hT : Submodule.span A (V : Set Af) ≤
        (LinearMap.range (Algebra.linearMap A Af)).comap
          (LinearMap.mulLeft A (algebraMap A Af (f ^ l))) := by
      refine Submodule.span_le.2 (fun v hv => ?_)
      obtain ⟨c, hc⟩ := hb v (by exact_mod_cast hv)
      refine ⟨c, ?_⟩
      show algebraMap A Af c = algebraMap A Af (f ^ l) * v
      rw [hc, hl, Algebra.smul_def]
    exact hT (hV a)
  choose P₀ hP₀ using hspan
  -- `P₀` is `k`-linear
  have hQ' : ∀ a : A, algebraMap A Af (P₀ a) =
      (multiplication (k := k) (algebraMap A Af (f ^ l)) * (Q : Module.End k Af))
        (algebraMap A Af a) := by
    intro a
    rw [hP₀ a]
    rfl
  have hadd : ∀ a c : A, P₀ (a + c) = P₀ a + P₀ c := by
    intro a c
    refine algebraMap_injective (Af := Af) f hf ?_
    simp only [map_add, hQ']
  have hsmul : ∀ (c : k) (a : A), P₀ (c • a) = c • P₀ a := by
    intro c a
    refine algebraMap_injective (Af := Af) f hf ?_
    simp only [algebraMap_A_smul, map_smul, hQ']
  obtain ⟨P₀ₗ, hPl⟩ : ∃ P₀ₗ : Module.End k A, ∀ a : A, P₀ₗ a = P₀ a :=
    ⟨{ toFun := P₀, map_add' := hadd, map_smul' := fun c a => hsmul c a }, fun _ => rfl⟩
  have hQ'ord : (multiplication (k := k) (algebraMap A Af (f ^ l)) * (Q : Module.End k Af)) ∈
      order (k := k) (R := Af) r := by
    simpa using
      mul_mem_order (multiplication_mem_order_zero (k := k) (algebraMap A Af (f ^ l))) hr
  have hPlQ : ∀ a : A, algebraMap A Af (P₀ₗ a) =
      (multiplication (k := k) (algebraMap A Af (f ^ l)) * (Q : Module.End k Af))
        (algebraMap A Af a) := by
    intro a
    rw [hPl a]
    exact hQ' a
  have hord : P₀ₗ ∈ order (k := k) (R := A) r :=
    mem_order_of_algebraMap_comm f hf r P₀ₗ _ hQ'ord hPlQ
  have hext : (extendₗ f hf P₀ₗ hord : Module.End k Af) =
      multiplication (k := k) (algebraMap A Af (f ^ l)) * (Q : Module.End k Af) :=
    ext_of_finite_order f (r := r) _ _ (extendₗ_mem_order f hf r _ hord) hQ'ord
      (fun a => by rw [extendₗ_algebraMap]; exact hPlQ a)
  have hpow : multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ l =
      multiplicationD (k := k) (A := Af) (algebraMap A Af (f ^ l)) := by
    rw [multiplicationD_pow, map_pow]
  refine ⟨l, ⟨P₀ₗ, (mem_algebra_iff _).2 ⟨r, hord⟩⟩, ?_⟩
  rw [hpow, ιHom_apply]
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_ιFun f hf _ hord, hext]
  rfl

/-! ## Step 9: the assembled interface -/

include hf in
/-- **The localization interface** (`PLAN.md` WP-11): `D_k(A_f)` is an
order-preserving, injective, `f`-power-clearable extension of `D_k(A)`.
This discharges the literature input recorded in `Localization/Interface.lean`
(WP-2) for every finitely generated integral domain `A` over `k`. -/
noncomputable def localizationInterface :
    LocalizationInterface (k := k) (A := A) (Af := Af) f where
  ι := ιHom f hf
  ι_multiplicationD := ιHom_multiplicationD f hf
  ι_mem_order := fun r P hP => by
    rw [ιHom_apply]
    exact ιFun_mem_order f hf r P hP
  ι_injective := ιHom_injective f hf
  clearance := ιHom_clearance f hf


end GlobalStafford.Localization

#print axioms GlobalStafford.Localization.ext_of_finite_order
#print axioms GlobalStafford.Localization.termFun_shift
#print axioms GlobalStafford.Localization.termFun_well_defined
#print axioms GlobalStafford.Localization.extend_algebraMap
#print axioms GlobalStafford.Localization.termFun_commutator
#print axioms GlobalStafford.Localization.extendₗ_of_order_zero
#print axioms GlobalStafford.Localization.extendₗ_commutator_algebraMap
#print axioms GlobalStafford.Localization.extendₗ_mem_order
#print axioms GlobalStafford.Localization.extendₗ_mul
#print axioms GlobalStafford.Localization.ιHom_multiplicationD
#print axioms GlobalStafford.Localization.ιHom_injective
#print axioms GlobalStafford.Localization.exists_span_of_order
#print axioms GlobalStafford.Localization.ιHom_clearance
#print axioms GlobalStafford.Localization.localizationInterface
