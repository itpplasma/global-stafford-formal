import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Fin.VecNotation
import GlobalStafford.Operators.Commutator

/-!
# Localization presentation of the differential-operator algebra (paper §1)

`PLAN.md` §3, WP-2 (`Localization/Interface.lean`). The `LocalizationInterface`
structure records the literature input that `D_k(A_f)` is (an isomorphic copy
of) an order-graded, injective extension of `D_k(A)` in which every element is
`f`-power-clearable to the image of `D_k(A)` (paper §1, the localization
presentation used throughout §§3-5). This file derives the elementary
consequences (`f` is a unit with a two-sided inverse `fInv`, powers of `f` and
`fInv` cancel, `clearance` restated with the explicit inverse). `rightClearance`
needs the binomial formula (1.2) from WP-1 and is deferred to WP-3.
-/

namespace GlobalStafford.Localization

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators

variable {k A Af : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing Af]
  [Algebra k Af] [Algebra A Af] [IsScalarTower k A Af] (f : A) [IsLocalization.Away f Af]

/-- Literature input (paper §1): the localization `D_k(A_f)` of the
differential-operator algebra, presented as an order-preserving, injective
extension `ι` of `D_k(A)` in which every operator is clearable by some power
of the multiplication-by-`f` operator. -/
structure LocalizationInterface where
  /-- The extension-of-operators algebra map `D_k(A) → D_k(A_f)`. -/
  ι : algebra (k := k) (R := A) →ₐ[k] algebra (k := k) (R := Af)
  /-- `ι` sends multiplication by `a` to multiplication by its image. -/
  ι_multiplicationD : ∀ a : A, ι (multiplicationD a) = multiplicationD (algebraMap A Af a)
  /-- `ι` does not increase order. -/
  ι_mem_order : ∀ (r : ℕ) (P : algebra (k := k) (R := A)),
    (P : Module.End k A) ∈ order (k := k) (R := A) r →
      ((ι P : algebra (k := k) (R := Af)) : Module.End k Af) ∈ order (k := k) (R := Af) r
  /-- `ι` is injective. -/
  ι_injective : Function.Injective ι
  /-- Every operator on `A_f` is cleared to the image of an operator on `A`
  by some power of multiplication by `f`. -/
  clearance : ∀ Q : algebra (k := k) (R := Af), ∃ (l : ℕ) (P : algebra (k := k) (R := A)),
    multiplicationD (algebraMap A Af f) ^ l * Q = ι P

namespace LocalizationInterface

/-- The image of `f` is a unit of `D_k(A_f)`. -/
theorem f_isUnit : IsUnit (multiplicationD (k := k) (A := Af) (algebraMap A Af f)) :=
  multiplicationD_isUnit (IsLocalization.Away.algebraMap_isUnit f)

/-- The inverse of multiplication by `f` in `D_k(A_f)`. -/
noncomputable def fInv : algebra (k := k) (R := Af) := (f_isUnit (k := k) f).unit⁻¹.val

theorem mul_fInv :
    multiplicationD (k := k) (A := Af) (algebraMap A Af f) * fInv (k := k) f = 1 :=
  (f_isUnit (k := k) f).mul_val_inv

theorem fInv_mul :
    fInv (k := k) f * multiplicationD (k := k) (A := Af) (algebraMap A Af f) = 1 :=
  (f_isUnit (k := k) f).val_inv_mul

theorem fInv_commute :
    Commute (fInv (k := k) f) (multiplicationD (k := k) (A := Af) (algebraMap A Af f)) := by
  unfold Commute SemiconjBy
  rw [fInv_mul, mul_fInv]

theorem fInv_pow_mul_pow (n : ℕ) :
    fInv (k := k) f ^ n * multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ n = 1 := by
  rw [← (fInv_commute (k := k) f).mul_pow, fInv_mul, one_pow]

theorem pow_mul_fInv_pow (n : ℕ) :
    multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ n * fInv (k := k) f ^ n = 1 := by
  rw [← (fInv_commute (k := k) f).symm.mul_pow, mul_fInv, one_pow]

theorem multiplicationD_pow_mul_fInv_pow_of_le {m n : ℕ} (h : m ≤ n) :
    multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ m * fInv (k := k) f ^ n =
      fInv (k := k) f ^ (n - m) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add]
  calc multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ m * (fInv (k := k) f ^ m * fInv (k := k) f ^ r)
      = multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ m * fInv (k := k) f ^ m * fInv (k := k) f ^ r := by
        rw [mul_assoc]
    _ = fInv (k := k) f ^ r := by rw [pow_mul_fInv_pow, one_mul]

theorem fInv_pow_mul_multiplicationD_pow_of_le {m n : ℕ} (h : m ≤ n) :
    fInv (k := k) f ^ n * multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ m =
      fInv (k := k) f ^ (n - m) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, add_comm m r, pow_add, mul_assoc, fInv_pow_mul_pow, mul_one]

variable {f}

/-- `ι` commutes with powers of multiplication by `a`. -/
theorem ι_pow_multiplicationD (L : LocalizationInterface (k := k) (A := A) (Af := Af) f)
    (a : A) (n : ℕ) :
    L.ι (multiplicationD a ^ n) = multiplicationD (k := k) (A := Af) (algebraMap A Af a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, map_mul, ih, L.ι_multiplicationD]

/-- `ι` commutes with `multiplicationD a ^ n * P`. -/
theorem ι_multiplicationD_pow_mul (L : LocalizationInterface (k := k) (A := A) (Af := Af) f)
    (a : A) (n : ℕ) (P : algebra (k := k) (R := A)) :
    L.ι (multiplicationD a ^ n * P) =
      multiplicationD (k := k) (A := Af) (algebraMap A Af a) ^ n * L.ι P := by
  rw [map_mul, ι_pow_multiplicationD]

/-- `clearance` restated with the explicit inverse `fInv`. -/
theorem clearance_eq (L : LocalizationInterface (k := k) (A := A) (Af := Af) f)
    (Q : algebra (k := k) (R := Af)) :
    ∃ (l : ℕ) (P : algebra (k := k) (R := A)), Q = fInv (k := k) f ^ l * L.ι P := by
  obtain ⟨l, P, hlP⟩ := L.clearance Q
  refine ⟨l, P, ?_⟩
  rw [← hlP, ← mul_assoc, fInv_pow_mul_pow, one_mul]

/-- Right denominator clearance (paper §1, used throughout §§3-5): every
`Q : D_k(A_f)` can be cleared to the image of `D_k(A)` by right
multiplication by a sufficiently high power of multiplication by `f`. -/
theorem rightClearance (L : LocalizationInterface (k := k) (A := A) (Af := Af) f)
    (Q : algebra (k := k) (R := Af)) :
    ∃ (m : ℕ) (P : algebra (k := k) (R := A)),
      Q * multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ m = L.ι P := by
  obtain ⟨l, P₀, hP₀⟩ := clearance_eq (k := k) L Q
  obtain ⟨r, hr⟩ := exists_order (k := k) (A := A) P₀
  obtain ⟨Q', hQ', hQ'eq⟩ :=
    exists_mul_multiplicationD_pow_eq (k := k) (A := A) (f := f) (n := l + r) hr (Nat.le_add_left r l)
  refine ⟨l + r, Q', ?_⟩
  have hstep : Q * multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ (l + r) =
      fInv (k := k) f ^ l * L.ι (P₀ * multiplicationD (k := k) (A := A) f ^ (l + r)) := by
    rw [hP₀, mul_assoc, map_mul, ι_pow_multiplicationD]
  rw [hstep, hQ'eq]
  have hlr : l + r - r = l := by omega
  rw [hlr, map_mul, ι_pow_multiplicationD, ← mul_assoc, fInv_pow_mul_pow, one_mul]

/-- `rightClearance` for a finite family, with a common exponent `m`. -/
theorem rightClearance_family (L : LocalizationInterface (k := k) (A := A) (Af := Af) f)
    {ι' : Type*} [Fintype ι'] (Q : ι' → algebra (k := k) (R := Af)) :
    ∃ m : ℕ, ∀ i, ∃ P : algebra (k := k) (R := A),
      Q i * multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ m = L.ι P := by
  classical
  have h : ∀ i, ∃ (mi : ℕ) (P : algebra (k := k) (R := A)),
      Q i * multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ mi = L.ι P :=
    fun i => rightClearance (k := k) L (Q i)
  choose mi Pi hPi using h
  refine ⟨Finset.univ.sup mi, fun i => ?_⟩
  have hle : mi i ≤ Finset.univ.sup mi := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  refine ⟨Pi i * multiplicationD (k := k) (A := A) f ^ e, ?_⟩
  rw [he, pow_add, ← mul_assoc, hPi i, map_mul, ι_pow_multiplicationD]

/-- Convenience form of `rightClearance` for a pair. -/
theorem rightClearance_pair (L : LocalizationInterface (k := k) (A := A) (Af := Af) f)
    (U V : algebra (k := k) (R := Af)) :
    ∃ (m : ℕ) (A₀ B₀ : algebra (k := k) (R := A)),
      U * multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ m = L.ι A₀ ∧
      V * multiplicationD (k := k) (A := Af) (algebraMap A Af f) ^ m = L.ι B₀ := by
  obtain ⟨m, hm⟩ := rightClearance_family (k := k) L (![U, V])
  obtain ⟨A₀, hA₀⟩ := hm 0
  obtain ⟨B₀, hB₀⟩ := hm 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hA₀ hB₀
  exact ⟨m, A₀, B₀, hA₀, hB₀⟩

end LocalizationInterface

end GlobalStafford.Localization

#print axioms GlobalStafford.Localization.LocalizationInterface.f_isUnit
#print axioms GlobalStafford.Localization.LocalizationInterface.mul_fInv
#print axioms GlobalStafford.Localization.LocalizationInterface.fInv_mul
#print axioms GlobalStafford.Localization.LocalizationInterface.fInv_commute
#print axioms GlobalStafford.Localization.LocalizationInterface.fInv_pow_mul_pow
#print axioms GlobalStafford.Localization.LocalizationInterface.pow_mul_fInv_pow
#print axioms GlobalStafford.Localization.LocalizationInterface.multiplicationD_pow_mul_fInv_pow_of_le
#print axioms GlobalStafford.Localization.LocalizationInterface.fInv_pow_mul_multiplicationD_pow_of_le
#print axioms GlobalStafford.Localization.LocalizationInterface.ι_pow_multiplicationD
#print axioms GlobalStafford.Localization.LocalizationInterface.ι_multiplicationD_pow_mul
#print axioms GlobalStafford.Localization.LocalizationInterface.clearance_eq
#print axioms GlobalStafford.Localization.LocalizationInterface.rightClearance
#print axioms GlobalStafford.Localization.LocalizationInterface.rightClearance_family
#print axioms GlobalStafford.Localization.LocalizationInterface.rightClearance_pair
