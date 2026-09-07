import GlobalStafford.Operators.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Module

/-!
# Iterated commutators and the binomial formulas

`PLAN.md` Section 1, formulas (1.1) and (1.2), and Section 3 work package
WP-1 (`Operators/Commutator.lean`). Defines `ad f P = [P, f]` and its
iterates, proves the order-drop lemmas for `ad`, and the left and right
binomial formulas for `P f^n` and `f^n P` together with their order-`r`
truncation (1.2), first over `Module.End k A` and then transported to the
subalgebra `algebra k A` of finite-order differential operators.
-/

namespace GlobalStafford.Operators

open AlgebraicAnalysis.DifferentialOperators

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- `ad f P = [P, f] = P f - f P`, as an endomorphism. -/
def ad (f : A) (P : Module.End k A) : Module.End k A := commutator P f

private theorem ad_zero (f : A) : ad (k := k) (A := A) f 0 = 0 := by
  simp [ad, commutator]

/-- The Leibniz rule for `ad` over composition, from `commutator_mul`. -/
theorem ad_apply_mul (f : A) (P Q : Module.End k A) :
    ad (k := k) (A := A) f (P * Q) =
      ad (k := k) (A := A) f P * Q + P * ad (k := k) (A := A) f Q := by
  have h := commutator_mul (k := k) (R := A) P Q f
  simpa [ad, add_comm] using h

/-- `P f = f P + [P, f]`. -/
theorem mul_multiplication (f : A) (P : Module.End k A) :
    P * multiplication (k := k) f = multiplication (k := k) f * P + ad (k := k) (A := A) f P := by
  show P * multiplication (k := k) f =
      multiplication (k := k) f * P +
        (P * multiplication (k := k) f - multiplication (k := k) f * P)
  abel

/-- `ad f` drops order by one. -/
theorem ad_mem_order {f : A} {P : Module.End k A} {r : ℕ} (h : P ∈ order (r + 1)) :
    ad (k := k) (A := A) f P ∈ order r :=
  (mem_order_succ_iff P r).1 h f

private theorem ad_iterate_mem_order_aux (f : A) {P : Module.End k A} {r : ℕ} (h : P ∈ order r) :
    ∀ j : ℕ, j ≤ r → (ad (k := k) (A := A) f)^[j] P ∈ order (r - j)
  | 0, _ => by simpa using h
  | j + 1, hj => by
      have hj' : j ≤ r := Nat.le_of_succ_le hj
      have hstep := ad_iterate_mem_order_aux f h j hj'
      have hsub : r - j = (r - (j + 1)) + 1 := by omega
      rw [hsub] at hstep
      rw [Function.iterate_succ_apply']
      exact ad_mem_order hstep

/-- `(ad f)^[j] P` has order `≤ r - j` when `P` has order `≤ r` and `j ≤ r`. -/
theorem ad_iterate_mem_order {f : A} {P : Module.End k A} {r j : ℕ}
    (h : P ∈ order r) (hj : j ≤ r) : (ad (k := k) (A := A) f)^[j] P ∈ order (r - j) :=
  ad_iterate_mem_order_aux f h j hj

/-- `(ad f)^[r+1] P = 0` when `P` has order `≤ r`. -/
theorem ad_iterate_eq_zero {f : A} {P : Module.End k A} {r : ℕ} (h : P ∈ order r) :
    (ad (k := k) (A := A) f)^[r + 1] P = 0 := by
  rw [Function.iterate_succ_apply']
  have hQ : (ad (k := k) (A := A) f)^[r] P ∈ order 0 := by
    simpa using ad_iterate_mem_order h (le_refl r)
  exact (mem_order_zero_iff _).1 hQ f

/-- `(ad f)^[j] P = 0` for `j > r` when `P` has order `≤ r`. -/
theorem ad_iterate_eq_zero_of_lt {f : A} {P : Module.End k A} {r j : ℕ}
    (h : P ∈ order r) (hj : r < j) : (ad (k := k) (A := A) f)^[j] P = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + (r + 1) := ⟨j - (r + 1), by omega⟩
  rw [Function.iterate_add_apply, ad_iterate_eq_zero h]
  exact Function.iterate_fixed (ad_zero f) t

/-- `ad f` applied to an iterate advances the iterate by one step. -/
private theorem ad_iterate_succ (f : A) (P : Module.End k A) (j : ℕ) :
    ad (k := k) (A := A) f ((ad (k := k) (A := A) f)^[j] P) = (ad (k := k) (A := A) f)^[j + 1] P :=
  (Function.iterate_succ_apply' (ad (k := k) (A := A) f) j P).symm

/-- `ad f` annihilates multiplication operators. -/
theorem ad_multiplication (f a : A) :
    ad (k := k) (A := A) f (multiplication (k := k) a) = 0 := by
  ext x
  simp [ad, commutator_apply, mul_left_comm]

/-- Iterates of `ad f` preserve the subalgebra of finite-order operators. -/
theorem ad_iterate_algebraMem (f : A) (P : Module.End k A) (hP : P ∈ algebra (k := k) (R := A))
    (j : ℕ) : (ad (k := k) (A := A) f)^[j] P ∈ algebra (k := k) (R := A) := by
  obtain ⟨r, hr⟩ := (mem_algebra_iff P).1 hP
  by_cases hj : j ≤ r
  · exact ⟨r - j, ad_iterate_mem_order hr hj⟩
  · simp only [not_le] at hj
    rw [ad_iterate_eq_zero_of_lt hr hj]
    exact (algebra (k := k) (R := A)).zero_mem

/-- Combining two consecutive binomial coefficients pulled off the front of a
range sum, as used to shift between the binomial expansions for `n` and
`n + 1`. Pure `Finset`/Pascal-triangle bookkeeping, independent of the
operator structure. -/
private theorem sum_pascal_shift {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    (∑ j ∈ Finset.range (n + 1), n.choose j • g j) +
        (∑ j ∈ Finset.range (n + 1), n.choose j • g (j + 1)) =
      ∑ j ∈ Finset.range (n + 2), (n + 1).choose j • g j := by
  have hsplit : ∑ j ∈ Finset.range (n + 2), (n + 1).choose j • g j =
      (∑ j ∈ Finset.range (n + 1), (n + 1).choose (j + 1) • g (j + 1)) + g 0 := by
    rw [Finset.sum_range_succ' (fun j => (n + 1).choose j • g j) (n + 1)]
    simp
  have hchoose : ∑ j ∈ Finset.range (n + 1), (n + 1).choose (j + 1) • g (j + 1) =
      (∑ j ∈ Finset.range (n + 1), n.choose j • g (j + 1)) +
        (∑ j ∈ Finset.range (n + 1), n.choose (j + 1) • g (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.choose_succ_succ, add_smul]
  have hkey : ∑ j ∈ Finset.range (n + 1), n.choose j • g j =
      (∑ j ∈ Finset.range (n + 1), n.choose (j + 1) • g (j + 1)) + g 0 := by
    have e1 : ∑ j ∈ Finset.range (n + 1), n.choose j • g j =
        (∑ j ∈ Finset.range n, n.choose (j + 1) • g (j + 1)) + g 0 := by
      rw [Finset.sum_range_succ' (fun j => n.choose j • g j) n]
      simp
    have e2 : ∑ j ∈ Finset.range (n + 1), n.choose (j + 1) • g (j + 1) =
        ∑ j ∈ Finset.range n, n.choose (j + 1) • g (j + 1) := by
      rw [Finset.sum_range_succ]
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp
    rw [e1, e2]
  rw [hsplit, hchoose, hkey]
  abel

/-- (1.1), left form: `P f^n = ∑_{j≤n} C(n,j) f^{n-j} (ad f)^[j] P`. -/
theorem mul_multiplication_pow (f : A) (P : Module.End k A) (n : ℕ) :
    P * multiplication (k := k) f ^ n =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j) •
          (multiplication (k := k) f ^ (n - j) * (ad (k := k) (A := A) f)^[j] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have step :
          P * multiplication (k := k) f ^ (n + 1) =
            (∑ j ∈ Finset.range (n + 1),
                (n.choose j) •
                  (multiplication (k := k) f ^ (n - j) * (ad (k := k) (A := A) f)^[j] P)) *
              multiplication (k := k) f := by
        rw [pow_succ, ← mul_assoc, ih]
      set g : ℕ → Module.End k A :=
        fun j => multiplication (k := k) f ^ (n + 1 - j) * (ad (k := k) (A := A) f)^[j] P with
        hg
      have hterm : ∀ j ∈ Finset.range (n + 1),
          (n.choose j) •
                (multiplication (k := k) f ^ (n - j) * (ad (k := k) (A := A) f)^[j] P) *
              multiplication (k := k) f =
            (n.choose j) • g j + (n.choose j) • g (j + 1) := by
        intro j hj
        have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hpow : multiplication (k := k) f ^ (n - j) * multiplication (k := k) f =
            multiplication (k := k) f ^ (n + 1 - j) := by
          rw [← pow_succ]; congr 1; omega
        have hsub : n + 1 - (j + 1) = n - j := by omega
        rw [smul_mul_assoc, mul_assoc, mul_multiplication, ad_iterate_succ,
          mul_add, ← mul_assoc, hpow, smul_add, hg]
        simp only [hsub]
      rw [step, Finset.sum_mul, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      exact sum_pascal_shift n g

/-- (1.1), right form: `f^n P = ∑_{j≤n} C(n,j) (-1)^j (ad f)^[j] P f^{n-j}`. -/
theorem multiplication_pow_mul (f : A) (P : Module.End k A) (n : ℕ) :
    multiplication (k := k) f ^ n * P =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j) •
          ((-1 : ℤ) ^ j • ((ad (k := k) (A := A) f)^[j] P * multiplication (k := k) f ^ (n - j))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have step :
          multiplication (k := k) f ^ (n + 1) * P =
            multiplication (k := k) f *
              ∑ j ∈ Finset.range (n + 1),
                (n.choose j) •
                  ((-1 : ℤ) ^ j •
                    ((ad (k := k) (A := A) f)^[j] P * multiplication (k := k) f ^ (n - j))) := by
        rw [pow_succ', mul_assoc, ih]
      set h : ℕ → Module.End k A :=
        fun j => (-1 : ℤ) ^ j •
          ((ad (k := k) (A := A) f)^[j] P * multiplication (k := k) f ^ (n + 1 - j)) with hh
      have hterm : ∀ j ∈ Finset.range (n + 1),
          multiplication (k := k) f *
              ((n.choose j) •
                ((-1 : ℤ) ^ j •
                  ((ad (k := k) (A := A) f)^[j] P * multiplication (k := k) f ^ (n - j)))) =
            (n.choose j) • h j + (n.choose j) • h (j + 1) := by
        intro j hj
        have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hpow : multiplication (k := k) f * multiplication (k := k) f ^ (n - j) =
            multiplication (k := k) f ^ (n + 1 - j) := by
          rw [← pow_succ']; congr 1; omega
        have hsub : n + 1 - (j + 1) = n - j := by omega
        have hstep : multiplication (k := k) f * (ad (k := k) (A := A) f)^[j] P =
            (ad (k := k) (A := A) f)^[j] P * multiplication (k := k) f -
              (ad (k := k) (A := A) f)^[j + 1] P := by
          rw [eq_sub_iff_add_eq, ← ad_iterate_succ]
          exact (mul_multiplication (k := k) (A := A) f ((ad (k := k) (A := A) f)^[j] P)).symm
        rw [mul_smul_comm, mul_smul_comm, ← mul_assoc, hstep, sub_mul, mul_assoc, hpow, smul_sub]
        simp only [hh, hsub, pow_succ, mul_neg_one]
        module
      rw [step, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      exact sum_pascal_shift n h

/-- Terms with `j > r` vanish in the binomial expansion of `P f^n` when `P`
has order `≤ r`. -/
theorem mul_multiplication_pow_truncate {f : A} {P : Module.End k A} {r : ℕ}
    (hP : P ∈ order r) (n : ℕ) :
    P * multiplication (k := k) f ^ n =
      ∑ j ∈ Finset.range (r + 1),
        (n.choose j) •
          (multiplication (k := k) f ^ (n - j) * (ad (k := k) (A := A) f)^[j] P) := by
  rw [mul_multiplication_pow]
  rcases le_total n r with h | h
  · refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro j hjmem hjnot
    have hgt : n < j := by
      by_contra hc
      exact hjnot (Finset.mem_range.2 (by omega))
    have h0 : n.choose j = 0 := Nat.choose_eq_zero_of_lt hgt
    simp [h0]
  · symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro j hjmem hjnot
    have hgt : r < j := by
      by_contra hc
      exact hjnot (Finset.mem_range.2 (by omega))
    rw [ad_iterate_eq_zero_of_lt hP hgt]
    simp

private theorem multiplication_mem_order_zero (f : A) :
    multiplication (k := k) f ∈ order (k := k) (R := A) 0 :=
  (mem_order_zero_iff_eq_multiplication _).2 (by ext x; simp [multiplication_apply])

private theorem multiplication_pow_mem_order_zero (f : A) (m : ℕ) :
    multiplication (k := k) f ^ m ∈ order (k := k) (R := A) 0 := by
  induction m with
  | zero =>
      have h1 : multiplication (k := k) f ^ 0 = multiplication (k := k) (1 : A) := by
        ext x; simp [multiplication_apply]
      rw [h1]
      exact multiplication_mem_order_zero (k := k) (1 : A)
  | succ m ih =>
      have := mul_mem_order ih (multiplication_mem_order_zero (k := k) f)
      simpa [pow_succ] using this

/-- (1.2): if `P` has order `≤ r ≤ n`, then `P f^n = f^{n-r} Q` for some `Q`
of order `≤ r`. -/
theorem exists_mul_multiplication_pow_eq {f : A} {P : Module.End k A} {r n : ℕ}
    (hP : P ∈ order r) (hn : r ≤ n) :
    ∃ Q ∈ order r,
      P * multiplication (k := k) f ^ n = multiplication (k := k) f ^ (n - r) * Q := by
  refine ⟨∑ j ∈ Finset.range (r + 1),
      (n.choose j) • (multiplication (k := k) f ^ (r - j) * (ad (k := k) (A := A) f)^[j] P),
    ?_, ?_⟩
  · refine (order (k := k) (R := A) r).sum_mem ?_
    intro j hj
    have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h0 : multiplication (k := k) f ^ (r - j) ∈ order (k := k) (R := A) 0 :=
      multiplication_pow_mem_order_zero f (r - j)
    have hadj : (ad (k := k) (A := A) f)^[j] P ∈ order (r - j) := ad_iterate_mem_order hP hjr
    have hmul : multiplication (k := k) f ^ (r - j) * (ad (k := k) (A := A) f)^[j] P ∈
        order (k := k) (R := A) (0 + (r - j)) := mul_mem_order h0 hadj
    have hmul' : multiplication (k := k) f ^ (r - j) * (ad (k := k) (A := A) f)^[j] P ∈
        order (k := k) (R := A) r := order_mono (by omega) hmul
    exact nsmul_mem hmul' (n.choose j)
  · rw [mul_multiplication_pow_truncate hP n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have heq : n - r + (r - j) = n - j := by omega
    rw [mul_smul_comm, ← mul_assoc, ← pow_add, heq]

/-- `ad f`, restricted to the subalgebra of finite-order differential
operators, where it preserves membership by `ad_iterate_algebraMem`. -/
def adD (f : A) (P : algebra (k := k) (R := A)) : algebra (k := k) (R := A) :=
  ⟨ad (k := k) (A := A) f (P : Module.End k A), by
    simpa using ad_iterate_algebraMem f (P : Module.End k A) P.2 1⟩

@[simp] theorem coe_adD (f : A) (P : algebra (k := k) (R := A)) :
    ((adD (k := k) (A := A) f P : algebra (k := k) (R := A)) : Module.End k A) =
      ad (k := k) (A := A) f (P : Module.End k A) := rfl

/-- Iterates of `adD` coerce to iterates of `ad`. -/
theorem coe_adD_iterate (f : A) (P : algebra (k := k) (R := A)) (j : ℕ) :
    (((adD (k := k) (A := A) f)^[j] P : algebra (k := k) (R := A)) : Module.End k A) =
      (ad (k := k) (A := A) f)^[j] (P : Module.End k A) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_adD, ih]

/-- (1.1), left form, at the level of the subalgebra of finite-order
differential operators. -/
theorem mul_multiplicationD_pow (f : A) (P : algebra (k := k) (R := A)) (n : ℕ) :
    P * multiplicationD (k := k) (A := A) f ^ n =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j) •
          (multiplicationD (k := k) (A := A) f ^ (n - j) * (adD (k := k) (A := A) f)^[j] P) := by
  apply Subtype.ext
  push_cast [coe_multiplicationD, coe_adD_iterate]
  simpa using mul_multiplication_pow f (P : Module.End k A) n

/-- (1.1), right form, at the level of the subalgebra of finite-order
differential operators. -/
theorem multiplicationD_pow_mul (f : A) (P : algebra (k := k) (R := A)) (n : ℕ) :
    multiplicationD (k := k) (A := A) f ^ n * P =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j) •
          ((-1 : ℤ) ^ j •
            ((adD (k := k) (A := A) f)^[j] P * multiplicationD (k := k) (A := A) f ^ (n - j))) := by
  apply Subtype.ext
  push_cast [coe_multiplicationD, coe_adD_iterate]
  simpa using multiplication_pow_mul f (P : Module.End k A) n

/-- (1.2), at the level of the subalgebra of finite-order differential
operators. -/
theorem exists_mul_multiplicationD_pow_eq {f : A} {P : algebra (k := k) (R := A)} {r n : ℕ}
    (hP : (P : Module.End k A) ∈ order r) (hn : r ≤ n) :
    ∃ Q : algebra (k := k) (R := A), (Q : Module.End k A) ∈ order r ∧
      P * multiplicationD (k := k) (A := A) f ^ n =
        multiplicationD (k := k) (A := A) f ^ (n - r) * Q := by
  obtain ⟨Q, hQ, hQeq⟩ := exists_mul_multiplication_pow_eq (f := f) hP hn
  refine ⟨⟨Q, (mem_algebra_iff Q).2 ⟨r, hQ⟩⟩, hQ, ?_⟩
  · apply Subtype.ext
    push_cast [coe_multiplicationD]
    simpa using hQeq

end GlobalStafford.Operators

#print axioms GlobalStafford.Operators.ad_apply_mul
#print axioms GlobalStafford.Operators.mul_multiplication
#print axioms GlobalStafford.Operators.ad_mem_order
#print axioms GlobalStafford.Operators.ad_iterate_mem_order
#print axioms GlobalStafford.Operators.ad_iterate_eq_zero
#print axioms GlobalStafford.Operators.ad_iterate_eq_zero_of_lt
#print axioms GlobalStafford.Operators.ad_multiplication
#print axioms GlobalStafford.Operators.ad_iterate_algebraMem
#print axioms GlobalStafford.Operators.mul_multiplication_pow
#print axioms GlobalStafford.Operators.multiplication_pow_mul
#print axioms GlobalStafford.Operators.mul_multiplication_pow_truncate
#print axioms GlobalStafford.Operators.exists_mul_multiplication_pow_eq

#print axioms GlobalStafford.Operators.coe_adD
#print axioms GlobalStafford.Operators.coe_adD_iterate
#print axioms GlobalStafford.Operators.mul_multiplicationD_pow
#print axioms GlobalStafford.Operators.multiplicationD_pow_mul
#print axioms GlobalStafford.Operators.exists_mul_multiplicationD_pow_eq
