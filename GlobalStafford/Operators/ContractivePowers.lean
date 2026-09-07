import GlobalStafford.Operators.Commutator

/-!
# Contractive powers

`PLAN.md` Section 1, Lemma 1.1, work package WP-1
(`Operators/ContractivePowers.lean`). If `E = f^L P` with `P` of order
`≤ r` and `L > r`, then `E^j = f^{jL-(j-1)r} Q_j` with `ord Q_j ≤ jr`, for
every `j ≥ 1`. Also records `exists_threshold`, used to choose `j` large
enough that the shrinking exponent still reaches a prescribed target `m`.
-/

namespace GlobalStafford.Operators

open AlgebraicAnalysis.DifferentialOperators

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Arithmetic identity relating the two equivalent forms of the exponent in
Lemma 1.1: `j*L - (j-1)*r = r + j*(L-r)`, valid for `j ≥ 1` and `r < L`. -/
private theorem jL_sub_eq {j r L : ℕ} (hL : r < L) (hj : 1 ≤ j) :
    j * L - (j - 1) * r = r + j * (L - r) := by
  have hj' : j - 1 + 1 = j := by omega
  have hjr : (j - 1) * r + r = j * r := by
    calc (j - 1) * r + r = (j - 1 + 1) * r := by ring
      _ = j * r := by rw [hj']
  have hLr : r + (L - r) = L := Nat.add_sub_cancel' hL.le
  have hrhs : (j - 1) * r + (r + j * (L - r)) = j * L := by
    calc (j - 1) * r + (r + j * (L - r)) = ((j - 1) * r + r) + j * (L - r) := by ring
      _ = j * r + j * (L - r) := by rw [hjr]
      _ = j * (r + (L - r)) := by ring
      _ = j * L := by rw [hLr]
  omega

/-- The clean (subtraction-free-in-the-induction) form of Lemma 1.1: for
`i ≥ 0`, `E^{i+1} = f^{r + (i+1)(L-r)} Q` with `Q` of order `≤ (i+1) r`. -/
private theorem pow_eq_multiplication_pow_mul_aux (f : A) {P : Module.End k A} {r L : ℕ}
    (hP : P ∈ order r) (hL : r < L) :
    ∀ i : ℕ, ∃ Q ∈ order ((i + 1) * r),
      (multiplication (k := k) f ^ L * P) ^ (i + 1) =
        multiplication (k := k) f ^ (r + (i + 1) * (L - r)) * Q
  | 0 => by
      refine ⟨P, by simpa using hP, ?_⟩
      have hLr : r + (L - r) = L := Nat.add_sub_cancel' hL.le
      simp [hLr]
  | i + 1 => by
      obtain ⟨Q, hQ, hEQ⟩ := pow_eq_multiplication_pow_mul_aux f hP hL i
      have hrle : r ≤ r + (i + 1) * (L - r) := Nat.le_add_right _ _
      obtain ⟨Q', hQ', hQ'eq⟩ := exists_mul_multiplication_pow_eq (f := f) hP hrle
      refine ⟨Q' * Q, ?_, ?_⟩
      · have hmem := mul_mem_order hQ' hQ
        have heq : r + (i + 1) * r = (i + 1 + 1) * r := by ring
        rwa [heq] at hmem
      · have hexpcancel :
            r + (i + 1) * (L - r) - r = (i + 1) * (L - r) := by omega
        have hexp : L + (i + 1) * (L - r) = r + (i + 1 + 1) * (L - r) := by
          have hLr : r + (L - r) = L := Nat.add_sub_cancel' hL.le
          set d := L - r with hd
          rw [← hLr]
          ring
        calc (multiplication (k := k) f ^ L * P) ^ (i + 1 + 1)
            = multiplication (k := k) f ^ L * P *
                (multiplication (k := k) f ^ L * P) ^ (i + 1) := pow_succ' _ _
          _ = multiplication (k := k) f ^ L * (P *
                (multiplication (k := k) f ^ (r + (i + 1) * (L - r)) * Q)) := by
                rw [hEQ, mul_assoc]
          _ = multiplication (k := k) f ^ L *
                ((P * multiplication (k := k) f ^ (r + (i + 1) * (L - r))) * Q) := by
                rw [mul_assoc]
          _ = multiplication (k := k) f ^ L *
                ((multiplication (k := k) f ^ (r + (i + 1) * (L - r) - r) * Q') * Q) := by
                rw [hQ'eq]
          _ = multiplication (k := k) f ^ L *
                (multiplication (k := k) f ^ ((i + 1) * (L - r)) * (Q' * Q)) := by
                rw [hexpcancel, mul_assoc]
          _ = (multiplication (k := k) f ^ L * multiplication (k := k) f ^ ((i + 1) * (L - r)))
                * (Q' * Q) := by rw [mul_assoc]
          _ = multiplication (k := k) f ^ (L + (i + 1) * (L - r)) * (Q' * Q) := by
                rw [← pow_add]
          _ = multiplication (k := k) f ^ (r + (i + 1 + 1) * (L - r)) * (Q' * Q) := by
                rw [hexp]

/-- Lemma 1.1 (contractive powers): if `E = f^L P` with `P` of order `≤ r`
and `L > r`, then `E^j = f^{jL-(j-1)r} Q` with `Q` of order `≤ jr`, for
every `j ≥ 1`. -/
theorem pow_eq_multiplication_pow_mul {f : A} {P : Module.End k A} {r L : ℕ}
    (hP : P ∈ order r) (hL : r < L) :
    ∀ j : ℕ, 1 ≤ j → ∃ Q ∈ order (j * r),
      (multiplication (k := k) f ^ L * P) ^ j =
        multiplication (k := k) f ^ (j * L - (j - 1) * r) * Q := by
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨Q, hQ, hEQ⟩ := pow_eq_multiplication_pow_mul_aux f hP hL i
  exact ⟨Q, hQ, by rw [jL_sub_eq hL hj, hEQ]⟩

/-- Choosing `j` large enough that the (weakly decreasing once past the
threshold) exponent `jL-(j-1)r` reaches a prescribed target `m`. -/
theorem exists_threshold {r L m : ℕ} (hL : r < L) : ∃ j, 1 ≤ j ∧ m ≤ j * L - (j - 1) * r := by
  refine ⟨m + 1, by omega, ?_⟩
  rw [jL_sub_eq hL (by omega)]
  have hpos : 1 ≤ L - r := by omega
  have hge : m + 1 ≤ (m + 1) * (L - r) := by
    calc m + 1 = (m + 1) * 1 := (mul_one _).symm
      _ ≤ (m + 1) * (L - r) := Nat.mul_le_mul_left _ hpos
  omega

/-- Lemma 1.1, at the level of the subalgebra of finite-order differential
operators. -/
theorem pow_eq_multiplicationD_pow_mul {f : A} {P : algebra (k := k) (R := A)} {r L : ℕ}
    (hP : (P : Module.End k A) ∈ order r) (hL : r < L) :
    ∀ j : ℕ, 1 ≤ j → ∃ Q : algebra (k := k) (R := A), (Q : Module.End k A) ∈ order (j * r) ∧
      (multiplicationD (k := k) (A := A) f ^ L * P) ^ j =
        multiplicationD (k := k) (A := A) f ^ (j * L - (j - 1) * r) * Q := by
  intro j hj
  obtain ⟨Q, hQ, hQeq⟩ := pow_eq_multiplication_pow_mul (f := f) hP hL j hj
  refine ⟨⟨Q, (mem_algebra_iff Q).2 ⟨j * r, hQ⟩⟩, hQ, ?_⟩
  apply Subtype.ext
  push_cast [coe_multiplicationD]
  simpa using hQeq

end GlobalStafford.Operators

#print axioms GlobalStafford.Operators.pow_eq_multiplication_pow_mul
#print axioms GlobalStafford.Operators.exists_threshold
#print axioms GlobalStafford.Operators.pow_eq_multiplicationD_pow_mul
