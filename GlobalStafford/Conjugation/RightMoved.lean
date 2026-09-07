import GlobalStafford.Operators.Commutator
import GlobalStafford.Localization.Interface
import GlobalStafford.Conjugation.PolynomialEvaluation

/-!
# Right-moved conjugation: `ρ` and the squared input `E'(t)`

`PLAN.md` Section 3, WP-4 "Chart-specific part", and Section 1 (Section 4
paragraph, `ρ_t`, `E'(t)`) of the paper proof (paper Remark 4.2, formulas
(4.10)-(4.11)). Fix a chart denominator `f : A` and its localization `Af`.
Write `fA := multiplicationD (algebraMap A Af f)` for multiplication by the
image of `f` in `D_k(A_f)`, and `u := L.fInv f` for its two-sided inverse
(`GlobalStafford.Localization.LocalizationInterface.fInv`). For `P` of order
`≤ r`, `ρ^{(m)}_t(P) = Σ_{j≤r} C(mt,j)(-1)^j ad_f^j(P) u^j` is a polynomial
in the central variable `t` (paper Remark 4.2) with

```text
ρ^{(m)}_N(P) = fA^{mN} P u^{mN}          for every N ∈ ℕ (right form of (1.1))
```

`E'(t) = c ρ_t(dc) ρ_{2t}(d)` (paper (4.10)) is the `squaredInput` below;
(4.11) is `evalNat_squaredInput`, computing `E'(N) = (c fA^N d)(c fA^N d) u^{2N}`,
i.e. `E'(N) f^{2N} = e_N^2` with `e_N = c f^N d`.
-/

namespace GlobalStafford.Conjugation

open Polynomial
open AlgebraicAnalysis.DifferentialOperators
open GlobalStafford.Operators
open GlobalStafford.Localization

variable {k A Af : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A] [CommRing Af]
  [Algebra k Af] [Algebra A Af] [IsScalarTower k A Af] (f : A) [IsLocalization.Away f Af]

/-- Multiplication by the image of `f` in `D_k(A_f)`. -/
local notation "fA" => multiplicationD (k := k) (A := Af) (algebraMap A Af f)

/-- The two-sided inverse of `fA` in `D_k(A_f)`. -/
local notation "u" => LocalizationInterface.fInv (k := k) f

/-- `algebraMap k D (n : k) * x = n • x`, converting the scalar action of a
natural number coefficient of a `k`-polynomial into the additive `ℕ`-scalar
action on `D`, as produced by `evalNat_scalarPoly` composed with
`binomPoly_comp_nsmul_eval`. -/
private theorem algebraMap_natCast_mul {D : Type*} [Ring D] [Algebra k D] (n : ℕ) (x : D) :
    algebraMap k D (n : k) * x = n • x := by
  rw [map_natCast, nsmul_eq_mul]

/-- Iterates of `adD` vanish beyond the order bound, at the level of the
subalgebra of finite-order differential operators on `A_f`. -/
private theorem adD_iterate_eq_zero_of_lt {r j : ℕ} {P : algebra (k := k) (R := Af)}
    (hP : (P : Module.End k Af) ∈ order r) (hj : r < j) :
    (adD (k := k) (A := Af) (algebraMap A Af f))^[j] P = 0 := by
  apply Subtype.ext
  simp [coe_adD_iterate, GlobalStafford.Operators.ad_iterate_eq_zero_of_lt hP hj]

/-- `binomPoly j` evaluated at the ring literal `0` (as opposed to a cast
natural number): `C(0,j) = 1` if `j = 0`, else `0`. Stated separately from
`binomPoly_eval_nat` because the literal `(0 : k)` produced by evaluating at
`t = 0` is not syntactically `((0 : ℕ) : k)`, so `binomPoly_eval_nat` does
not directly rewrite it. -/
private theorem binomPoly_eval_zero (j : ℕ) :
    (binomPoly (k := k) j).eval (0 : k) = if j = 0 then 1 else 0 := by
  have h := binomPoly_eval_nat (k := k) j 0
  rw [Nat.cast_zero] at h
  rw [h]
  by_cases hj : j = 0
  · subst hj; simp
  · simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), hj]

/-- The right binomial formula (1.1), truncated at the order bound `r` of
`P`, at the level of the subalgebra of finite-order differential operators
on `A_f`. Right-form analogue of `mul_multiplication_pow_truncate`. -/
private theorem multiplicationD_pow_mul_truncate {r : ℕ} {P : algebra (k := k) (R := Af)}
    (hP : (P : Module.End k Af) ∈ order r) (n : ℕ) :
    fA ^ n * P =
      ∑ j ∈ Finset.range (r + 1),
        (n.choose j) •
          ((-1 : ℤ) ^ j •
            ((adD (k := k) (A := Af) (algebraMap A Af f))^[j] P * fA ^ (n - j))) := by
  rw [multiplicationD_pow_mul]
  rcases le_total n r with h | h
  · refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro j hjmem hjnot
    have hgt : n < j := by
      by_contra hc
      exact hjnot (Finset.mem_range.2 (by omega))
    simp [Nat.choose_eq_zero_of_lt hgt]
  · symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro j hjmem hjnot
    have hgt : r < j := by
      by_contra hc
      exact hjnot (Finset.mem_range.2 (by omega))
    rw [adD_iterate_eq_zero_of_lt f hP hgt]
    simp

/-- `ρ^{(m)}_t(P) = Σ_{j≤r} C(mt,j) (-1)^j ad_f^j(P) u^j` (paper Remark 4.2),
as a polynomial in the central variable `t`. -/
noncomputable def rho (m r : ℕ) (P : algebra (k := k) (R := Af)) :
    Polynomial (algebra (k := k) (R := Af)) :=
  ∑ j ∈ Finset.range (r + 1),
    scalarPoly (D := algebra (k := k) (R := Af))
        ((binomPoly (k := k) j).comp (m • (Polynomial.X : Polynomial k))) *
      Polynomial.C
        ((-1 : ℤ) ^ j • ((adD (k := k) (A := Af) (algebraMap A Af f))^[j] P * u ^ j))

/-- `ρ^{(m)}_0(P) = P` unconditionally: at `t = 0` every term with `j > 0`
vanishes because `C(0,j) = 0`, and the `j = 0` term is `P`. -/
theorem evalNat_zero_rho (m r : ℕ) (P : algebra (k := k) (R := Af)) :
    evalNat 0 (rho f m r P) = P := by
  rw [rho, map_sum]
  rw [Finset.sum_eq_single 0]
  · simp [map_mul, evalNat_scalarPoly, evalNat_C, binomPoly_eval_zero]
  · intro j _hj hj0
    simp [map_mul, evalNat_scalarPoly, evalNat_C, binomPoly_eval_zero, hj0]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos r)) h

/-- `ρ^{(m)}_N(P) = fA^{mN} P u^{mN}` for `P` of order `≤ r` and every
`N ∈ ℕ`: the right form of (1.1), truncated at `r`, then multiplied on the
right by `u^{mN}` and simplified using `fA^{mN-j} u^{mN} = u^j`. -/
theorem evalNat_rho (m r : ℕ) {P : algebra (k := k) (R := Af)}
    (hP : (P : Module.End k Af) ∈ order r) (N : ℕ) :
    evalNat N (rho f m r P) = fA ^ (m * N) * P * u ^ (m * N) := by
  rw [rho, map_sum]
  have hRHS : fA ^ (m * N) * P * u ^ (m * N) =
      ∑ j ∈ Finset.range (r + 1),
        ((m * N).choose j •
          ((-1 : ℤ) ^ j •
            ((adD (k := k) (A := Af) (algebraMap A Af f))^[j] P * fA ^ (m * N - j)))) *
          u ^ (m * N) := by
    rw [multiplicationD_pow_mul_truncate f hP (m * N), Finset.sum_mul]
  rw [hRHS]
  refine Finset.sum_congr rfl (fun j _hj => ?_)
  rw [map_mul, evalNat_scalarPoly, binomPoly_comp_nsmul_eval, evalNat_C, map_natCast,
    ← nsmul_eq_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc,
    LocalizationInterface.multiplicationD_pow_mul_fInv_pow_of_le f (Nat.sub_le (m * N) j)]
  by_cases hjmn : j ≤ m * N
  · have he : m * N - (m * N - j) = j := by omega
    rw [he]
  · have h0 : (m * N).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]

/-- `E'(t) = c ρ_t(dc) ρ_{2t}(d)` (paper (4.10)). -/
noncomputable def squaredInput (c d : algebra (k := k) (R := Af)) (r₁ r₂ : ℕ) :
    Polynomial (algebra (k := k) (R := Af)) :=
  Polynomial.C c * rho f 1 r₁ (d * c) * rho f 2 r₂ d

/-- `E'(0) = c d c d`, unconditionally. -/
theorem evalNat_zero_squaredInput (c d : algebra (k := k) (R := Af)) (r₁ r₂ : ℕ) :
    evalNat 0 (squaredInput f c d r₁ r₂) = c * d * c * d := by
  rw [squaredInput, map_mul, map_mul, evalNat_C, evalNat_zero_rho, evalNat_zero_rho, ← mul_assoc]

/-- `E'(N) = (c fA^N d)(c fA^N d) u^{2N}` (paper (4.11)): `E'(N) f^{2N} = e_N^2`
with `e_N = c fA^N d`. -/
theorem evalNat_squaredInput {c d : algebra (k := k) (R := Af)} {r₁ r₂ : ℕ}
    (h₁ : ((d * c : algebra (k := k) (R := Af)) : Module.End k Af) ∈ order r₁)
    (h₂ : (d : Module.End k Af) ∈ order r₂) (N : ℕ) :
    evalNat N (squaredInput f c d r₁ r₂) =
      (c * fA ^ N * d) * (c * fA ^ N * d) * u ^ (2 * N) := by
  have hu : u ^ N * fA ^ (2 * N) = fA ^ N := by
    have h2N : 2 * N = N + N := two_mul N
    rw [h2N, pow_add, ← mul_assoc, LocalizationInterface.fInv_pow_mul_pow, one_mul]
  rw [squaredInput, map_mul, map_mul, evalNat_C, evalNat_rho f 1 r₁ h₁ N,
    evalNat_rho f 2 r₂ h₂ N]
  simp only [one_mul]
  have e1 : c * (fA ^ N * (d * c) * u ^ N) * (fA ^ (2 * N) * d * u ^ (2 * N)) =
      c * fA ^ N * d * c * (u ^ N * fA ^ (2 * N)) * d * u ^ (2 * N) := by
    simp only [mul_assoc]
  rw [e1, hu]
  simp only [mul_assoc]

/-- `E'(t) ≠ 0` when `c, d ≠ 0` and `D_k(A_f)` has no zero divisors: if it
were zero, `evalNat 0` would give `c d c d = 0`, forcing `c = 0` or `d = 0`. -/
theorem squaredInput_ne_zero [NoZeroDivisors (algebra (k := k) (R := Af))]
    {c d : algebra (k := k) (R := Af)} (hc : c ≠ 0) (hd : d ≠ 0) (r₁ r₂ : ℕ) :
    squaredInput f c d r₁ r₂ ≠ 0 := by
  intro h
  have h0 : evalNat 0 (squaredInput f c d r₁ r₂) = (0 : algebra (k := k) (R := Af)) := by
    rw [h, map_zero]
  rw [evalNat_zero_squaredInput] at h0
  rcases mul_eq_zero.mp h0 with h1 | h2
  · rcases mul_eq_zero.mp h1 with h1a | h1b
    · rcases mul_eq_zero.mp h1a with h1a1 | h1a2
      · exact hc h1a1
      · exact hd h1a2
    · exact hc h1b
  · exact hd h2

end GlobalStafford.Conjugation

#print axioms GlobalStafford.Conjugation.evalNat_zero_rho
#print axioms GlobalStafford.Conjugation.evalNat_rho
#print axioms GlobalStafford.Conjugation.evalNat_zero_squaredInput
#print axioms GlobalStafford.Conjugation.evalNat_squaredInput
#print axioms GlobalStafford.Conjugation.squaredInput_ne_zero
