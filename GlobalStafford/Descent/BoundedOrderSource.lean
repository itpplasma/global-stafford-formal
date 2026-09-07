import GlobalStafford.Certificate.SquaredAnnihilator
import GlobalStafford.Localization.Interface
import GlobalStafford.Conjugation.RightMoved
import GlobalStafford.Chart.PolynomialS38

/-!
# Bounded-order sources (paper Theorem 4.1)

`PLAN.md` §3, WP-5 (`Descent/BoundedOrderSource.lean`), formalizing paper
Theorem 4.1 in the Remark 4.2 (right-moved conjugation) form summarized in
§1, "Section 4 (bounded-order sources, right-moved form)". Fix `f ≠ 0` in
`A`, a localization interface `L : LocalizationInterface k A Af f`, and
`S38_poly(D_k(A_f))`. Given `d ≠ 0` in `D_k(A)`, `B`, and right Ore data
`(c, a, b₀)` for `(d, B)`, this produces `M`, `l`, and a nonzero
`H : Polynomial k`, fixed once and for all, such that for every `N` with
`l + M ≤ N` and `H.eval N ≠ 0` there is a bounded-order source `T` (order
`≤ M`) with `F_N := B + f^{N-l-M} T` a locally successful source:
`1 = d U + F_N d V` in `D_k(A_f)`.

The proof follows the paper's Section 3 (squared-annihilator certificate,
`GlobalStafford.Certificate.certificate_of_square`) applied to
`e_N = c f^N d`, whose square is `evalNat N (squaredInput f c d r₁ r₂)`
(`GlobalStafford.Conjugation.evalNat_squaredInput`), combined with the
`S38_poly` hypothesis applied to `squaredInput f c' d' r₁ r₂` and the
denominator-clearing of the coefficients of `w' * C c'` via `L.clearance_eq`.
-/

namespace GlobalStafford.Descent

open Polynomial
open AlgebraicAnalysis.DifferentialOperators
open GlobalStafford.Operators
open GlobalStafford.Localization
open GlobalStafford.Localization.LocalizationInterface
open GlobalStafford.Certificate
open GlobalStafford.Conjugation
open GlobalStafford.Chart

variable {k A Af : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
  [CommRing Af] [Nontrivial Af] [Algebra k Af] [Algebra A Af] [IsScalarTower k A Af]
  (f : A) [IsLocalization.Away f Af] (L : LocalizationInterface (k := k) (A := A) (Af := Af) f)
  [NoZeroDivisors (algebra (k := k) (R := Af))] (hS : S38Poly k (algebra (k := k) (R := Af)))

/-- Multiplication by the image of `f` in `D_k(A_f)`. -/
local notation "fA" => multiplicationD (k := k) (A := Af) (algebraMap A Af f)

/-- The two-sided inverse of `fA`. -/
local notation "uu" => LocalizationInterface.fInv (k := k) f

section Helpers

/-- Evaluation of a `k`-algebra-valued polynomial at a natural number equals
the finite sum of its coefficients times powers of `(N : D)`, over the range
determined by `natDegree`. -/
private theorem evalNat_eq_sum_range {D : Type*} [Ring D] [Algebra k D] (N : ℕ)
    (p : Polynomial D) :
    evalNat N p = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (N : D) ^ i := by
  rw [evalNat_apply, Polynomial.eval₂_eq_sum_range]
  simp

/-- The natural-number cast into the subalgebra of finite-order differential
operators has order `0`: it is `(N : k) • 1`, and `1` has order `0`. -/
private theorem natCast_mem_order_zero {D : Type*} [CommRing D] [Algebra k D] (N : ℕ) :
    ((N : algebra (k := k) (R := D)) : Module.End k D) ∈ order 0 := by
  have h1 : ((1 : algebra (k := k) (R := D)) : Module.End k D) ∈ order 0 := by
    rw [show (1 : algebra (k := k) (R := D)) = multiplicationD (1 : D) from
      multiplicationD_one.symm]
    exact multiplicationD_mem_order_zero 1
  have heq : (N : algebra (k := k) (R := D)) = (N : k) • (1 : algebra (k := k) (R := D)) := by
    rw [← map_natCast (algebraMap k (algebra (k := k) (R := D))) N,
      Algebra.algebraMap_eq_smul_one]
  rw [heq]
  exact smul_mem_order (N : k) h1

/-- Powers of the natural-number cast also have order `0`. -/
private theorem natCast_pow_mem_order_zero {D : Type*} [CommRing D] [Algebra k D] (N i : ℕ) :
    (((N : algebra (k := k) (R := D)) ^ i : algebra (k := k) (R := D)) : Module.End k D) ∈
      order 0 := by
  induction i with
  | zero =>
      rw [pow_zero, show (1 : algebra (k := k) (R := D)) = multiplicationD (1 : D) from
        multiplicationD_one.symm]
      exact multiplicationD_mem_order_zero 1
  | succ i ih =>
      have hmul := mul_mem_orderD ih (natCast_mem_order_zero (k := k) (D := D) N)
      simpa [pow_succ] using hmul

end Helpers

include hS

/-- Paper Theorem 4.1 (Remark 4.2 form): fixed `M`, `l`, and a nonzero
`H : Polynomial k`, such that every admissible `N` (`l + M ≤ N`,
`H.eval N ≠ 0`) supplies a bounded-order source `T` of order `≤ M` making
`F = B + f^{N-l-M} T` a locally successful source at `d`. -/
theorem exists_bounded_order_sources (d B : algebra (k := k) (R := A)) (od : OreData d B)
    (hd : d ≠ 0) :
    ∃ (M l : ℕ) (H : Polynomial k), H ≠ 0 ∧
      ∀ N : ℕ, l + M ≤ N → H.eval (N : k) ≠ 0 →
        ∃ T : algebra (k := k) (R := A), (T : Module.End k A) ∈ order M ∧
          ∃ U V : algebra (k := k) (R := Af),
            (1 : algebra (k := k) (R := Af)) =
              L.ι d * U +
                L.ι (B + multiplicationD f ^ (N - l - M) * T) * L.ι d * V := by
  classical
  -- Step 1: nonzero images of `d` and the Ore denominator `c`, and their orders.
  have hc'ne : L.ι od.c ≠ 0 := fun h => od.hne (L.ι_injective (by rw [h, map_zero]))
  have hd'ne : L.ι d ≠ 0 := fun h => hd (L.ι_injective (by rw [h, map_zero]))
  obtain ⟨r1, hr1⟩ := exists_order (L.ι d * L.ι od.c)
  obtain ⟨r2, hr2⟩ := exists_order (L.ι d)
  -- Step 2: the squared input `E'` is nonzero; obtain the `S38_poly` certificate.
  have hE0 : squaredInput f (L.ι od.c) (L.ι d) r1 r2 ≠ 0 :=
    squaredInput_ne_zero f hc'ne hd'ne r1 r2
  obtain ⟨h, hh0, u', w', v', hcert⟩ := hS _ hE0
  -- Step 3: clear the coefficients of `w' * C c'` and package the source polynomial `Pt`.
  set Wc : Polynomial (algebra (k := k) (R := Af)) := w' * Polynomial.C (L.ι od.c) with hWc_def
  have hclear : ∀ i : ℕ, ∃ (l : ℕ) (P : algebra (k := k) (R := A)),
      Wc.coeff i = LocalizationInterface.fInv (k := k) f ^ l * L.ι P :=
    fun i => L.clearance_eq (Wc.coeff i)
  choose li Pi hPi using hclear
  set l : ℕ := Finset.sup (Finset.range (Wc.natDegree + 1)) li with hl_def
  have hile : ∀ i ∈ Finset.range (Wc.natDegree + 1), li i ≤ l := fun i hi => Finset.le_sup hi
  have hPi' : ∀ i ∈ Finset.range (Wc.natDegree + 1),
      Wc.coeff i =
        LocalizationInterface.fInv (k := k) f ^ l *
          L.ι (multiplicationD f ^ (l - li i) * Pi i) := by
    intro i hi
    have hle := hile i hi
    rw [L.ι_multiplicationD_pow_mul, ← mul_assoc,
      LocalizationInterface.fInv_pow_mul_multiplicationD_pow_of_le f (Nat.sub_le l (li i))]
    have hsub : l - (l - li i) = li i := by omega
    rw [hsub]
    exact hPi i
  have hPiorder : ∀ i : ℕ, ∃ r : ℕ, (Pi i : Module.End k A) ∈ order r := fun i =>
    exists_order (Pi i)
  choose Mi hMi using hPiorder
  set M : ℕ := Finset.sup (Finset.range (Wc.natDegree + 1)) Mi with hM_def
  have hPi'order : ∀ i ∈ Finset.range (Wc.natDegree + 1),
      ((multiplicationD f ^ (l - li i) * Pi i : algebra (k := k) (R := A)) :
        Module.End k A) ∈ order M := by
    intro i hi
    have hz : ((multiplicationD f ^ (l - li i) : algebra (k := k) (R := A)) :
        Module.End k A) ∈ order 0 := by
      rw [multiplicationD_pow]
      exact multiplicationD_mem_order_zero _
    have hmul := mul_mem_orderD hz (hMi i)
    have hle : (0 + Mi i) ≤ M := by
      have := Finset.le_sup (s := Finset.range (Wc.natDegree + 1)) (f := Mi) hi
      omega
    exact order_mono hle hmul
  set Pt : Polynomial (algebra (k := k) (R := A)) :=
    ∑ i ∈ Finset.range (Wc.natDegree + 1),
      Polynomial.C (multiplicationD f ^ (l - li i) * Pi i) * Polynomial.X ^ i with hPt_def
  have hEvalPt : ∀ N : ℕ, evalNat N Pt =
      ∑ i ∈ Finset.range (Wc.natDegree + 1),
        (multiplicationD f ^ (l - li i) * Pi i) * (N : algebra (k := k) (R := A)) ^ i := by
    intro N
    rw [hPt_def, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, evalNat_C, evalNat_natCast_pow]
  have hPtorder : ∀ N : ℕ,
      ((evalNat N Pt : algebra (k := k) (R := A)) : Module.End k A) ∈ order M := by
    intro N
    rw [hEvalPt]
    refine sum_mem_order fun i hi => ?_
    have h1 := hPi'order i hi
    have h2 := natCast_pow_mem_order_zero (k := k) (D := A) N i
    have hmul := mul_mem_orderD h1 h2
    simpa using hmul
  -- Key identity: `evalNat N Wc = u^l * L.ι (evalNat N Pt)`.
  have hkey : ∀ N : ℕ, evalNat N Wc =
      LocalizationInterface.fInv (k := k) f ^ l * L.ι (evalNat N Pt) := by
    intro N
    have hLPt : L.ι (evalNat N Pt) =
        ∑ i ∈ Finset.range (Wc.natDegree + 1),
          L.ι (multiplicationD f ^ (l - li i) * Pi i) *
            (N : algebra (k := k) (R := Af)) ^ i := by
      rw [hEvalPt, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_natCast]
    have hWcsum : evalNat N Wc =
        ∑ i ∈ Finset.range (Wc.natDegree + 1),
          Wc.coeff i * (N : algebra (k := k) (R := Af)) ^ i :=
      evalNat_eq_sum_range (k := k) (D := algebra (k := k) (R := Af)) N Wc
    rw [hLPt, Finset.mul_sum, hWcsum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← mul_assoc, ← hPi' i hi]
  -- Step 4: `H := h`; fix an admissible `N`.
  refine ⟨M, l, h, hh0, fun N hNle hHne => ?_⟩
  have hMleN : M ≤ N := by omega
  -- Step 5: evaluate the certificate at `N` and rewrite it as a squared-annihilator
  -- certificate for `e := c' fA^N d'`.
  set κ : k := (h.eval (N : k))⁻¹ with hκ_def
  have hNeval : algebraMap k (algebra (k := k) (R := Af)) (h.eval (N : k)) =
      evalNat N (squaredInput f (L.ι od.c) (L.ι d) r1 r2) * evalNat N u' +
        evalNat N w' * evalNat N (squaredInput f (L.ι od.c) (L.ι d) r1 r2) * evalNat N v' := by
    have hcongr := congrArg (evalNat N) hcert
    simpa [map_add, map_mul, evalNat_scalarPoly] using hcongr
  have hone : κ • algebraMap k (algebra (k := k) (R := Af)) (h.eval (N : k)) = 1 := by
    rw [Algebra.smul_def, ← map_mul, hκ_def, inv_mul_cancel₀ hHne, map_one]
  have hE : evalNat N (squaredInput f (L.ι od.c) (L.ι d) r1 r2) =
      (L.ι od.c * fA ^ N * L.ι d) * (L.ι od.c * fA ^ N * L.ι d) * uu ^ (2 * N) :=
    evalNat_squaredInput f hr1 hr2 N
  set e : algebra (k := k) (R := Af) := L.ι od.c * fA ^ N * L.ι d with he_def
  set U0 : algebra (k := k) (R := Af) := κ • (uu ^ (2 * N) * evalNat N u') with hU0_def
  set W : algebra (k := k) (R := Af) := κ • evalNat N w' with hW_def
  set V0 : algebra (k := k) (R := Af) := uu ^ (2 * N) * evalNat N v' with hV0_def
  have hinner : e * e * (uu ^ (2 * N) * evalNat N u') +
      evalNat N w' * (e * e) * (uu ^ (2 * N) * evalNat N v') =
      evalNat N (squaredInput f (L.ι od.c) (L.ι d) r1 r2) * evalNat N u' +
        evalNat N w' * evalNat N (squaredInput f (L.ι od.c) (L.ι d) r1 r2) * evalNat N v' := by
    rw [hE, he_def]
    simp only [mul_assoc]
  have hrw : e * e * U0 + W * (e * e) * V0 =
      κ • (e * e * (uu ^ (2 * N) * evalNat N u') +
        evalNat N w' * (e * e) * (uu ^ (2 * N) * evalNat N v')) := by
    rw [hU0_def, hW_def, hV0_def, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, ← smul_add]
  have step5 : (1 : algebra (k := k) (R := Af)) = e * e * U0 + W * (e * e) * V0 := by
    rw [hrw, hinner, ← hNeval]
    exact hone.symm
  -- Step 6: apply the squared-annihilator certificate (paper §3).
  have hc' : L.ι od.c = L.ι d * L.ι od.a := by rw [od.hc, map_mul]
  have hb' : L.ι B * L.ι d * L.ι od.c = L.ι d * L.ι od.b₀ := by
    rw [← map_mul, ← map_mul, od.hb, map_mul]
  have hsquare := certificate_of_square (L.ι d) (L.ι od.a) (L.ι od.b₀) (L.ι B) (L.ι od.c)
    (fA ^ N) U0 W V0 hc' hb' step5
  -- Step 7: identify `W * c' * fA^N` with the image of a bounded-order source.
  obtain ⟨Q, hQorder, hQeq⟩ :=
    exists_mul_multiplicationD_pow_eq (f := f) (P := evalNat N Pt) (hPtorder N) hMleN
  have hιPt : L.ι (evalNat N Pt) * fA ^ N = fA ^ (N - M) * L.ι Q := by
    have hcongr := congrArg L.ι hQeq
    simp only [map_mul, L.ι_pow_multiplicationD, L.ι_multiplicationD_pow_mul] at hcongr
    exact hcongr
  have hlNM : l ≤ N - M := by omega
  have hsplit : fA ^ (N - M) = fA ^ l * fA ^ (N - M - l) := by
    rw [← pow_add]
    congr 1
    omega
  have hcancel : LocalizationInterface.fInv (k := k) f ^ l * fA ^ (N - M) = fA ^ (N - M - l) := by
    rw [hsplit, ← mul_assoc, LocalizationInterface.fInv_pow_mul_pow, one_mul]
  set κQ : algebra (k := k) (R := A) := κ • Q with hT_def
  have hTorder : (κQ : Module.End k A) ∈ order M := smul_mem_order κ hQorder
  have hsmul : L.ι κQ = κ • L.ι Q := by
    rw [hT_def, Algebra.smul_def, Algebra.smul_def, map_mul, L.ι.commutes]
  have hNMl : N - M - l = N - l - M := by omega
  have hWeq : W * L.ι od.c * fA ^ N =
      L.ι (multiplicationD f ^ (N - l - M) * κQ) := by
    calc W * L.ι od.c * fA ^ N
        = κ • (evalNat N w' * L.ι od.c * fA ^ N) := by
          rw [hW_def, smul_mul_assoc, smul_mul_assoc]
      _ = κ • (evalNat N Wc * fA ^ N) := by rw [hWc_def, map_mul, evalNat_C]
      _ = κ • (LocalizationInterface.fInv (k := k) f ^ l *
            (L.ι (evalNat N Pt) * fA ^ N)) := by rw [hkey N, mul_assoc]
      _ = κ • (fA ^ (N - M - l) * L.ι Q) := by rw [hιPt, ← mul_assoc, hcancel]
      _ = κ • (fA ^ (N - l - M) * L.ι Q) := by rw [hNMl]
      _ = fA ^ (N - l - M) * (κ • L.ι Q) := by rw [mul_smul_comm]
      _ = fA ^ (N - l - M) * L.ι κQ := by rw [hsmul]
      _ = L.ι (multiplicationD f ^ (N - l - M)) * L.ι κQ := by
          rw [L.ι_pow_multiplicationD]
      _ = L.ι (multiplicationD f ^ (N - l - M) * κQ) := by rw [← map_mul]
  -- Step 8: assemble the final certificate.
  have hFinal := hsquare
  rw [hWeq, ← map_add] at hFinal
  exact ⟨κQ, hTorder, _, _, hFinal⟩

end GlobalStafford.Descent

#print axioms GlobalStafford.Descent.exists_bounded_order_sources
