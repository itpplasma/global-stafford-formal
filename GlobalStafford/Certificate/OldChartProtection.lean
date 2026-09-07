import GlobalStafford.Localization.Interface
import GlobalStafford.Operators.ContractivePowers
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NoncommRing

/-!
# Old-chart protection (paper §1, Lemma 1.2)

`PLAN.md` §1 (Lemma 1.2) and §3, work package WP-3
(`Certificate/OldChartProtection.lean`). Given a same-divisor certificate
`1 = d U_g + B d V_g` on an old chart `A_g` and a right denominator
clearance `f^m = d A_0 + F d B_0` (with `F = B + f^L T`, `ord T ≤ M`, and
`L` large enough compared to `M`, `ord d`, `ord V_g`) of the *new* source
`F` obtained on chart `A_f`, produces a certificate `1 = d U_g' + F d V_g'`
for the combined source `F` that still holds on the old chart `A_g`. This
is the right-denominator-clearance form of Lemma 1.2 (paper §1): geometric
series in `E := f^L (T d V_g)` (Lemma 1.1, `pow_eq_multiplicationD_pow_mul`)
absorb the perturbation `F - B` without disturbing the old-chart identity.
-/

namespace GlobalStafford.Certificate

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators
  GlobalStafford.Localization GlobalStafford.Localization.LocalizationInterface

variable {k A Ag : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing Ag] [Algebra k Ag]
  [Algebra A Ag] [IsScalarTower k A Ag] {g : A} [IsLocalization.Away g Ag]
  (Lg : LocalizationInterface (k := k) (A := A) (Af := Ag) g) (f : A)

/-- Lemma 1.2 (old-chart protection). If `1 = d U_g + B d V_g` holds on the
old chart `A_g`, `T` has order `≤ M`, `L > M + ord d + ord V_g`, and
`f^m = d A_0 + F d B_0` in `D_k(A)` with `F = B + f^L T` (a right
denominator clearance of `F` obtained on chart `A_f`), then the same
source `F` still admits a same-divisor certificate on the old chart
`A_g`. -/
theorem protect_old_chart {d B T A₀ B₀ : algebra (k := k) (R := A)} {U V : algebra (k := k) (R := Ag)}
    {rd M rV L m : ℕ}
    (hd : (d : Module.End k A) ∈ order rd) (hT : (T : Module.End k A) ∈ order M)
    (hV : (V : Module.End k Ag) ∈ order rV)
    (hL : M + rd + rV < L)
    (hold : (1 : algebra (k := k) (R := Ag)) = Lg.ι d * U + Lg.ι B * Lg.ι d * V)
    (hclear : multiplicationD (k := k) (A := A) f ^ m =
      d * A₀ + (B + multiplicationD (k := k) (A := A) f ^ L * T) * d * B₀) :
    ∃ U' V' : algebra (k := k) (R := Ag),
      (1 : algebra (k := k) (R := Ag)) =
        Lg.ι d * U' +
          Lg.ι (B + multiplicationD (k := k) (A := A) f ^ L * T) * Lg.ι d * V' := by
  classical
  set F : algebra (k := k) (R := A) := B + multiplicationD (k := k) (A := A) f ^ L * T with hF
  set fg : algebra (k := k) (R := Ag) := multiplicationD (k := k) (A := Ag) (algebraMap A Ag f)
    with hfg
  -- Step 1: `ι F = ι B + fg ^ L * ι T`.
  have hιF : Lg.ι F = Lg.ι B + fg ^ L * Lg.ι T := by
    rw [hF, map_add, map_mul, ι_pow_multiplicationD]
  -- Step 2: `P := ι T * ι d * V` has order `≤ r := M + rd + rV`.
  set r : ℕ := M + rd + rV with hr
  have hP : ((Lg.ι T * Lg.ι d * V : algebra (k := k) (R := Ag)) : Module.End k Ag) ∈ order r := by
    have hιT : (Lg.ι T : Module.End k Ag) ∈ order M := Lg.ι_mem_order M T hT
    have hιd : (Lg.ι d : Module.End k Ag) ∈ order rd := Lg.ι_mem_order rd d hd
    have h1 : ((Lg.ι T * Lg.ι d : algebra (k := k) (R := Ag)) : Module.End k Ag) ∈
        order (M + rd) := mul_mem_orderD hιT hιd
    have h2 := mul_mem_orderD h1 hV
    rwa [hr]
  set P : algebra (k := k) (R := Ag) := Lg.ι T * Lg.ι d * V with hPdef
  set E : algebra (k := k) (R := Ag) := fg ^ L * P with hE
  -- Step 3: `ι d * U + ι F * ι d * V = 1 + E`.
  have hsum : Lg.ι d * U + Lg.ι F * Lg.ι d * V = 1 + E := by
    have hexpand : Lg.ι F * Lg.ι d * V = Lg.ι B * Lg.ι d * V + E := by
      rw [hιF, hE, hPdef, add_mul, add_mul]
      simp only [mul_assoc]
    rw [hexpand, ← add_assoc, ← hold]
  -- Step 4: `exists_threshold` and Lemma 1.1 give `E^j = fg ^ a * Q`.
  obtain ⟨j, hj1, hjm⟩ := exists_threshold (r := r) (L := L) (m := m) hL
  obtain ⟨Q, hQ, hEQ⟩ := pow_eq_multiplicationD_pow_mul (f := algebraMap A Ag f) (P := P) (r := r)
    (L := L) hP hL j hj1
  set a : ℕ := j * L - (j - 1) * r with ha
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hjm
  have hEQ2 : E ^ j = fg ^ a * Q := by rw [hE]; exact hEQ
  set W : algebra (k := k) (R := Ag) := (-1 : algebra (k := k) (R := Ag)) ^ j * (fg ^ e * Q) with hW
  -- Step 5: geometric-series inverse, `(1 + E) * Z + fg ^ m * W = 1`. Proved
  -- at the level of `Module.End k Ag` (via `Subtype.ext`) because the
  -- subalgebra `algebra k Ag` carries a typeclass diamond on `Neg`/`Sub`
  -- (two non-syntactically-equal `HasDistribNeg`/`NegMemClass` instances)
  -- that blocks `neg_pow`/`mul_neg_geom_sum` from applying directly to it.
  set Z : algebra (k := k) (R := Ag) := ∑ i ∈ Finset.range j, (-E) ^ i with hZ
  have hkey : (1 + E) * Z + fg ^ m * W = (1 : algebra (k := k) (R := Ag)) := by
    apply Subtype.ext
    push_cast [hZ, hW]
    have hnp := neg_pow (E : Module.End k Ag) j
    have hgs := mul_neg_geom_sum (-(E : Module.End k Ag)) j
    rw [sub_neg_eq_add] at hgs
    have hEQ2' : ((E ^ j : algebra (k := k) (R := Ag)) : Module.End k Ag) =
        ((fg ^ a * Q : algebra (k := k) (R := Ag)) : Module.End k Ag) := by rw [hEQ2]
    push_cast at hEQ2'
    have hcomm := (Commute.neg_one_left ((fg : Module.End k Ag) ^ m)).pow_left j
    rw [hgs, hnp, hEQ2', he, pow_add]
    simp only [← mul_assoc]
    rw [hcomm.eq]
    abel
  -- Step 6: `fg ^ m = ι d * ι A₀ + ι F * ι d * ι B₀`.
  have hfgm : fg ^ m = Lg.ι d * Lg.ι A₀ + Lg.ι F * Lg.ι d * Lg.ι B₀ := by
    have hstep : Lg.ι (multiplicationD (k := k) (A := A) f ^ m) = fg ^ m := ι_pow_multiplicationD Lg f m
    rw [← hstep, hclear, map_add, map_mul, map_mul, map_mul, mul_assoc]
  -- Step 7: assemble the certificate.
  refine ⟨U * Z + Lg.ι A₀ * W, V * Z + Lg.ι B₀ * W, ?_⟩
  have hexpand :
      (Lg.ι d * U + Lg.ι F * Lg.ι d * V) * Z + (Lg.ι d * Lg.ι A₀ + Lg.ι F * Lg.ι d * Lg.ι B₀) * W =
        Lg.ι d * (U * Z + Lg.ι A₀ * W) + Lg.ι F * Lg.ι d * (V * Z + Lg.ι B₀ * W) := by
    rw [add_mul, add_mul, mul_add, mul_add, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    abel
  rw [← hexpand, hsum, ← hfgm]
  exact hkey.symm

end GlobalStafford.Certificate

#print axioms GlobalStafford.Certificate.protect_old_chart
