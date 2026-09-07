import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Cast.Field
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Polynomial evaluation over a noncommutative `k`-algebra

Generic part of WP-4 (`PLAN.md`, Section 3, "WP-4 Polynomial evaluation and the
right-moved conjugation"), feeding the right-moved conjugation argument of
Section 4 of the paper proof. For a possibly noncommutative `k`-algebra `D`,
`Polynomial D` is still a semiring, and `Polynomial.X` is central in it; this
lets us evaluate a polynomial over `D` at a natural number `N` (i.e. at the
central element `(N : D)`) as a ring homomorphism `evalNat N`. We also
transport a polynomial `h` over the base field `k` into `Polynomial D` via
`scalarPoly`, and record that its image is central and evaluates compatibly
with `evalNat`. The key generic fact used downstream (Section 4) is
`eq_zero_of_forall_evalNat_eq_zero`: a polynomial over `D` that vanishes at
every natural number is the zero polynomial. We also package the generalized
binomial coefficient `C(t, j)` as a polynomial `binomPoly j` over `k`.

Chart-specific declarations (`rho`, `squaredInput`) are not part of this file;
they depend on WP-1/WP-2 operator infrastructure and are added later.
-/

namespace GlobalStafford.Conjugation

open Polynomial

section CommRingSection

variable {k D : Type*} [CommRing k] [Ring D] [Algebra k D]

/-- Evaluation of a polynomial over `D` at a natural number `N`, i.e. at the central
element `(N : D)`, as a ring homomorphism. `Polynomial D` is a semiring even when `D`
is noncommutative, and `(N : D)` is central (`Nat.cast_commute`), so `eval₂RingHom'`
applies with the identity coefficient map. -/
noncomputable def evalNat (N : ℕ) : Polynomial D →+* D :=
  Polynomial.eval₂RingHom' (RingHom.id D) (N : D) (fun a => (Nat.cast_commute N a).symm)

theorem evalNat_apply (N : ℕ) (p : Polynomial D) :
    evalNat N p = p.eval₂ (RingHom.id D) (N : D) := rfl

@[simp] theorem evalNat_C (N : ℕ) (a : D) : evalNat N (Polynomial.C a) = a := by
  rw [evalNat_apply, Polynomial.eval₂_C, RingHom.id_apply]

@[simp] theorem evalNat_X (N : ℕ) : evalNat N (Polynomial.X : Polynomial D) = (N : D) := by
  rw [evalNat_apply, Polynomial.eval₂_X]

@[simp] theorem evalNat_monomial (N i : ℕ) (a : D) :
    evalNat N (Polynomial.monomial i a) = a * (N : D) ^ i := by
  rw [evalNat_apply, Polynomial.eval₂_monomial, RingHom.id_apply]

theorem evalNat_natCast_pow (N i : ℕ) :
    evalNat N ((Polynomial.X : Polynomial D) ^ i) = (N : D) ^ i := by
  rw [map_pow, evalNat_X]

/-- The image of a `k`-polynomial `h` in `Polynomial D`, via the coefficient map
`algebraMap k D`. Its image consists of central elements of `Polynomial D`
(`scalarPoly_commute`), which is what lets it play the role of a central scalar in
the right-moved conjugation argument of Section 4. -/
noncomputable def scalarPoly (h : Polynomial k) : Polynomial D := h.map (algebraMap k D)

theorem scalarPoly_C (c : k) :
    scalarPoly (D := D) (Polynomial.C c) = Polynomial.C (algebraMap k D c) :=
  Polynomial.map_C _

theorem scalarPoly_X : scalarPoly (D := D) (Polynomial.X : Polynomial k) = Polynomial.X :=
  Polynomial.map_X _

@[simp] theorem scalarPoly_add (h₁ h₂ : Polynomial k) :
    scalarPoly (D := D) (h₁ + h₂) = scalarPoly h₁ + scalarPoly h₂ :=
  Polynomial.map_add _

@[simp] theorem scalarPoly_mul (h₁ h₂ : Polynomial k) :
    scalarPoly (D := D) (h₁ * h₂) = scalarPoly h₁ * scalarPoly h₂ :=
  Polynomial.map_mul _

@[simp] theorem scalarPoly_one : scalarPoly (D := D) (1 : Polynomial k) = 1 :=
  Polynomial.map_one _

/-- The image of `Polynomial.C c` under `scalarPoly` commutes with every element of
`Polynomial D`: `algebraMap k D c` is central in `D` (`Algebra.commutes`), hence so is
its image under `Polynomial.C`. -/
theorem central_C_commute (c : k) (q : Polynomial D) :
    Commute (Polynomial.C (algebraMap k D c)) q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => exact hp.add_right hq
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      refine Commute.mul_right ?_ ((Polynomial.commute_X _).symm.pow_right n)
      show Polynomial.C (algebraMap k D c) * Polynomial.C a
          = Polynomial.C a * Polynomial.C (algebraMap k D c)
      rw [← Polynomial.C_mul, ← Polynomial.C_mul, Algebra.commutes]

/-- `scalarPoly h` is central in `Polynomial D`: it commutes with every `q : Polynomial D`.
Paper Section 4 relies on this to move scalar coefficients of a polynomial identity past
the noncommutative variable `t`. -/
theorem scalarPoly_commute (h : Polynomial k) (q : Polynomial D) :
    Commute (scalarPoly (D := D) h) q := by
  induction h using Polynomial.induction_on with
  | C c => rw [scalarPoly_C]; exact central_C_commute c q
  | add p q' hp hq' => rw [scalarPoly_add]; exact hp.add_left hq'
  | monomial n a ih =>
      have hX : Commute (Polynomial.X : Polynomial D) q := Polynomial.commute_X q
      have hstep : scalarPoly (D := D) (Polynomial.C a * Polynomial.X ^ (n + 1))
          = scalarPoly (D := D) (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by
        rw [pow_succ, ← mul_assoc, scalarPoly_mul, scalarPoly_X]
      rw [hstep]
      exact ih.mul_left hX

theorem evalNat_scalarPoly (h : Polynomial k) (N : ℕ) :
    evalNat N (scalarPoly (D := D) h) = algebraMap k D (h.eval (N : k)) := by
  rw [scalarPoly, evalNat_apply, Polynomial.eval₂_map, RingHom.id_comp,
    ← map_natCast (algebraMap k D) N, Polynomial.eval₂_at_apply]

end CommRingSection

section FieldSection

variable {k D : Type*} [Field k] [Ring D] [Algebra k D]

/-- `scalarPoly` is injective over a field `k` when `D` is nontrivial: the coefficient
map `algebraMap k D` is injective (`k` is a simple ring, `D` is nontrivial), and
`Polynomial.map` of an injective ring homomorphism is injective. -/
theorem scalarPoly_injective [Nontrivial D] :
    Function.Injective (scalarPoly (k := k) (D := D)) :=
  Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective k D)

theorem scalarPoly_ne_zero [Nontrivial D] {h : Polynomial k} (hh : h ≠ 0) :
    scalarPoly (D := D) h ≠ 0 := by
  have := (scalarPoly_injective (k := k) (D := D)).ne (a₁ := h) (a₂ := 0) hh
  rwa [show scalarPoly (D := D) (0 : Polynomial k) = 0 from Polynomial.map_zero _] at this

/-- A polynomial over a `k`-vector space `D` vanishing at every natural number is zero.
Paper Section 4: this is what lets Theorem 4.1 pass from a polynomial identity to a
concrete identity at a sufficiently large natural number `N`. -/
theorem eq_zero_of_forall_evalNat_eq_zero [CharZero k] (p : Polynomial D)
    (hp : ∀ N : ℕ, evalNat N p = 0) : p = 0 := by
  have hcoeff : ∀ φ : Module.Dual k D, ∀ i : ℕ, φ (p.coeff i) = 0 := by
    intro φ
    set q : Polynomial k := ∑ i ∈ p.support, Polynomial.C (φ (p.coeff i)) * Polynomial.X ^ i
      with hq
    have hcoeff_q : ∀ n, q.coeff n = φ (p.coeff n) := by
      intro n
      simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · rw [Polynomial.notMem_support_iff.mp h, map_zero]
    have heval : ∀ N : ℕ, q.eval (N : k) = φ (evalNat N p) := by
      intro N
      have hEval : evalNat N p = ∑ i ∈ p.support, p.coeff i * (N : D) ^ i := by
        rw [evalNat_apply, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
        simp
      rw [hEval, map_sum, hq]
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc : (N : k) ^ i • p.coeff i = p.coeff i * (N : D) ^ i := by
        rw [Algebra.smul_def, Algebra.commutes, map_pow, map_natCast]
      rw [mul_comm, ← smul_eq_mul, ← map_smul, hc]
    have hroot : ∀ N : ℕ, q.IsRoot (N : k) := by
      intro N
      show q.eval (N : k) = 0
      rw [heval N, hp N, map_zero]
    have hinf : Set.Infinite { x : k | q.IsRoot x } :=
      Set.Infinite.mono (Set.range_subset_iff.mpr hroot)
        (Set.infinite_range_of_injective Nat.cast_injective)
    have hq0 : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q hinf
    intro i
    rw [← hcoeff_q i, hq0, Polynomial.coeff_zero]
  ext i
  have hi : ∀ φ : Module.Dual k D, φ (p.coeff i) = 0 := fun φ => hcoeff φ i
  rw [(Module.forall_dual_apply_eq_zero_iff k (p.coeff i)).mp hi, Polynomial.coeff_zero]

end FieldSection

section BinomSection

variable {k : Type*} [Field k] [CharZero k]

/-- Generalized binomial coefficient as a polynomial: `C(t, j)`, given by
`(1/j!) t(t-1)⋯(t-j+1)`. Paper Section 4. -/
noncomputable def binomPoly (j : ℕ) : Polynomial k :=
  Polynomial.C ((j.factorial : k)⁻¹) * descPochhammer k j

theorem binomPoly_eval_nat (j N : ℕ) :
    (binomPoly (k := k) j).eval (N : k) = (N.choose j : k) := by
  rw [binomPoly, Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.choose_eq_descFactorial_div_factorial,
    Nat.cast_div_charZero (Nat.factorial_dvd_descFactorial N j)]
  ring

theorem binomPoly_comp_nsmul_eval (m j N : ℕ) :
    ((binomPoly (k := k) j).comp (m • Polynomial.X)).eval (N : k) = ((m * N).choose j : k) := by
  rw [Polynomial.eval_comp, Polynomial.eval_smul, Polynomial.eval_X, nsmul_eq_mul,
    ← Nat.cast_mul, binomPoly_eval_nat]

end BinomSection

section BinomScalarSection

variable {k D : Type*} [Field k] [CharZero k] [Ring D] [Algebra k D]

theorem evalNat_scalarPoly_binomPoly (j N : ℕ) :
    evalNat N (scalarPoly (D := D) (binomPoly (k := k) j)) = algebraMap k D (N.choose j : k) := by
  rw [evalNat_scalarPoly, binomPoly_eval_nat]

end BinomScalarSection

end GlobalStafford.Conjugation

#print axioms GlobalStafford.Conjugation.eq_zero_of_forall_evalNat_eq_zero
#print axioms GlobalStafford.Conjugation.binomPoly_eval_nat
#print axioms GlobalStafford.Conjugation.scalarPoly_commute
#print axioms GlobalStafford.Conjugation.evalNat_scalarPoly
