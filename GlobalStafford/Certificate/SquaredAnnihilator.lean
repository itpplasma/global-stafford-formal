import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Squared annihilator certificate (paper §3)

`PLAN.md` §3, WP-2 (`Certificate/SquaredAnnihilator.lean`). Formalizes the
paper's Section 3 computation: given `c = d a`, `B d c = d b₀`, and a
squared-annihilator certificate `1 = e² U + W e² V` for `e = c h d`, produces
a certificate `1 = d R + F d S` with `F = B + W c h`. Also formalizes the
right Ore choice (3.1) of the pair `(c, b₀)` producing an `OreData`
structure.
-/

namespace GlobalStafford.Certificate

variable {Λ : Type*} [Ring Λ]

/-- Paper §3: the squared-annihilator certificate. If `c = d a`,
`B d c = d b₀`, and `e = c h d` admits a certificate `1 = e * e * U +
W * (e * e) * V`, then `F := B + W * c * h` gives a certificate
`1 = d R + F d S` with `R = a h d (c h d) U - b₀ h d V` and
`S = (c h d) V`. -/
theorem certificate_of_square (d a b₀ B c h U W V : Λ)
    (hc : c = d * a) (hb : B * d * c = d * b₀)
    (hcert : (1 : Λ) = (c * h * d) * (c * h * d) * U + W * ((c * h * d) * (c * h * d)) * V) :
    (1 : Λ) = d * (a * h * d * (c * h * d) * U - b₀ * h * d * V)
              + (B + W * c * h) * d * ((c * h * d) * V) := by
  subst hc
  rw [mul_sub]
  have key : d * (b₀ * h * d * V) = B * d * (d * a) * h * d * V := by
    have e1 : d * (b₀ * h * d * V) = (d * b₀) * (h * d * V) := by noncomm_ring
    rw [e1, ← hb]
    noncomm_ring
  rw [key]
  have final :
      d * (a * h * d * (d * a * h * d) * U) - B * d * (d * a) * h * d * V +
          (B + W * (d * a) * h) * d * (d * a * h * d * V) =
        (d * a * h * d) * (d * a * h * d) * U + W * ((d * a * h * d) * (d * a * h * d)) * V := by
    noncomm_ring
  rw [final]
  exact hcert

/-- Paper (3.1): the right Ore choice for a nonzero `d` and arbitrary `B`. -/
structure OreData (d B : Λ) where
  /-- The Ore denominator `c = d a`. -/
  c : Λ
  /-- The Ore numerator `a`. -/
  a : Λ
  /-- The Ore companion `b₀` with `B d c = d b₀`. -/
  b₀ : Λ
  hc : c = d * a
  hne : c ≠ 0
  hb : B * d * c = d * b₀

/-- The right Ore choice exists whenever `Λ` satisfies the right Ore
condition (applied to `B d d` and `d`). -/
theorem OreData.of_rightOre [NoZeroDivisors Λ] [Nontrivial Λ]
    (hOre : ∀ x y : Λ, x ≠ 0 → y ≠ 0 → ∃ a b : Λ, a ≠ 0 ∧ x * a = y * b)
    (d B : Λ) (hd : d ≠ 0) : Nonempty (OreData d B) := by
  by_cases hBdd : B * d * d = 0
  · refine ⟨⟨d, 1, 0, by rw [mul_one], hd, ?_⟩⟩
    rw [mul_zero]
    exact hBdd
  · obtain ⟨a, b, ha, hab⟩ := hOre (B * d * d) d hBdd hd
    refine ⟨⟨d * a, a, b, rfl, mul_ne_zero hd ha, ?_⟩⟩
    show B * d * (d * a) = d * b
    rw [← mul_assoc]
    exact hab

end GlobalStafford.Certificate
