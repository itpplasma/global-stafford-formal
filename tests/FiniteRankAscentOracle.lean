import GlobalStafford.Chart.FiniteRankAscent
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Oracle test for finite-right-span ascent (Lemma 6.1)

`PLAN.md` WP-7 acceptance test. `Polynomial ℚ` trivially spans itself as a right
`Polynomial ℚ`-module through the identity map: `m = 1`, `s 0 = 1`. This instantiates
`GlobalStafford.Chart.FiniteRightSpan (RingHom.id (Polynomial ℚ))`, an independent
consumer of the three public theorems of `Chart/FiniteRankAscent.lean`, and prints
their axiom dependencies.
-/

namespace GlobalStafford.FiniteRankAscentOracle

open GlobalStafford.Chart
open Polynomial

/-- `Polynomial ℚ` is spanned, as a right `Polynomial ℚ`-module through the identity
homomorphism, by the single element `1` (`m = 1`, `s 0 = 1`): for every `x`, take
`τ = 1 ≠ 0` and `t 0 = x`, so `x * φ 1 = 1 * φ x`. -/
theorem finiteRightSpan_id : FiniteRightSpan (RingHom.id (Polynomial ℚ)) := by
  refine ⟨1, fun _ => 1, fun x => ⟨1, one_ne_zero, fun _ => x, ?_⟩⟩
  simp

/-- Independent oracle check: `finiteRightSpan_id`, unfolded to the concrete polynomial
`X + 1`, reproduces the same fraction datum `(τ, t) = (1, X + 1)` by direct
computation, without appealing to `finiteRightSpan_id` itself. -/
theorem finiteRightSpan_id_apply_oracle :
    (X + 1 : Polynomial ℚ) * (RingHom.id (Polynomial ℚ)) 1 =
      ∑ i : Fin 1, (fun _ : Fin 1 => (1 : Polynomial ℚ)) i *
        (RingHom.id (Polynomial ℚ)) ((fun _ : Fin 1 => (X + 1 : Polynomial ℚ)) i) := by
  simp

/-- Applying `exists_mul_eq_of_finiteRightSpan` to `finiteRightSpan_id` and the nonzero
polynomial `X`: since `φ = id`, the witnesses are trivially `y = 1`, `a = X`. -/
example : ∃ (y : Polynomial ℚ) (a : Polynomial ℚ), a ≠ 0 ∧ (X : Polynomial ℚ) * y = a :=
  exists_mul_eq_of_finiteRightSpan (RingHom.id (Polynomial ℚ)) finiteRightSpan_id X
    (X_ne_zero)

end GlobalStafford.FiniteRankAscentOracle

#print axioms GlobalStafford.Chart.exists_mul_eq_of_finiteRightSpan
#print axioms GlobalStafford.Chart.twoGeneratorIdentity_of_finiteRightSpan
#print axioms GlobalStafford.Chart.rightOre_of_finiteRightSpan
