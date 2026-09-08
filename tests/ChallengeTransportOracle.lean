import GlobalStaffordChallenge
import Mathlib.Algebra.Polynomial.Basic

/-!
# Oracle test for the Challenge definitions used by WP-19 transport

`PLAN.md` WP-19 acceptance test. `GlobalStafford/Assembly/ChallengeTransport.lean`
restates `Challenge.lean`'s definitions verbatim under the same names, so this
file imports `Challenge` alone (never `ChallengeTransport`, whose declarations
would clash on the same names) and exercises `Challenge.lean`'s own
`IsOrderLE`, `commutator`, and `multiplication` on a concrete carrier,
independently of the restated copy: multiplication by any `a : Polynomial ℚ`
is an order-`0` differential operator, since multiplication operators
commute with each other. This is an independent behavioral oracle on the
frozen file, not a restatement of the transport proof.
-/

namespace GlobalStaffordChallengeOracle

open GlobalStaffordChallenge

/-- Oracle: multiplication by any polynomial `a` is order `≤ 0`, i.e. its
commutator with every multiplication operator vanishes, since
`(a * (b * x)) = (b * (a * x))` by commutativity of `Polynomial ℚ`. -/
theorem multiplication_isOrderLE_zero (a : Polynomial ℚ) :
    IsOrderLE 0 (multiplication (k := ℚ) (A := Polynomial ℚ) a) := by
  simp only [IsOrderLE, GlobalStaffordChallenge.commutator, multiplication]
  intro b
  ext x
  simp [mul_left_comm]

end GlobalStaffordChallengeOracle

#print axioms GlobalStaffordChallengeOracle.multiplication_isOrderLE_zero
