import GlobalStafford.Assembly.Closure

/-!
# Solution

Transport of the proved Global Stafford theorem to the Palomar statement.
The definitions of `Challenge.lean` are restated verbatim in
`GlobalStafford/Assembly/ChallengeTransport.lean` (this file does not import
`Challenge`); the theorem below has the exact name and type of the compared
declaration `GlobalStaffordChallenge.universalStatement`.
-/

namespace GlobalStaffordChallenge

universe u

/-- Global Stafford, in the Mathlib-only form of `Challenge.lean`. -/
theorem universalStatement : UniversalStatement.{u} :=
  GlobalStafford.challengeStatement.{u}

end GlobalStaffordChallenge

#print axioms GlobalStaffordChallenge.universalStatement
