import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Global Stafford for rings of differential operators

Let `k` be a field of characteristic zero and `A` a smooth integral
finitely generated `k`-algebra, the coordinate ring of a smooth integral
affine variety over `k`. Let `D_k(A)` be the ring of `k`-linear finite-order
differential operators on `A` in Grothendieck's sense: `k`-linear
endomorphisms `P` of `A` such that iterated commutators with multiplication
operators eventually vanish. Products in `D_k(A)` are compositions. The
statement is Stafford's same-divisor identity for this ring:

> for every nonzero `d ∈ D_k(A)` there exist `F, R, S ∈ D_k(A)` with
> `1 = d R + F d S`.

Both `d R` and `F d S` are ordered products in the noncommutative ring
`D_k(A)`, so `d D_k(A) + F d D_k(A) = D_k(A)` with the same right divisor
`d` in both summands. Over the polynomial ring `A = k[x₁,…,xₙ]` the ring
`D_k(A)` is the Weyl algebra and the statement is Stafford's Conjecture 3.8
(J. London Math. Soc. (2) 18 (1978), p. 438), proved in the separate
`stafford38-formal` development; this file states the extension to every
smooth integral affine variety.

The statement uses only Mathlib. Smoothness is Mathlib's `Algebra.Smooth`
(formally smooth and of finite presentation), which over a field agrees with
the usual notion. Differential operators are defined below without forming a
subalgebra, so that no closure proof enters the statement; the products are
those of `Module.End k A`, that is, composition of maps. The compared theorem
is `universalStatement`; its `sorry` is the deliberate hole filled by
`Solution.lean`.
-/

universe u

namespace GlobalStaffordChallenge

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]

/-- Multiplication by `a`, as a `k`-linear endomorphism of `A`. -/
def multiplication (a : A) : Module.End k A := LinearMap.mulLeft k a

/-- The commutator `[P, a] = P ∘ a - a ∘ P` of an endomorphism with a
multiplication operator. -/
def commutator (P : Module.End k A) (a : A) : Module.End k A :=
  P * multiplication (k := k) a - multiplication (k := k) a * P

/-- `IsOrderLE n P` says that `P` is a differential operator of order at most
`n`: order `0` operators commute with every multiplication, and `P` has order
at most `n + 1` when every commutator `[P, a]` has order at most `n`. -/
def IsOrderLE : ℕ → Module.End k A → Prop
  | 0, P => ∀ a : A, commutator P a = 0
  | n + 1, P => ∀ a : A, IsOrderLE n (commutator P a)

/-- A finite-order `k`-linear differential operator on `A`. -/
def IsDifferentialOperator (P : Module.End k A) : Prop :=
  ∃ n : ℕ, IsOrderLE n P

end GlobalStaffordChallenge

namespace GlobalStaffordChallenge

open GlobalStaffordChallenge

/-- Global Stafford: for every characteristic-zero field `k`, every smooth
integral finitely generated `k`-algebra `A`, and every nonzero differential
operator `d` on `A`, there are differential operators `F, R, S` on `A` with
`1 = d * R + F * d * S`, the products being compositions of endomorphisms. -/
def UniversalStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (d : Module.End k A),
    IsDifferentialOperator d → d ≠ 0 →
      ∃ F R S : Module.End k A,
        IsDifferentialOperator F ∧ IsDifferentialOperator R ∧
        IsDifferentialOperator S ∧
        (1 : Module.End k A) = d * R + F * d * S

/-- The compared theorem. The proof is supplied by `Solution.lean`. -/
theorem universalStatement : UniversalStatement.{u} := by
  sorry

end GlobalStaffordChallenge
