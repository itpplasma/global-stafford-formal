import AlgebraicAnalysis.DifferentialOperators.Basic
import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity
import GlobalStafford.Assembly.PhaseI

/-!
# Challenge transport (paper §5, `PLAN.md` WP-19)

This file restates the definitions of `Challenge.lean` verbatim, under the
same namespace `GlobalStaffordChallenge` and with the same names, without
importing `Challenge.lean` (which is frozen and carries the deliberate
`sorry` that this development discharges). Restating rather than importing
lets `Solution.lean` import both this file and `Challenge.lean` so that a
comparator can match `GlobalStaffordChallenge.UniversalStatement` here
against the one in `Challenge.lean` by name; Lean itself checks nothing
about that correspondence, so keeping the two texts identical is a human/CI
responsibility (`scripts/verify.sh`).

The transport theorems show that the Challenge's `IsOrderLE`/
`IsDifferentialOperator` predicates on `Module.End k A` coincide with the
`AlgebraicAnalysis.DifferentialOperators.order`/`algebra` filtration
(`isOrderLE_iff_mem_order`, `isDifferentialOperator_iff_mem_algebra`), since
`multiplication` and `commutator` are defined by the identical term
`LinearMap.mulLeft k a` on both sides. `challenge_of_twoGeneratorIdentity`
then transports a `TwoGeneratorIdentity (algebra k A)` witness for a single
nonzero differential operator `d` to the Challenge-shaped existential, and
`universalStatement_of_universal` / `universalStatement_of_inputs'`
quantify this over every `k` and `A` to produce
`GlobalStaffordChallenge.UniversalStatement`.
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

end GlobalStaffordChallenge

/-!
## Transport

`multiplication` and `commutator` above are defined by the same terms as
`AlgebraicAnalysis.DifferentialOperators.multiplication` and `.commutator`
(both `LinearMap.mulLeft k a` and the same difference of products), so the
two order predicates coincide by induction on `n`, unfolding one step at a
time with `mem_order_zero_iff` / `mem_order_succ_iff`.
-/

namespace GlobalStafford.Assembly

open AlgebraicAnalysis.DifferentialOperators

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]

theorem isOrderLE_iff_mem_order (n : ℕ) (P : Module.End k A) :
    GlobalStaffordChallenge.IsOrderLE n P ↔ P ∈ order (k := k) (R := A) n := by
  induction n generalizing P with
  | zero =>
      show (∀ a : A, GlobalStaffordChallenge.commutator P a = 0) ↔ _
      rw [mem_order_zero_iff]
      exact Iff.rfl
  | succ n ih =>
      show (∀ a : A, GlobalStaffordChallenge.IsOrderLE n
        (GlobalStaffordChallenge.commutator P a)) ↔ _
      rw [mem_order_succ_iff]
      constructor
      · intro h a; exact (ih _).1 (h a)
      · intro h a; exact (ih _).2 (h a)

theorem isDifferentialOperator_iff_mem_algebra (P : Module.End k A) :
    GlobalStaffordChallenge.IsDifferentialOperator P ↔
      P ∈ algebra (k := k) (R := A) := by
  unfold GlobalStaffordChallenge.IsDifferentialOperator
  rw [mem_algebra_iff]
  exact exists_congr fun n => isOrderLE_iff_mem_order n P

/-- Coerce a `TwoGeneratorIdentity (algebra k A)` witness for a single nonzero
differential operator `d` down to the Challenge-shaped existential over
`Module.End k A`. -/
theorem challenge_of_twoGeneratorIdentity {k A : Type u} [Field k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (h : AlgebraicAnalysis.TwoGeneratorIdentity
      (algebra (k := k) (R := A)))
    (d : Module.End k A) (hd : GlobalStaffordChallenge.IsDifferentialOperator d)
    (hne : d ≠ 0) :
    ∃ F R S : Module.End k A,
      GlobalStaffordChallenge.IsDifferentialOperator F ∧
      GlobalStaffordChallenge.IsDifferentialOperator R ∧
      GlobalStaffordChallenge.IsDifferentialOperator S ∧
      (1 : Module.End k A) = d * R + F * d * S := by
  set d' : algebra (k := k) (R := A) :=
    ⟨d, (isDifferentialOperator_iff_mem_algebra d).1 hd⟩ with hd'_def
  have hd'ne : d' ≠ 0 := by
    intro hcontra
    apply hne
    have := congrArg Subtype.val hcontra
    simpa [hd'_def] using this
  obtain ⟨F', R', S', hFRS⟩ := h d' hd'ne
  refine ⟨(F' : Module.End k A), (R' : Module.End k A), (S' : Module.End k A),
    (isDifferentialOperator_iff_mem_algebra _).2 F'.2,
    (isDifferentialOperator_iff_mem_algebra _).2 R'.2,
    (isDifferentialOperator_iff_mem_algebra _).2 S'.2, ?_⟩
  have hcoe : ((1 : algebra (k := k) (R := A)) : Module.End k A) =
      ((d' * R' + F' * d' * S' : algebra (k := k) (R := A)) : Module.End k A) :=
    congrArg Subtype.val hFRS
  simpa [hd'_def] using hcoe

theorem universalStatement_of_universal
    (h : ∀ (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A]
      [IsDomain A] [Algebra k A] [Algebra.Smooth k A],
      AlgebraicAnalysis.TwoGeneratorIdentity
        (algebra (k := k) (R := A))) :
    GlobalStaffordChallenge.UniversalStatement.{u} := by
  intro k _ _ A _ _ _ _ d hd hne
  exact challenge_of_twoGeneratorIdentity (h k A) d hd hne

theorem universalStatement_of_inputs'
    (hI : ∀ (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A]
      [IsDomain A] [Algebra k A] [Algebra.Smooth k A],
      GlobalStafford.Assembly.Inputs k A) :
    GlobalStaffordChallenge.UniversalStatement.{u} :=
  universalStatement_of_universal fun k _ _ A _ _ _ _ =>
    GlobalStafford.PhaseI.twoGeneratorIdentity_of_inputs (hI k A)

end GlobalStafford.Assembly

#print axioms GlobalStafford.Assembly.challenge_of_twoGeneratorIdentity
#print axioms GlobalStafford.Assembly.universalStatement_of_universal
#print axioms GlobalStafford.Assembly.universalStatement_of_inputs'
