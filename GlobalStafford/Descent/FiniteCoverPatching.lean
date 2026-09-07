import GlobalStafford.Certificate.OldChartProtection
import GlobalStafford.Certificate.SquaredAnnihilator
import GlobalStafford.Chart.PolynomialS38
import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite-cover patching (paper §5, Theorem 5.1)

`PLAN.md` §3, work package WP-6 (`Descent/FiniteCoverPatching.lean`). Given a
finite principal cover `f_1, …, f_s` of `A` by chart rings `A_{f_i}`, each of
which produces bounded-order sources for every Ore pair `(d, B)` (the
conclusion of Theorem 4.1 / WP-5, taken here as an explicit hypothesis
`BoundedSourceProducer` because WP-5 is developed on a separate branch and is
not available on this branch), and given the right Ore condition on `A`,
every nonzero `d : D_k(A)` admits a same-divisor certificate `1 = d R + F d
S`. This is Theorem 5.1 of the paper.

The proof follows PLAN.md §1 Section 5: induct on the charts, carrying a
single "source" `B` for which a same-divisor certificate has already been
built on every earlier chart; at each step, Theorem 4.1 supplies a new
bounded-order perturbation of `B` that succeeds on the new chart, and
`GlobalStafford.Certificate.protect_old_chart` (Lemma 1.2) shows the same
perturbation still succeeds on every earlier chart, provided the new
exponent is chosen large enough. After all charts are covered, the finitely
many chart certificates are right-cleared to a common power of the
corresponding `f_i`, and a Bézout combination for the ideal `(f_1^m, …,
f_s^m) = A` (from `Ideal.span_pow_eq_top`) assembles them into a single
certificate on `A`.
-/

namespace GlobalStafford.Descent

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators
  GlobalStafford.Certificate GlobalStafford.Localization
  GlobalStafford.Localization.LocalizationInterface

universe u

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]

/-- The conclusion of Theorem 4.1 (WP-5) for the chart `Af` at `f`, as a
predicate: every Ore pair `(d, B)` with `d ≠ 0` admits, for all sufficiently
large `N` (with `H.eval N ≠ 0` for a fixed nonzero `H : Polynomial k`), a
bounded-order perturbation `B + f^{N-l-M} T` of `B` (with `ord T ≤ M`) that
succeeds as a same-divisor source on the chart `Af`. -/
def BoundedSourceProducer (f : A) (Af : Type u) [CommRing Af] [Algebra k Af] [Algebra A Af]
    [IsScalarTower k A Af] [IsLocalization.Away f Af]
    (L : LocalizationInterface (k := k) (A := A) (Af := Af) f) : Prop :=
  ∀ (d B : algebra (k := k) (R := A)), OreData d B → d ≠ 0 →
    ∃ (M l : ℕ) (H : Polynomial k), H ≠ 0 ∧
      ∀ N : ℕ, l + M ≤ N → H.eval (N : k) ≠ 0 →
        ∃ T : algebra (k := k) (R := A), (T : Module.End k A) ∈ order M ∧
          ∃ U V : algebra (k := k) (R := Af),
            (1 : algebra (k := k) (R := Af)) =
              L.ι d * U + L.ι (B + multiplicationD f ^ (N - l - M) * T) * L.ι d * V

/-- Chart data for a finite principal cover of `A`: chart rings `Af i` at
generators `f i` of the unit ideal, each equipped with a `LocalizationInterface`
and a `BoundedSourceProducer` (the Theorem 4.1 conclusion). -/
structure ChartCover (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
    [Algebra k A] where
  /-- Number of charts. -/
  s : ℕ
  /-- The chart generators. -/
  f : Fin s → A
  /-- The chart generators cover: they generate the unit ideal of `A`. -/
  cover : Ideal.span (Set.range f) = ⊤
  /-- The chart rings. -/
  Af : Fin s → Type u
  [instCommRing : ∀ i, CommRing (Af i)]
  [instAlgk : ∀ i, Algebra k (Af i)]
  [instAlgA : ∀ i, Algebra A (Af i)]
  [instTower : ∀ i, IsScalarTower k A (Af i)]
  [instLoc : ∀ i, IsLocalization.Away (f i) (Af i)]
  /-- The localization interface at each chart. -/
  loc : ∀ i, LocalizationInterface (k := k) (A := A) (Af := Af i) (f i)
  /-- Each chart produces bounded-order sources (Theorem 4.1). -/
  producer : ∀ i, BoundedSourceProducer (f i) (Af i) (loc i)

attribute [instance] ChartCover.instCommRing ChartCover.instAlgk ChartCover.instAlgA
  ChartCover.instTower ChartCover.instLoc

end GlobalStafford.Descent
