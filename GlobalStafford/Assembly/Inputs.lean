import GlobalStafford.Descent.BoundedOrderSource
import GlobalStafford.Descent.FiniteCoverPatching

/-!
# Phase I assembly inputs (paper §§4-5, `PLAN.md` WP-10)

`PLAN.md` §3, work package WP-10 (`Assembly/Inputs.lean`). `Inputs k A`
packages, for a single carrier `A`, everything Phase I needs to conclude
the same-divisor identity on `D_k(A)`: a finite principal cover of `A` by
chart rings, a `LocalizationInterface` at each chart (WP-2), the `S38_poly`
hypothesis on each chart (WP-4), that each chart and the global ring have no
zero divisors, and the right Ore condition on `D_k(A)` (paper §5,
`GlobalStafford.Certificate.OreData.of_rightOre`). `Assembly/PhaseI.lean`
turns an `Inputs k A` value into a `ChartCover k A` (feeding `Descent.
exists_bounded_order_sources`, WP-5, into each chart's `BoundedSourceProducer`)
and applies `Descent.twoGeneratorIdentity_of_charts` (WP-6, Theorem 5.1).
-/

namespace GlobalStafford.Assembly

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators
  GlobalStafford.Localization GlobalStafford.Localization.LocalizationInterface
  GlobalStafford.Certificate GlobalStafford.Chart

universe u

/-- Phase I inputs for `A`: a finite principal cover by charts, each equipped with a
`LocalizationInterface` and the `S38_poly` hypothesis, chart and global integrality, and
the right Ore condition on `D_k(A)`. Assembled into `TwoGeneratorIdentity (algebra k A)`
by `twoGeneratorIdentity_of_inputs` in `Assembly/PhaseI.lean`. -/
structure Inputs (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
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
  [instNontrivial : ∀ i, Nontrivial (Af i)]
  [instAlgk : ∀ i, Algebra k (Af i)]
  [instAlgA : ∀ i, Algebra A (Af i)]
  [instTower : ∀ i, IsScalarTower k A (Af i)]
  [instLoc : ∀ i, IsLocalization.Away (f i) (Af i)]
  /-- The localization interface at each chart. -/
  loc : ∀ i, LocalizationInterface (k := k) (A := A) (Af := Af i) (f i)
  /-- Each chart satisfies `S38_poly` (paper Section 4, WP-4). -/
  chartS38Poly : ∀ i, S38Poly k (algebra (k := k) (R := Af i))
  /-- Each chart ring's differential-operator algebra has no zero divisors. -/
  chartDomain : ∀ i, NoZeroDivisors (algebra (k := k) (R := Af i))
  /-- `D_k(A)` has no zero divisors. -/
  globalDomain : NoZeroDivisors (algebra (k := k) (R := A))
  /-- `D_k(A)` satisfies the right Ore condition (paper §5). -/
  rightOre : ∀ x y : algebra (k := k) (R := A), x ≠ 0 → y ≠ 0 →
    ∃ a b, a ≠ 0 ∧ x * a = y * b

attribute [instance] Inputs.instCommRing Inputs.instNontrivial Inputs.instAlgk
  Inputs.instAlgA Inputs.instTower Inputs.instLoc

end GlobalStafford.Assembly
