import GlobalStafford.Assembly.Inputs

/-!
# Phase I assembly (paper §§4-5, `PLAN.md` WP-10)

`PLAN.md` §3, work package WP-10 (`Assembly/PhaseI.lean`). Turns an
`Inputs k A` value (WP-10, `Assembly/Inputs.lean`) into the same-divisor
identity on `D_k(A)`: each chart's `LocalizationInterface` and `S38_poly`
hypothesis feed `GlobalStafford.Descent.exists_bounded_order_sources`
(WP-5, Theorem 4.1) to produce a `BoundedSourceProducer` for every chart,
assembled into a `ChartCover`; `GlobalStafford.Descent.
twoGeneratorIdentity_of_charts` (WP-6, Theorem 5.1) then concludes.

`s38Poly_of_chartData`, the remaining Phase I endpoint that supplies
`Inputs.chartS38Poly` from étale chart data and the imported Weyl theorem
(WP-8), needs the scalar-extension development of WP-8/WP-9 and is added
once WP-8 is merged; it is not part of this file.
-/

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators
  GlobalStafford.Localization GlobalStafford.Localization.LocalizationInterface
  GlobalStafford.Certificate GlobalStafford.Chart GlobalStafford.Descent

universe u

namespace GlobalStafford.Assembly

/-- Every chart of `I` produces bounded-order sources (Theorem 4.1, WP-5), using the
chart's `LocalizationInterface`, `S38_poly` hypothesis, and integral-domain instance. -/
noncomputable def Inputs.toChartCover {k A : Type u} [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] (I : Inputs k A) : ChartCover k A where
  s := I.s
  f := I.f
  cover := I.cover
  Af := I.Af
  loc := I.loc
  producer := fun i d B od hd =>
    haveI := I.chartDomain i
    exists_bounded_order_sources (I.f i) (I.loc i) (I.chartS38Poly i) d B od hd

end GlobalStafford.Assembly

namespace GlobalStafford.PhaseI

open GlobalStafford.Assembly

/-- Phase I terminal declaration: an `Inputs k A` value supplies the same-divisor
identity on `D_k(A)` (paper §5, Theorem 5.1). -/
theorem twoGeneratorIdentity_of_inputs {k A : Type u} [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] (I : Inputs k A) :
    AlgebraicAnalysis.TwoGeneratorIdentity (algebra (k := k) (R := A)) :=
  haveI := I.globalDomain
  twoGeneratorIdentity_of_charts I.toChartCover I.rightOre

/-- The universal statement, quantified over `k` and `A`, taking `Inputs k A` as
hypothesis: the Phase I shape of the Global Stafford theorem. -/
def UniversalStatementOfInputs : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A],
    Inputs k A → AlgebraicAnalysis.TwoGeneratorIdentity (algebra (k := k) (R := A))

theorem universalStatement_of_inputs : UniversalStatementOfInputs.{u} :=
  fun _ _ _ _ _ _ _ I => twoGeneratorIdentity_of_inputs I

end GlobalStafford.PhaseI

#print axioms GlobalStafford.PhaseI.twoGeneratorIdentity_of_inputs
#print axioms GlobalStafford.PhaseI.universalStatement_of_inputs
