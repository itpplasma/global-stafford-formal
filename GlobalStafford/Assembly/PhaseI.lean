import GlobalStafford.Assembly.Inputs
import GlobalStafford.Chart.EtaleChartData
import GlobalStafford.Chart.ScalarExtension

/-!
# Phase I assembly (paper §§4-5, `PLAN.md` WP-10)

`PLAN.md` §3, work package WP-10 (`Assembly/PhaseI.lean`). Turns an
`Inputs k A` value (WP-10, `Assembly/Inputs.lean`) into the same-divisor
identity on `D_k(A)`: each chart's `LocalizationInterface` and `S38_poly`
hypothesis feed `GlobalStafford.Descent.exists_bounded_order_sources`
(WP-5, Theorem 4.1) to produce a `BoundedSourceProducer` for every chart,
assembled into a `ChartCover`; `GlobalStafford.Descent.
twoGeneratorIdentity_of_charts` (WP-6, Theorem 5.1) then concludes.

`s38Poly_of_chartData` is the remaining Phase I endpoint: it supplies
`Inputs.chartS38Poly` from étale chart data over `k` and over `K = RatFunc k`
(WP-8, `Chart/EtaleChartData.lean`), a scalar-extension interface between the
two operator rings (WP-9, `Chart/ScalarExtension.lean`), and the imported Weyl
theorem `Stafford38.universalStatement` (via `twoGeneratorIdentity_chart_of_weyl`):
`twoGeneratorIdentity_chart_of_weyl EK : TwoGeneratorIdentity (algebra (RatFunc k) CK)`
feeds `s38Poly_of_scalarExtension I` to conclude `S38Poly k (algebra k C)`. The
étale chart data `E : EtaleChartData k n C` over `k` itself is not needed: the
scalar-extension interface already ties `D = algebra k C` to `DK = algebra
(RatFunc k) CK` as `Polynomial D →+* DK`, so only the chart over `K` is used to
produce the `TwoGeneratorIdentity` input.
-/

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators
  GlobalStafford.Localization GlobalStafford.Localization.LocalizationInterface
  GlobalStafford.Certificate GlobalStafford.Chart GlobalStafford.Descent
open scoped nonZeroDivisors

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

/-- Chart producer (paper Lemma 6.2 over `k(t)`): étale chart data over `K = RatFunc k`,
a scalar-extension interface between the two operator rings, and the imported Weyl
theorem give the polynomial chart hypothesis `S38Poly` of the chart over `k`. The
`Algebra k (algebra (k := RatFunc k) (R := CK))`-style instances that
`ScalarExtensionInterface`'s `DK` slot might otherwise need are not required: the
structure omits them (its fields only reach `DK` through `algebraMap K DK`, never
through a `k`-algebra structure on `DK` itself), so no extra instances have to be
supplied here beyond the ones already on `EtaleChartData (RatFunc k) n CK` and
`ScalarExtensionInterface (k := k) (algebra k C) (RatFunc k) (algebra (RatFunc k) CK)
RatFunc.X`. -/
theorem s38Poly_of_chartData {k : Type u} [Field k] [CharZero k] {n : ℕ}
    {C : Type u} [CommRing C] [Nontrivial C] [Algebra k C]
    [Algebra (MvPolynomial (Fin n) k) C] [IsScalarTower k (MvPolynomial (Fin n) k) C]
    {CK : Type u} [CommRing CK] [Nontrivial CK] [Algebra (RatFunc k) CK]
    [Algebra (MvPolynomial (Fin n) (RatFunc k)) CK]
    [IsScalarTower (RatFunc k) (MvPolynomial (Fin n) (RatFunc k)) CK]
    [OreLocalization.OreSet
      ((Stafford38.WeylIteratedEquivalence.PresentedWeyl (RatFunc k) n)ᵐᵒᵖ)⁰]
    [NoZeroDivisors (Stafford38.WeylIteratedEquivalence.PresentedWeyl (RatFunc k) n)]
    (EK : EtaleChartData (RatFunc k) n CK)
    (I : ScalarExtensionInterface (k := k) (algebra (k := k) (R := C)) (RatFunc k)
      (algebra (k := RatFunc k) (R := CK)) (RatFunc.X : RatFunc k)) :
    S38Poly k (algebra (k := k) (R := C)) :=
  s38Poly_of_scalarExtension _ _ _ _ I (twoGeneratorIdentity_chart_of_weyl EK)

end GlobalStafford.PhaseI

#print axioms GlobalStafford.PhaseI.twoGeneratorIdentity_of_inputs
#print axioms GlobalStafford.PhaseI.universalStatement_of_inputs
#print axioms GlobalStafford.PhaseI.s38Poly_of_chartData
