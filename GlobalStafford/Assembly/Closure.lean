import GlobalStafford.Assembly.ChallengeTransport
import GlobalStafford.Assembly.Inputs
import GlobalStafford.Chart.ChartDataOverK
import GlobalStafford.Chart.ChartDomain
import GlobalStafford.Chart.EtaleDerivations
import GlobalStafford.Chart.GenericFibre
import GlobalStafford.Chart.SmoothCover
import GlobalStafford.Chart.WeylActionInjective
import GlobalStafford.Localization.Construction
import GlobalStafford.Weyl.OreDomain

/-!
# Closure: global domain, global right Ore, `Inputs`, and the universal statement

`PLAN.md` §4, work package WP-18 (`Assembly/Closure.lean`). This is the terminal
Phase II file. It packages a single `EtaleCoordinateChart` (WP-17) into the
per-chart data (`chartDomain`, `chartS38Poly`, `chartData`, `chartRightOre`)
Phase I needs, transports domain and right-Ore from a chart `Localization.Away f`
to the global ring `A` (`noZeroDivisors_of_chart`, `rightOre_of_chart`, using the
`LocalizationInterface` construction of WP-11), and assembles a value of
`Inputs k A` (WP-10) from the finite étale cover of WP-17, closing the two
remaining Phase I leaves recorded in `PLAN.md` §7 (`Inputs.globalDomain`,
`Inputs.rightOre`). `Chart.rightOre_chart`'s injectivity hypothesis on
`weylAction` is discharged by WP-18a's `Chart.weylAction_injective`, applied to
`chartData X`, which is built directly (not through `Chart.etaleChartData_of_fields`'s
`Classical.choice`) so that its `«∂»` field is *definitionally* `liftDerivation`.
-/

namespace GlobalStafford

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators
open GlobalStafford.Chart GlobalStafford.Localization
  GlobalStafford.Localization.LocalizationInterface GlobalStafford.Assembly
open scoped nonZeroDivisors

universe u

/-! ## 1. Chart-level packaging -/

section ChartLevel

variable {k : Type u} [Field k] [CharZero k] {C : Type u} [CommRing C] [IsDomain C] [Algebra k C]

/-- The chart operator ring `D_k(C)` has no zero divisors, for `C` étale over
`MvPolynomial (Fin X.n) k` via the `EtaleCoordinateChart` data `X` (WP-14,
`noZeroDivisors_algebra_of_etale`, fed by the injectivity of `X`'s coordinate
algebra map, WP-13's `algebraMap_injective_of_etale`). -/
theorem chartDomain (X : EtaleCoordinateChart k C) :
    NoZeroDivisors (algebra (k := k) (R := C)) :=
  letI := X.alg
  haveI := X.tower
  haveI := X.etale
  GlobalStafford.Chart.noZeroDivisors_algebra_of_etale (k := k) (n := X.n) (C := C)
    GlobalStafford.Chart.algebraMap_injective_of_etale

/-- The chart `S38Poly` hypothesis of `C`, closing the leaf `Inputs.chartS38Poly`
(WP-10) for this chart, via `Chart.s38Poly_chart` (WP-18b). -/
theorem chartS38Poly (X : EtaleCoordinateChart k C) :
    S38Poly k (algebra (k := k) (R := C)) :=
  letI := X.alg
  haveI := X.tower
  haveI := X.etale
  GlobalStafford.Chart.s38Poly_chart (k := k) (n := X.n) (C := C) (chartDomain X)

/-- The étale chart data of `C` (WP-8's `EtaleChartData`), built directly (rather
than through `Chart.etaleChartData_of_fields`'s `Classical.choice`) from the
derivation-and-rigidity fields of WP-12 (`liftDerivation`, `liftDerivation_coord`,
`liftDerivation_comm`, `coordinateRigidity`), the finite generic fibre and
injectivity of the coordinate algebra map (WP-13), and `chartDomain`, so that its
`«∂»` field is definitionally `liftDerivation` (needed by WP-18a's
`weylAction_injective`). -/
noncomputable def chartData (X : EtaleCoordinateChart k C) :
    letI := X.alg
    haveI := X.tower
    haveI := X.etale
    EtaleChartData k X.n C :=
  letI := X.alg
  haveI := X.tower
  haveI := X.etale
  { «∂» := GlobalStafford.Chart.liftDerivation
    «∂_coord» := GlobalStafford.Chart.liftDerivation_coord
    «∂_comm» := GlobalStafford.Chart.liftDerivation_comm
    coordinateRigidity := GlobalStafford.Chart.coordinateRigidity
    finiteGenericFibre :=
      GlobalStafford.Chart.finiteGenericFibre_of_etale (k := k) (n := X.n) (C := C)
    algebraMap_ne_zero :=
      GlobalStafford.Chart.algebraMap_ne_zero_of_etale (k := k) (n := X.n) (C := C)
    noZeroDivisors := chartDomain X }

/-- The right Ore condition on `D_k(C)`, transported from the presented Weyl
algebra `A_{X.n}(k)` (WP-15) via `Chart.rightOre_chart` (WP-8), using injectivity
of the Weyl action of `chartData X` (WP-18a's `Chart.weylAction_injective`,
applicable because `(chartData X).«∂» = liftDerivation` definitionally). -/
theorem chartRightOre (X : EtaleCoordinateChart k C) :
    ∀ x y : algebra (k := k) (R := C), x ≠ 0 → y ≠ 0 → ∃ a b, a ≠ 0 ∧ x * a = y * b :=
  letI := X.alg
  haveI := X.tower
  haveI := X.etale
  GlobalStafford.Chart.rightOre_chart (chartData X)
    (GlobalStafford.Chart.weylAction_injective (chartData X) (fun _ => rfl)
      GlobalStafford.Chart.algebraMap_injective_of_etale)

end ChartLevel

/-! ## 2. Global domain and global right Ore from a single chart -/

section GlobalFromChart

variable {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- `D_k(A)` has no zero divisors, given that the chart `D_k(A_f)` at some nonzero
`f : A` has no zero divisors: `ι` of the `LocalizationInterface` (WP-11) is an
injective ring homomorphism into a ring with no zero divisors. -/
theorem noZeroDivisors_of_chart (f : A) (hf : f ≠ 0)
    (hC : NoZeroDivisors (algebra (k := k) (R := Localization.Away f))) :
    NoZeroDivisors (algebra (k := k) (R := A)) :=
  haveI := hC
  let L := localizationInterfaceAway (k := k) (A := A) f hf
  Function.Injective.noZeroDivisors L.ι L.ι_injective (map_zero L.ι) (map_mul L.ι)

/-- The right Ore condition on `D_k(A)`, transported from the chart `D_k(A_f)`
at some nonzero `f : A` (WP-11's `LocalizationInterface`, `rightClearance_pair`):
clear `x, y ≠ 0` through `ι` to `ι x, ι y ≠ 0`, apply right Ore in the chart to
get `a', b'` with `a' ≠ 0` and `ι x * a' = ι y * b'`, right-clear `a', b'` by a
common power of `multiplicationD f` to `a, b` with `ι a = a' * f^m`,
`ι b = b' * f^m`; injectivity of `ι` gives `x * a = y * b`, and `a ≠ 0` because
`a' * f^m ≠ 0` (`f^m` is a unit, `a' ≠ 0`). -/
theorem rightOre_of_chart (f : A) (hf : f ≠ 0)
    (hOreC : ∀ x y : algebra (k := k) (R := Localization.Away f), x ≠ 0 → y ≠ 0 →
      ∃ a b, a ≠ 0 ∧ x * a = y * b) :
    ∀ x y : algebra (k := k) (R := A), x ≠ 0 → y ≠ 0 → ∃ a b, a ≠ 0 ∧ x * a = y * b := by
  intro x y hx hy
  set L := localizationInterfaceAway (k := k) (A := A) f hf with hLdef
  have hLx : L.ι x ≠ 0 := fun h => hx (L.ι_injective (by rw [h, map_zero]))
  have hLy : L.ι y ≠ 0 := fun h => hy (L.ι_injective (by rw [h, map_zero]))
  obtain ⟨a', b', ha', hab'⟩ := hOreC (L.ι x) (L.ι y) hLx hLy
  obtain ⟨m, a, b, ha, hb⟩ := L.rightClearance_pair a' b'
  refine ⟨a, b, ?_, ?_⟩
  · intro ha0
    apply ha'
    have hunit : IsUnit (multiplicationD (k := k) (A := Localization.Away f)
        (algebraMap A (Localization.Away f) f) ^ m) :=
      (LocalizationInterface.f_isUnit (k := k) f).pow m
    have hL0 : L.ι a = 0 := by rw [ha0, map_zero]
    exact (hunit.mul_left_eq_zero).mp (ha.trans hL0)
  · apply L.ι_injective
    rw [map_mul, map_mul, ← ha, ← hb, ← mul_assoc, ← mul_assoc, hab']

end GlobalFromChart

/-! ## 3. Assembly: `Inputs k A` -/

section Assembly

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.Smooth k A]

/-- **WP-18**: `A` (smooth, integral, affine over `k`) supplies a value of
`Inputs k A`. Uses the finite étale cover of WP-17
(`Chart.exists_finite_etale_cover`); the cover is nonempty since `A` is a
nontrivial domain (`Ideal.span (Set.range f) = ⊤` with `f : Fin 0 → A` would
force `A` trivial), so chart `0` supplies the global domain and right-Ore
leaves via `noZeroDivisors_of_chart` / `rightOre_of_chart`. -/
theorem exists_inputs : Nonempty (Inputs k A) := by
  classical
  haveI hfinType : Algebra.FiniteType k A := inferInstance
  obtain ⟨s, f, hcover, hf⟩ := GlobalStafford.Chart.exists_finite_etale_cover k A
  have hs0 : s ≠ 0 := by
    intro hs0
    subst hs0
    have hempty : Set.range f = (∅ : Set A) := by
      rw [Set.range_eq_empty_iff]; infer_instance
    rw [hempty, Ideal.span_empty] at hcover
    have h1 : (1 : A) ∈ (⊥ : Ideal A) := hcover ▸ Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp h1)
  set i0 : Fin s := ⟨0, Nat.pos_of_ne_zero hs0⟩ with hi0def
  set Af : Fin s → Type u := fun i => Localization.Away (f i) with hAfdef
  set X : ∀ i, EtaleCoordinateChart k (Af i) := fun i => Classical.choice (hf i).2 with hXdef
  haveI instDomainAf : ∀ i, IsDomain (Af i) := fun i => by
    have hfi : f i ≠ 0 := (hf i).1
    have hmono : Submonoid.powers (f i) ≤ nonZeroDivisors A :=
      Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hfi)
    exact IsLocalization.isDomain_localization hmono
  haveI instNontrivialAf : ∀ i, Nontrivial (Af i) := fun i => (instDomainAf i).toNontrivial
  refine ⟨{
    s := s
    f := f
    cover := hcover
    Af := Af
    instCommRing := fun i => inferInstanceAs (CommRing (Localization.Away (f i)))
    instNontrivial := instNontrivialAf
    instAlgk := fun i => inferInstanceAs (Algebra k (Localization.Away (f i)))
    instAlgA := fun i => inferInstanceAs (Algebra A (Localization.Away (f i)))
    instTower := fun i => inferInstanceAs (IsScalarTower k A (Localization.Away (f i)))
    instLoc := fun i => inferInstanceAs (IsLocalization.Away (f i) (Localization.Away (f i)))
    loc := fun i => localizationInterfaceAway (k := k) (A := A) (f i) (hf i).1
    chartS38Poly := fun i => chartS38Poly (X i)
    chartDomain := fun i => chartDomain (X i)
    globalDomain := noZeroDivisors_of_chart (f i0) (hf i0).1 (chartDomain (X i0))
    rightOre := rightOre_of_chart (f i0) (hf i0).1 (chartRightOre (X i0)) }⟩

/-- The `Inputs k A` value assembled from a finite étale cover of `A` (WP-18). -/
noncomputable def inputs : Inputs k A := Classical.choice exists_inputs

end Assembly

/-! ## 4. The universal statement -/

/-- **WP-18 terminal declaration**: the Global Stafford theorem, quantified over
every characteristic-zero field `k` and every smooth integral affine
`k`-algebra `A`. -/
theorem universalStatement :
    ∀ (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
      [Algebra.Smooth k A], AlgebraicAnalysis.TwoGeneratorIdentity (algebra (k := k) (R := A)) :=
  fun _k _ _ _A _ _ _ _ => GlobalStafford.PhaseI.twoGeneratorIdentity_of_inputs inputs

/-- The Palomar-shaped Challenge statement. -/
theorem challengeStatement : GlobalStaffordChallenge.UniversalStatement.{u} :=
  GlobalStafford.Assembly.universalStatement_of_universal universalStatement

end GlobalStafford

#print axioms GlobalStafford.chartDomain
#print axioms GlobalStafford.chartS38Poly
#print axioms GlobalStafford.chartData
#print axioms GlobalStafford.chartRightOre
#print axioms GlobalStafford.noZeroDivisors_of_chart
#print axioms GlobalStafford.rightOre_of_chart
#print axioms GlobalStafford.exists_inputs
#print axioms GlobalStafford.inputs
#print axioms GlobalStafford.universalStatement
#print axioms GlobalStafford.challengeStatement
