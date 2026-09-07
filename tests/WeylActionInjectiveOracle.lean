import GlobalStafford.Chart.WeylActionInjective

/-!
# Oracle test for injectivity of the Weyl action (WP-18a)

A literal consumer of `GlobalStafford.Chart.weylAction_injective`: specializes it at `k = ℚ`,
`n = 1`, `C = MvPolynomial (Fin 1) ℚ` over itself (`B ℚ 1 = MvPolynomial (Fin 1) ℚ` literally,
via the reflexive `Algebra.id` instance, with `Algebra.FormallyEtale R R` supplying the needed
formal-étaleness instance for the identity), taking the chart data `E` from
`GlobalStafford.Chart.etaleChartData_of_fields` (whose derivations are `liftDerivation` by
construction, so `hE` holds by `rfl`) with its remaining geometric hypotheses
(`finiteGenericFibre`, `algebraMap_ne_zero`, `noZeroDivisors`) taken as hypotheses rather than
constructed (their construction is Phase II, WP-13/WP-14). This checks that
`weylAction_injective` specializes to a genuine injectivity statement independent of the internal
proof.
-/

namespace GlobalStafford.WeylActionInjectiveOracle

open GlobalStafford.Chart AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators
open Stafford38.WeylIteratedEquivalence

/-- Independent oracle: specializing `weylAction_injective` (WP-18a) at `k = ℚ`, `n = 1`,
`C = MvPolynomial (Fin 1) ℚ` over itself, with the chart data built from
`etaleChartData_of_fields` and the remaining geometric hypotheses supplied abstractly, reproduces
injectivity of `weylAction E`. -/
theorem weylAction_injective_oracle
    (hfin : ∃ (m : ℕ) (c : Fin m → MvPolynomial (Fin 1) ℚ),
      ∀ x : MvPolynomial (Fin 1) ℚ, ∃ b : B ℚ 1, b ≠ 0 ∧
        ∃ t : Fin m → B ℚ 1, algebraMap (B ℚ 1) (MvPolynomial (Fin 1) ℚ) b * x =
          ∑ i, c i * algebraMap (B ℚ 1) (MvPolynomial (Fin 1) ℚ) (t i))
    (hne : ∀ b : B ℚ 1, b ≠ 0 → algebraMap (B ℚ 1) (MvPolynomial (Fin 1) ℚ) b ≠ 0)
    (hdom : NoZeroDivisors (algebra (k := ℚ) (R := MvPolynomial (Fin 1) ℚ)))
    (hinj : Function.Injective (algebraMap (B ℚ 1) (MvPolynomial (Fin 1) ℚ))) :
    Function.Injective
      (weylAction (k := ℚ) (n := 1) (C := MvPolynomial (Fin 1) ℚ)
        { «∂» := liftDerivation
          «∂_coord» := liftDerivation_coord
          «∂_comm» := liftDerivation_comm
          coordinateRigidity := coordinateRigidity
          finiteGenericFibre := hfin
          algebraMap_ne_zero := hne
          noZeroDivisors := hdom }) :=
  weylAction_injective _ (fun _ => rfl) hinj

end GlobalStafford.WeylActionInjectiveOracle

#print axioms GlobalStafford.WeylActionInjectiveOracle.weylAction_injective_oracle
