import GlobalStafford.Chart.EtaleDerivations

/-!
# Oracle test for étale derivations and coordinate rigidity (WP-12)

`PLAN.md` WP-12 acceptance test. A literal consumer of
`GlobalStafford.Chart.liftDerivation` and `GlobalStafford.Chart.liftDerivation_coord`:
instantiates `liftDerivation` at `k = ℚ`, `n = 1`, `C = MvPolynomial (Fin 1) ℚ` over
itself (the reflexive `Algebra.id` instance, with `Algebra.FormallyEtale B B` coming
from the standard Mathlib instance `Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth`
applied to any ring over itself), and checks the independently-computable fact
`liftDerivation 0 (xC 0) = 1` by `simp` on `liftDerivation_coord`, without unfolding
the internal Kähler-differential construction of `liftDerivation` itself.
-/

namespace GlobalStafford.EtaleDerivationsOracle

open GlobalStafford.Chart

noncomputable abbrev C := MvPolynomial (Fin 1) ℚ

/-- Independent oracle: `liftDerivation 0` is dual to the coordinate `x_0`, at the
concrete carrier `C = MvPolynomial (Fin 1) ℚ` over itself. -/
theorem liftDerivation_coord_oracle :
    liftDerivation (k := ℚ) (n := 1) (C := C) 0 (xC ℚ 1 C 0) = 1 := by
  simp [liftDerivation_coord]

end GlobalStafford.EtaleDerivationsOracle

#print axioms GlobalStafford.EtaleDerivationsOracle.liftDerivation_coord_oracle
