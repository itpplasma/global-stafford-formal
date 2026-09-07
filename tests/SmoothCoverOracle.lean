import GlobalStafford.Chart.SmoothCover

/-!
# Oracle test for the finite étale cover (WP-17)

`PLAN.md` WP-17 acceptance test. A literal consumer of
`GlobalStafford.Chart.exists_finite_etale_cover`, instantiated at
`k = ℚ`, `A = MvPolynomial (Fin 2) ℚ`. `A` is a domain (a polynomial ring over a
field), `CharZero ℚ` holds, and `Algebra.Smooth ℚ A` holds because both
`Algebra.FormallySmooth ℚ A` (`instFormallySmoothMvPolynomial`) and
`Algebra.FinitePresentation ℚ A` (`FinitePresentation.mvPolynomial`) are already
registered instances for multivariate polynomial rings. This checks that
`exists_finite_etale_cover` specializes and elaborates at a concrete carrier,
independent of the internal proof.
-/

namespace GlobalStafford.SmoothCoverOracle

noncomputable abbrev A : Type := MvPolynomial (Fin 2) ℚ

instance : Algebra.Smooth ℚ A where

/-- Oracle: `exists_finite_etale_cover` (Theorem 6.3) instantiated at
`k = ℚ`, `A = ℚ[x₀, x₁]`. -/
theorem oracle :
    ∃ (s : ℕ) (f : Fin s → A), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i, f i ≠ 0 ∧
        Nonempty (GlobalStafford.Chart.EtaleCoordinateChart ℚ (Localization.Away (f i))) :=
  GlobalStafford.Chart.exists_finite_etale_cover ℚ A

end GlobalStafford.SmoothCoverOracle

#print axioms GlobalStafford.SmoothCoverOracle.oracle
