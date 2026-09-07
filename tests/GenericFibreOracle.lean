import GlobalStafford.Chart.GenericFibre

/-!
# Oracle test for `finiteGenericFibre_of_etale` (WP-13)

`PLAN.md` WP-13 acceptance test. A literal consumer of
`GlobalStafford.Chart.finiteGenericFibre_of_etale`: instantiates it at the concrete
self-étale chart `k := ℚ`, `n := 1`, `C := MvPolynomial (Fin 1) ℚ` (the polynomial
ring `B = k[x_0]` viewed as an étale `B`-algebra over itself, via the generic
`Algebra.Etale.self` instance). This checks that the abstract WP-13 theorem
specializes to a genuine instance without any further axioms, independent of the
internal proof of `finiteGenericFibre_of_etale` itself.
-/

namespace GlobalStafford.GenericFibreOracle

open GlobalStafford.Chart

/-- Instantiation of `finiteGenericFibre_of_etale` at the self-étale chart
`C = B = MvPolynomial (Fin 1) ℚ`. A literal consumer of the WP-13 theorem, not a
restatement of its proof. -/
theorem finiteGenericFibre_rat_self :
    ∃ (m : ℕ) (c : Fin m → MvPolynomial (Fin 1) ℚ),
      ∀ x : MvPolynomial (Fin 1) ℚ, ∃ b : MvPolynomial (Fin 1) ℚ, b ≠ 0 ∧
        ∃ t : Fin m → MvPolynomial (Fin 1) ℚ,
          algebraMap (MvPolynomial (Fin 1) ℚ) (MvPolynomial (Fin 1) ℚ) b * x =
            ∑ i, c i * algebraMap (MvPolynomial (Fin 1) ℚ) (MvPolynomial (Fin 1) ℚ) (t i) :=
  finiteGenericFibre_of_etale (k := ℚ) (n := 1) (C := MvPolynomial (Fin 1) ℚ)

/-- Instantiation of `algebraMap_injective_of_etale` at the same self-étale chart. -/
theorem algebraMap_injective_rat_self :
    Function.Injective
      (algebraMap (MvPolynomial (Fin 1) ℚ) (MvPolynomial (Fin 1) ℚ)) :=
  algebraMap_injective_of_etale (k := ℚ) (n := 1) (C := MvPolynomial (Fin 1) ℚ)

#print axioms finiteGenericFibre_rat_self
#print axioms algebraMap_injective_rat_self

end GlobalStafford.GenericFibreOracle
