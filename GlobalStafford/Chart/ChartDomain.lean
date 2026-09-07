import GlobalStafford.Chart.ChartDomain.Monomials
import GlobalStafford.Chart.ChartDomain.NormalForm
import GlobalStafford.Chart.ChartDomain.Symbol

/-!
# The chart operator ring is a domain

`PLAN.md` §4, work package WP-14 (`Chart/ChartDomain.lean`). Assembly of the three parts of the
PBW/symbol argument for an integral affine `C` étale over `B = k[x_1,…,x_n]`:

* `Chart/ChartDomain/Monomials.lean` (steps 1–2): the iterated coordinate derivations
  `partialMonomial α = ∏ i, (∂_i)^{α i}` and their action on polynomial monomials;
* `Chart/ChartDomain/NormalForm.lean` (steps 3–4): left-`C`-linear independence
  (`linearIndependent_partialMonomial`) and `C`-spanning (`mem_span_partialMonomial`) of that
  family in `Module.End k C`, i.e. the normal form `P = ∑_α c_α ∂^α`;
* `Chart/ChartDomain/Symbol.lean` (steps 5–7): the realization map `opOf` from coefficient
  polynomials to operators, the weak composition rule
  `partialMonomial_commutator_mem` (`∂^α` passes a multiplication operator up to a normal form
  of strictly smaller total degree), the resulting product formula `opOf_mul_sub_mem`, and the
  multiplicativity of the leading symbol (`opOf_mul_ne_zero`).

The conclusion `noZeroDivisors_algebra_of_etale` is the `noZeroDivisors` field of
`EtaleChartData` (`Chart/EtaleChartData.lean`, consumed by `etaleChartData_of_fields` in
`Chart/EtaleDerivations.lean`).

The WP-13 output `hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) k) C)` is carried
as a hypothesis because `PLAN.md` supplies it here, but it is **not used**: linear independence
of `partialMonomial` only evaluates operators on images of polynomial monomials and needs the
injectivity of `algebraMap k C` (automatic for a field acting on a nontrivial ring), not that of
`algebraMap B C`. The `linter.unusedVariables` check is therefore switched off for the theorem.
-/

namespace GlobalStafford.Chart

open AlgebraicAnalysis AlgebraicAnalysis.DifferentialOperators

noncomputable section

universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {C : Type u} [CommRing C] [IsDomain C]
  [Algebra k C] [Algebra (B k n) C] [IsScalarTower k (B k n) C] [Algebra.FormallyEtale (B k n) C]

set_option linter.unusedVariables false in
/-- **WP-14**: the ring `D_k(C)` of finite-order differential operators on an integral affine
`C` étale over `k[x_1,…,x_n]` has no zero divisors. -/
theorem noZeroDivisors_algebra_of_etale
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) k) C)) :
    NoZeroDivisors (algebra (k := k) (R := C)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro P Q hPQ
    by_contra hcon
    push_neg at hcon
    obtain ⟨hP, hQ⟩ := hcon
    obtain ⟨f, hf⟩ := exists_opOf (k := k) (C := C) (n := n) (P : Module.End k C) P.2
    obtain ⟨g, hg⟩ := exists_opOf (k := k) (C := C) (n := n) (Q : Module.End k C) Q.2
    have hPz : (P : Module.End k C) ≠ 0 := fun h => hP (Subtype.ext h)
    have hQz : (Q : Module.End k C) ≠ 0 := fun h => hQ (Subtype.ext h)
    have hfz : f ≠ 0 := by
      intro h
      exact hPz (by rw [← hf, h, map_zero])
    have hgz : g ≠ 0 := by
      intro h
      exact hQz (by rw [← hg, h, map_zero])
    have hval : (P : Module.End k C) * (Q : Module.End k C) = 0 := by
      have := congrArg (fun R : algebra (k := k) (R := C) => (R : Module.End k C)) hPQ
      simpa using this
    rw [← hf, ← hg] at hval
    exact opOf_mul_ne_zero (k := k) (C := C) hfz hgz hval

end
end GlobalStafford.Chart

#print axioms GlobalStafford.Chart.noZeroDivisors_algebra_of_etale
