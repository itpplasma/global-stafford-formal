import GlobalStafford.Localization.Construction
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Oracle test for the localization interface construction (WP-11)

`PLAN.md` WP-11 acceptance test. A literal consumer of
`GlobalStafford.Localization.localizationInterfaceAway`, instantiated at
`k = ℚ`, `A = ℚ[X]`, `f = X`, `A_f = Localization.Away X`, with **no**
hypotheses: the interface is constructed, not assumed. The behavioural oracle
is a finite computation checked by `simp` on the concrete ring `ℚ[X]`: the
image of the derivation `d/dX` under `ι` sends `algebraMap X` to
`algebraMap (d/dX X) = 1`, and `ι` sends `multiplicationD X` to multiplication
by the image of `X`. Neither check restates the internal construction.
-/

namespace GlobalStafford.LocalizationConstructionOracle

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators GlobalStafford.Localization
open Polynomial

noncomputable abbrev Af := Localization.Away (Polynomial.X : Polynomial ℚ)

/-- `X ≠ 0` in `ℚ[X]`. -/
theorem hX : (Polynomial.X : Polynomial ℚ) ≠ 0 := Polynomial.X_ne_zero

/-- The interface for `ℚ[X] → ℚ[X]_X`, constructed (not assumed). -/
noncomputable abbrev L : LocalizationInterface (k := ℚ) (A := Polynomial ℚ) (Af := Af)
    Polynomial.X :=
  localizationInterface (k := ℚ) (A := Polynomial ℚ) (Af := Af) Polynomial.X hX

/-- The `Localization.Away` instance-level corollary agrees with it. -/
theorem oracle_away :
    localizationInterfaceAway (k := ℚ) (A := Polynomial ℚ) Polynomial.X hX = L := rfl

/-- `[d/dX, a] = multiplication (d/dX a)`, the Leibniz rule on `ℚ[X]`. -/
theorem commutator_derivative (a : Polynomial ℚ) :
    commutator (k := ℚ) (R := Polynomial ℚ) (Polynomial.derivative (R := ℚ)) a =
      multiplication (k := ℚ) (Polynomial.derivative (R := ℚ) a) := by
  refine LinearMap.ext fun x => ?_
  simp only [commutator_apply, multiplication_apply, Polynomial.derivative_mul]
  ring

/-- `d/dX` is a differential operator of order at most `1`. -/
theorem derivative_mem_order_one :
    (Polynomial.derivative (R := ℚ) : Module.End ℚ (Polynomial ℚ)) ∈
      order (k := ℚ) (R := Polynomial ℚ) 1 := by
  rw [mem_order_succ_iff]
  intro a
  rw [commutator_derivative a]
  exact (mem_order_zero_iff_eq_multiplication _).2
    (LinearMap.ext fun x => by simp [multiplication_apply])

/-- `d/dX` as an element of `D_ℚ(ℚ[X])`. -/
noncomputable def derivativeD : algebra (k := ℚ) (R := Polynomial ℚ) :=
  ⟨Polynomial.derivative (R := ℚ), (mem_algebra_iff _).2 ⟨1, derivative_mem_order_one⟩⟩

/-- **Oracle 1** (finite computation on `ℚ[X]`): `ι (d/dX)` sends the image of
`X` to `1`, because `d/dX X = 1`. -/
theorem oracle_derivative :
    ((L.ι derivativeD : algebra (k := ℚ) (R := Af)) : Module.End ℚ Af)
        (algebraMap (Polynomial ℚ) Af Polynomial.X) = 1 := by
  rw [localizationInterface_ι_algebraMap]
  show algebraMap (Polynomial ℚ) Af (Polynomial.derivative (R := ℚ) Polynomial.X) = 1
  simp

/-- **Oracle 2**: `ι (d/dX)` sends the image of `X ^ 2` to `2 * X`. -/
theorem oracle_derivative_sq :
    ((L.ι derivativeD : algebra (k := ℚ) (R := Af)) : Module.End ℚ Af)
        (algebraMap (Polynomial ℚ) Af (Polynomial.X ^ 2)) =
      algebraMap (Polynomial ℚ) Af (2 * Polynomial.X) := by
  rw [localizationInterface_ι_algebraMap]
  show algebraMap (Polynomial ℚ) Af (Polynomial.derivative (R := ℚ) (Polynomial.X ^ 2)) = _
  congr 1
  simp
  norm_num

/-- **Oracle 3**: `ι` sends multiplication by `X` to multiplication by the
image of `X`. -/
theorem oracle_multiplicationD :
    L.ι (multiplicationD (k := ℚ) (A := Polynomial ℚ) Polynomial.X) =
      multiplicationD (k := ℚ) (A := Af) (algebraMap (Polynomial ℚ) Af Polynomial.X) :=
  L.ι_multiplicationD Polynomial.X

/-- **Oracle 4**: `ι` does not increase order. -/
theorem oracle_order :
    ((L.ι derivativeD : algebra (k := ℚ) (R := Af)) : Module.End ℚ Af) ∈
      order (k := ℚ) (R := Af) 1 :=
  L.ι_mem_order 1 derivativeD derivative_mem_order_one

/-- **Oracle 5**: `ι` is injective, and every operator on `ℚ[X]_X` clears into
its image by a power of multiplication by `X`. -/
theorem oracle_injective_and_clearance :
    Function.Injective L.ι ∧
      ∀ Q : algebra (k := ℚ) (R := Af), ∃ (l : ℕ) (P : algebra (k := ℚ) (R := Polynomial ℚ)),
        multiplicationD (k := ℚ) (A := Af) (algebraMap (Polynomial ℚ) Af Polynomial.X) ^ l * Q =
          L.ι P :=
  ⟨L.ι_injective, L.clearance⟩

end GlobalStafford.LocalizationConstructionOracle

#print axioms GlobalStafford.LocalizationConstructionOracle.L
#print axioms GlobalStafford.LocalizationConstructionOracle.oracle_away
#print axioms GlobalStafford.LocalizationConstructionOracle.oracle_derivative
#print axioms GlobalStafford.LocalizationConstructionOracle.oracle_derivative_sq
#print axioms GlobalStafford.LocalizationConstructionOracle.oracle_multiplicationD
#print axioms GlobalStafford.LocalizationConstructionOracle.oracle_order
#print axioms GlobalStafford.LocalizationConstructionOracle.oracle_injective_and_clearance
