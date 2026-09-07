import GlobalStafford.Weyl.OreDomain

/-!
# Oracle test for the Weyl-algebra right Ore condition (WP-15)

`PLAN.md` WP-15 acceptance test. A literal consumer of
`GlobalStafford.Weyl.weyl_rightOre` and the induced
`OreLocalization.OreSet` instance, instantiated at the first rank-`1` Weyl
algebra over `ℚ` (`A_1(ℚ)`), independent of the general proof: it only
uses the public statement, not its internal tower-induction construction.
-/

namespace GlobalStafford.WeylOreDomainOracle

open GlobalStafford.Weyl
open scoped nonZeroDivisors

/-- The right Ore condition, restated concretely for `A_1(ℚ)`. -/
theorem rightOre_A1Q :
    ∀ x y : Stafford38.WeylIteratedEquivalence.PresentedWeyl ℚ 1,
      x ≠ 0 → y ≠ 0 →
        ∃ a b : Stafford38.WeylIteratedEquivalence.PresentedWeyl ℚ 1,
          a ≠ 0 ∧ x * a = y * b :=
  weyl_rightOre ℚ 1

/-- The induced `OreSet` instance is available at `A_1(ℚ)`, so the full Ore
localization of the opposite ring is well defined there. -/
noncomputable example :
    OreLocalization.OreSet
      ((Stafford38.WeylIteratedEquivalence.PresentedWeyl ℚ 1)ᵐᵒᵖ)⁰ :=
  inferInstance

#print axioms rightOre_A1Q

end GlobalStafford.WeylOreDomainOracle
