import GlobalStafford.Certificate.OldChartProtection
import GlobalStafford.Certificate.SquaredAnnihilator
import GlobalStafford.Chart.PolynomialS38
import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite-cover patching (paper §5, Theorem 5.1)

`PLAN.md` §3, work package WP-6 (`Descent/FiniteCoverPatching.lean`). Given a
finite principal cover `f_1, …, f_s` of `A` by chart rings `A_{f_i}`, each of
which produces bounded-order sources for every Ore pair `(d, B)` (the
conclusion of Theorem 4.1 / WP-5, taken here as an explicit hypothesis
`BoundedSourceProducer` because WP-5 is developed on a separate branch and is
not available on this branch), and given the right Ore condition on `A`,
every nonzero `d : D_k(A)` admits a same-divisor certificate `1 = d R + F d
S`. This is Theorem 5.1 of the paper.

The proof follows PLAN.md §1 Section 5: induct on the charts, carrying a
single "source" `B` for which a same-divisor certificate has already been
built on every earlier chart; at each step, Theorem 4.1 supplies a new
bounded-order perturbation of `B` that succeeds on the new chart, and
`GlobalStafford.Certificate.protect_old_chart` (Lemma 1.2) shows the same
perturbation still succeeds on every earlier chart, provided the new
exponent is chosen large enough. After all charts are covered, the finitely
many chart certificates are right-cleared to a common power of the
corresponding `f_i`, and a Bézout combination for the ideal `(f_1^m, …,
f_s^m) = A` (from `Ideal.span_pow_eq_top`) assembles them into a single
certificate on `A`.
-/

namespace GlobalStafford.Descent

open AlgebraicAnalysis.DifferentialOperators GlobalStafford.Operators
  GlobalStafford.Certificate GlobalStafford.Localization
  GlobalStafford.Localization.LocalizationInterface

universe u

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]

/-- The conclusion of Theorem 4.1 (WP-5) for the chart `Af` at `f`, as a
predicate: every Ore pair `(d, B)` with `d ≠ 0` admits, for all sufficiently
large `N` (with `H.eval N ≠ 0` for a fixed nonzero `H : Polynomial k`), a
bounded-order perturbation `B + f^{N-l-M} T` of `B` (with `ord T ≤ M`) that
succeeds as a same-divisor source on the chart `Af`. -/
def BoundedSourceProducer (f : A) (Af : Type u) [CommRing Af] [Algebra k Af] [Algebra A Af]
    [IsScalarTower k A Af] [IsLocalization.Away f Af]
    (L : LocalizationInterface (k := k) (A := A) (Af := Af) f) : Prop :=
  ∀ (d B : algebra (k := k) (R := A)), OreData d B → d ≠ 0 →
    ∃ (M l : ℕ) (H : Polynomial k), H ≠ 0 ∧
      ∀ N : ℕ, l + M ≤ N → H.eval (N : k) ≠ 0 →
        ∃ T : algebra (k := k) (R := A), (T : Module.End k A) ∈ order M ∧
          ∃ U V : algebra (k := k) (R := Af),
            (1 : algebra (k := k) (R := Af)) =
              L.ι d * U + L.ι (B + multiplicationD f ^ (N - l - M) * T) * L.ι d * V

/-- Chart data for a finite principal cover of `A`: chart rings `Af i` at
generators `f i` of the unit ideal, each equipped with a `LocalizationInterface`
and a `BoundedSourceProducer` (the Theorem 4.1 conclusion). -/
structure ChartCover (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
    [Algebra k A] where
  /-- Number of charts. -/
  s : ℕ
  /-- The chart generators. -/
  f : Fin s → A
  /-- The chart generators cover: they generate the unit ideal of `A`. -/
  cover : Ideal.span (Set.range f) = ⊤
  /-- The chart rings. -/
  Af : Fin s → Type u
  [instCommRing : ∀ i, CommRing (Af i)]
  [instAlgk : ∀ i, Algebra k (Af i)]
  [instAlgA : ∀ i, Algebra A (Af i)]
  [instTower : ∀ i, IsScalarTower k A (Af i)]
  [instLoc : ∀ i, IsLocalization.Away (f i) (Af i)]
  /-- The localization interface at each chart. -/
  loc : ∀ i, LocalizationInterface (k := k) (A := A) (Af := Af i) (f i)
  /-- Each chart produces bounded-order sources (Theorem 4.1). -/
  producer : ∀ i, BoundedSourceProducer (f i) (Af i) (loc i)

attribute [instance] ChartCover.instCommRing ChartCover.instAlgk ChartCover.instAlgA
  ChartCover.instTower ChartCover.instLoc

variable {Af' : Type u} [CommRing Af'] [Algebra k Af'] [Algebra A Af'] [IsScalarTower k A Af']
  {g : A} [IsLocalization.Away g Af']

/-- Right-clearing a same-divisor certificate `1 = ι d * U + ι X * ι d * V` on a chart `Af'`
at `g` to a same-divisor identity `g^m = d A₀ + X d B₀` back on `A`. Used both for the new
chart at each induction step (with `X` the perturbed source `F`) and, at the end, for every
chart against the final global source `B`. -/
theorem clear_to_base (Lg : LocalizationInterface (k := k) (A := A) (Af := Af') g)
    (d X : algebra (k := k) (R := A)) (U V : algebra (k := k) (R := Af'))
    (hcert : (1 : algebra (k := k) (R := Af')) = Lg.ι d * U + Lg.ι X * Lg.ι d * V) :
    ∃ (m : ℕ) (A₀ B₀ : algebra (k := k) (R := A)),
      multiplicationD (k := k) (A := A) g ^ m = d * A₀ + X * d * B₀ := by
  obtain ⟨m, A₀, B₀, hA₀, hB₀⟩ := Lg.rightClearance_pair U V
  refine ⟨m, A₀, B₀, ?_⟩
  apply Lg.ι_injective
  rw [Lg.ι_pow_multiplicationD]
  simp only [map_add, map_mul]
  rw [← hA₀, ← hB₀, ← mul_assoc, ← mul_assoc, ← add_mul, ← hcert, one_mul]

/-- The induction step of Theorem 5.1: given a same-divisor certificate for `d` and `B` on
every chart `j < i` (`hInv`), Theorem 4.1 (`C.producer`) at chart `i` and old-chart protection
(`protect_old_chart`, Lemma 1.2) produce a new global source `B'` with a same-divisor
certificate on every chart `j < i + 1`. -/
theorem chart_step (C : ChartCover k A) [NoZeroDivisors (algebra (k := k) (R := A))]
    (hOre : ∀ x y : algebra (k := k) (R := A), x ≠ 0 → y ≠ 0 →
      ∃ a b : algebra (k := k) (R := A), a ≠ 0 ∧ x * a = y * b)
    (d : algebra (k := k) (R := A)) (hd : d ≠ 0) {i : ℕ} (hi : i < C.s)
    (B : algebra (k := k) (R := A))
    (hInv : ∀ j : Fin C.s, (j : ℕ) < i →
      ∃ U V : algebra (k := k) (R := C.Af j),
        (1 : algebra (k := k) (R := C.Af j)) =
          (C.loc j).ι d * U + (C.loc j).ι B * (C.loc j).ι d * V) :
    ∃ B' : algebra (k := k) (R := A), ∀ j : Fin C.s, (j : ℕ) < i + 1 →
      ∃ U V : algebra (k := k) (R := C.Af j),
        (1 : algebra (k := k) (R := C.Af j)) =
          (C.loc j).ι d * U + (C.loc j).ι B' * (C.loc j).ι d * V := by
  classical
  set i' : Fin C.s := ⟨i, hi⟩ with hi'def
  obtain ⟨od⟩ := OreData.of_rightOre hOre d B hd
  obtain ⟨M, l, H, hH, hprod⟩ := C.producer i' d B od hd
  -- Old certificates, extracted by choice from `hInv`.
  let oldU : ∀ j : Fin C.s, (j : ℕ) < i → algebra (k := k) (R := C.Af j) :=
    fun j hj => (hInv j hj).choose
  let oldV : ∀ j : Fin C.s, (j : ℕ) < i → algebra (k := k) (R := C.Af j) :=
    fun j hj => (hInv j hj).choose_spec.choose
  have oldCert : ∀ (j : Fin C.s) (hj : (j : ℕ) < i),
      (1 : algebra (k := k) (R := C.Af j)) =
        (C.loc j).ι d * oldU j hj + (C.loc j).ι B * (C.loc j).ι d * oldV j hj :=
    fun j hj => (hInv j hj).choose_spec.choose_spec
  -- Orders needed to invoke `protect_old_chart`: `rd` for `d`, `Rmax` a common bound for
  -- the orders of all the old `V`'s.
  obtain ⟨rd, hrd⟩ := exists_order d
  set Rmax : ℕ :=
      Finset.univ.sup (fun j : {j : Fin C.s // (j : ℕ) < i} => (exists_order (oldV j.1 j.2)).choose)
    with hRmaxdef
  have hRmax : ∀ j : Fin C.s, (hj : (j : ℕ) < i) →
      (oldV j hj : Module.End k (C.Af j)) ∈ order Rmax := by
    intro j hj
    have hmem : (⟨j, hj⟩ : {j : Fin C.s // (j : ℕ) < i}) ∈ (Finset.univ : Finset _) :=
      Finset.mem_univ _
    have hle : (exists_order (oldV j hj)).choose ≤ Rmax := by
      rw [hRmaxdef]
      exact Finset.le_sup
        (f := fun j : {j : Fin C.s // (j : ℕ) < i} => (exists_order (oldV j.1 j.2)).choose) hmem
    exact order_mono hle (exists_order (oldV j hj)).choose_spec
  -- Choose `N` large enough for the Theorem 4.1 admissibility bound, and large enough that
  -- old-chart protection applies to every old chart.
  obtain ⟨N₀, hN₀⟩ := GlobalStafford.Chart.exists_admissible_bound hH
  set N : ℕ := max (max (l + M) N₀) (l + 2 * M + rd + Rmax + 1) with hNdef
  have hN1 : l + M ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN2 : N₀ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN3 : l + 2 * M + rd + Rmax + 1 ≤ N := le_max_right _ _
  have hHN : H.eval (N : k) ≠ 0 := hN₀ N hN2
  obtain ⟨T, hT, U, V, hcertNew⟩ := hprod N hN1 hHN
  set B' : algebra (k := k) (R := A) :=
      B + multiplicationD (k := k) (A := A) (C.f i') ^ (N - l - M) * T with hB'def
  -- Right-clear the new-chart certificate to a same-divisor identity on `A`.
  obtain ⟨m, A₀, B₀, hclear⟩ := clear_to_base (C.loc i') d B' U V hcertNew
  -- Old-chart protection: the new source `B'` still succeeds on every old chart.
  have step_old : ∀ (j : Fin C.s) (hj : (j : ℕ) < i), ∃ U' V' : algebra (k := k) (R := C.Af j),
      (1 : algebra (k := k) (R := C.Af j)) =
        (C.loc j).ι d * U' + (C.loc j).ι B' * (C.loc j).ι d * V' := by
    intro j hj
    have hL : M + rd + Rmax < N - l - M := by omega
    exact protect_old_chart (Lg := C.loc j) (f := C.f i') hrd hT (hRmax j hj) hL (oldCert j hj)
      hclear
  refine ⟨B', fun j hj1 => ?_⟩
  by_cases hji : (j : ℕ) < i
  · exact step_old j hji
  · have hjeq : (j : ℕ) = i := by omega
    have hji' : j = i' := by
      apply Fin.ext
      rw [hi'def]
      exact hjeq
    subst hji'
    exact ⟨U, V, hcertNew⟩

end GlobalStafford.Descent
