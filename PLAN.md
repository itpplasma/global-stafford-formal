# Global Stafford formalization plan

```yaml
phase: phase-i
phase_i_status: in-progress (WP-1, WP-2 core, WP-4 generic, AA-1 done)
phase_ii_status: not-started
phase_iii_status: not-started
paper_source: itpplasma/global-stafford notes/source-changing-descent-2026-09-07.md
paper_review: two independent-context model reviews passed 2026-09-07; human review open
lean_toolchain: leanprover/lean4:v4.33.0
mathlib: db584cd6d46c92f209a44c0f1c829460d327499d
algebraic_analysis: faa64814d5a310dc925e330af58e000f129f1098
stafford38_formal: 784b59925beb9a480519142336bd6434f6eeef16
challenge_declaration: GlobalStaffordChallenge.universalStatement
palomar_registration: not-submitted
open_holes: []
```

This file is the live plan and status of the Lean formalization of the
Global Stafford theorem. It is written so that an agent with no prior
context can implement every step. Read `AGENTS.md` first. The paper proof
lives in the private research repository and is summarized in Section 1;
everything needed to write the Lean code is in this file.

Status vocabulary for the work-package tables: `todo`, `wip` (has a
`sorry` registered in `open_holes`), `done` (builds, no `sorry`,
`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`
or the declared conditional hypotheses), `blocked` (reason recorded).

## 0. Target theorem

Let `k` be a field of characteristic zero, `A` a smooth integral finitely
generated `k`-algebra, and `D_k(A)` the ring of `k`-linear finite-order
differential operators on `A` (Grothendieck's definition, composition as
product). The theorem is

```text
for every nonzero d in D_k(A) there exist F, R, S in D_k(A) with 1 = dR + FdS.
```

Both products are ordered; `d` is the first factor of the first product and
the middle factor of the second. Nothing may be commuted past `d`.

Lean carriers:

| Object | Lean |
| --- | --- |
| `D_k(A)` | `AlgebraicAnalysis.DifferentialOperators.algebra (k := k) (R := A)`, a `Subalgebra k (Module.End k A)`; write `𝒟 k A` for it in comments, `algebra k A` in code after `open AlgebraicAnalysis.DifferentialOperators` |
| order filtration | `AlgebraicAnalysis.DifferentialOperators.order n : Submodule k (Module.End k A)` |
| multiplication by `a` | `multiplication a := LinearMap.mulLeft k a`; inside the subalgebra use `multiplicationD a : algebra k A` (define once in `GlobalStafford/Operators/Basic.lean`, copying `Stafford38.LocalizedDifferentialCorollaries.multiplicationD`) |
| commutator `[P,a]` | `commutator P a = P * multiplication a - multiplication a * P` |
| S38 property of a ring | `AlgebraicAnalysis.TwoGeneratorIdentity R : ∀ d, d ≠ 0 → ∃ F r s, 1 = d * r + F * d * s` |
| Weyl algebra | `Stafford38.WeylIteratedEquivalence.PresentedWeyl k n` (= `Stafford.FreeWeyl k (Fin n ⊕ Fin n) (Matrix.J (Fin n) k)`) |
| Weyl S38 (imported, axiom-clean) | `Stafford38.universalStatement : ∀ (k : Type u) [Field k] [CharZero k] (n) (d : WeylAlg k n), d ≠ 0 → ∃ F R S, 1 = d * R + F * d * S` |
| Palomar statement | `Challenge.lean`, `GlobalStaffordChallenge.UniversalStatement`, differential operators defined by the same recursion without a subalgebra |

Final deliverable (Phase III): `GlobalStafford.universalStatement`
proving `∀ (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A]
[IsDomain A] [Algebra k A] [Algebra.Smooth k A], TwoGeneratorIdentity
(algebra k A)` with only the three standard axioms, and `Solution.lean`
transporting it to `GlobalStaffordChallenge.universalStatement`.

## 1. The paper proof in the form that is formalized

The formal development follows Remark 4.2 of the paper (right-moved
conjugation), which needs no inverse automorphism. Notation: `R = D_k(A)`,
`R_f = D_k(A_f)` for `f ≠ 0` in `A`, `ι_f : R → R_f` the extension of
operators to the localization, `f` also denotes the multiplication operator.
`ad_f(P) = [P, f] = P f - f P`. For `P` of order `≤ r`, `ad_f^{r+1}(P) = 0`
and `ad_f^j(P)` has order `≤ r - j`.

**(1.1) Binomial formulas.** For every `n ≥ 0`:

```text
P f^n = Σ_{j=0}^{n} C(n,j) f^{n-j} ad_f^j(P)              (left form)
f^n P = Σ_{j=0}^{n} C(n,j) (-1)^j ad_f^j(P) f^{n-j}        (right form)
```

Both by induction on `n` from `Q f = f Q + ad_f(Q)`.
Consequence (1.2): if `ord P ≤ r ≤ n` then `P f^n = f^{n-r} Q` with
`Q = Σ_{j≤r} C(n,j) f^{r-j} ad_f^j(P)` of order `≤ r`.

**Lemma 1.1 (contractive powers).** If `E = f^L P`, `ord P ≤ r`, `L > r`,
then for all `j ≥ 1`, `E^j = f^{jL-(j-1)r} Q_j` with `ord Q_j ≤ jr`.
Induction: `E^{j+1} = f^L P f^a Q_j`, `a = jL-(j-1)r ≥ r`, apply (1.2).

**Lemma 1.2 (old-chart protection).** Chart rings `R_g` and `R_f`. Suppose
`1 = d U_g + B d V_g` in `R_g`, `F = B + f^L T` in `R` with `ord T ≤ M`,
`L > M + ord d + ord V_g`, and `f^m = d A_0 + F d B_0` in `R` (obtained by
right-clearing an `R_f`-certificate of `F`). Put `P = T d V_g`,
`E = f^L P`, `r = M + ord d + ord V_g`; then `d U_g + F d V_g = 1 + E`.
Choose `j` with `jL - (j-1)r ≥ m`; then `(-E)^j = f^m W`, `W ∈ R_g`.
With `Z = Σ_{i<j} (-E)^i`, `(1+E)Z = 1 - (-E)^j`, so

```text
1 = d (U_g Z + A_0 W) + F d (V_g Z + B_0 W)    in R_g.
```

**Section 3 (squared annihilator).** In any ring, if `c = d a`,
`B d c = d b_0`, `e = c h d`, and `1 = e^2 U + W e^2 V`, then with
`F = B + W c h`, `α = a h d`, `β = b_0 h d`:

```text
1 = d (α e U - β V) + F d (e V).
```

(Check: `dα = e`, `dβ = Bde = B d c h d`, `Fd = Bd + We`.) The pair
`(c, b_0)` comes from the right Ore condition applied to `B d d` and `d`:
`(B d d) a = d b_0` with `a ≠ 0`, `c := d a ≠ 0`.

**Section 4 (bounded-order sources, right-moved form).** Fix `f ≠ 0`,
`d ≠ 0`, `B`, and Ore data `c, a, b_0`. Let `ρ_t(P) = Σ_j C(t,j)(-1)^j
ad_f^j(P) f^{-j}` (polynomial in a central variable `t`, coefficients in
`R_f`); by the right form of (1.1), `ρ_N(P) = f^N P f^{-N}` for `N ∈ ℕ`.
Put `e_N = c f^N d` and

```text
E'(t) = c ρ_t(d c) ρ_{2t}(d),        e_N^2 = E'(N) f^{2N},   E'(0) = (cd)^2 ≠ 0.
```

Hypothesis `S38_poly(R_f)`: for every nonzero `E ∈ R_f[t]` there are
`h ∈ k[t] \ 0` and `u', w', v' ∈ R_f[t]` with `h = E u' + w' E v'` in
`R_f[t]`. Apply it to `E'`. For `N` with `h(N) ≠ 0`, evaluation at `t = N`
(a ring homomorphism, `t` central) gives `1 = e_N^2 U + W e_N^2 V` with
`U = f^{-2N} u'(N)/h(N)`, `W = w'(N)/h(N)`, `V = f^{-2N} v'(N)`. Section 3
with `h = f^N` yields the locally successful source `F' = B + W c f^N`.
Left-clear the finitely many coefficients of `w'(t) c`: `w'_i c = f^{-l_i}
ι(P_i)`; set `l = max l_i`, `P(t) = Σ_i f^{l-l_i} P_i t^i ∈ R[t]`,
`M = max ord(P_i)`. For `N ≥ l + M` and `h(N) ≠ 0`, (1.2) gives

```text
F' = ι(F_N),   F_N = B + f^{N-l-M} T_N,
T_N = h(N)^{-1} Σ_{j≤M} C(N,j) f^{M-j} ad_f^j(P(N)),   ord T_N ≤ M.
```

`M, l, h` are fixed before `N`. This is Theorem 4.1.

**Section 5 (finite-cover patching).** `f_1, …, f_s` generate the unit
ideal of `A`; each `R_{f_i}` satisfies `S38_poly`; `R` is a domain with the
right Ore condition. Induct on `i`, carrying a global `B` with certificates
on charts `j < i`. At step `i`, Theorem 4.1 gives `M, l, h`; choose `N`
with `N ≥ l+M`, `h(N) ≠ 0`, and `N-l-M > M + ord d + max_{j<i} ord V_j`;
Lemma 1.2 protects every old chart, and the new chart holds by
construction. At the end right-clear each chart certificate to
`f_i^{m} = d A_i + F d B_i` (common `m`), pick `a_i ∈ A` with
`Σ f_i^m a_i = 1`, and sum after right multiplication by `a_i`.

**Section 6 (chart input).** For an integral affine `C` étale over
`B = k[x_1..x_n]`: the `∂_i` lift uniquely to commuting derivations of `C`
with `∂_i(x_j) = δ_ij`; the Weyl algebra `T = A_n(k)` acts on `C`;
`S = D_k(C)` is spanned as a right `T`-module, up to a nonzero denominator
in `T`, by finitely many multiplication operators (coordinate generation
plus finiteness of the generic fibre `C ⊗_B Frac(B)`); `S` is a domain.
Lemma 6.1 (finite-rank ascent): for such `S ⊇ T`, every nonzero `d ∈ S`
has `d y = a` with `0 ≠ a ∈ T`, hence `S38(T) ⇒ S38(S)`. The same holds
over `K = k(t)` for `C_K = K ⊗_k C`, and a scalar-extension map
`D_k(C)[t] → D_K(C_K)` (injective, image spanning up to scalar
denominators) turns `S38(D_K(C_K))` into `S38_poly(D_k(C))`.
Theorem 6.3: a smooth `A` has a finite principal cover by such charts.

## 2. Repository layout

```text
GlobalStafford.lean                 root import file
GlobalStafford/
  Operators/Basic.lean              multiplicationD, coercion lemmas          (WP-1)
  Operators/Commutator.lean         (1.1), (1.2), ad-power order lemmas       (WP-1)
  Operators/ContractivePowers.lean  Lemma 1.1                                  (WP-1)
  Certificate/SquaredAnnihilator.lean  Section 3, OreData                     (WP-2)
  Localization/Interface.lean       LocalizationInterface leaf + right clearing (WP-2)
  Certificate/OldChartProtection.lean  Lemma 1.2                              (WP-3)
  Conjugation/PolynomialEvaluation.lean  evalNat, scalarPoly, binomPoly, ρ, E' (WP-4)
  Chart/PolynomialS38.lean          S38Poly, admissible integers                (WP-4)
  Descent/BoundedOrderSource.lean   Theorem 4.1                                 (WP-5)
  Descent/FiniteCoverPatching.lean  Theorem 5.1                                 (WP-6)
  Chart/FiniteRankAscent.lean       Lemma 6.1 generic (FiniteRightSpan)         (WP-7)
  Chart/EtaleChartData.lean         chart leaf structure, Weyl action, S38 of chart (WP-8)
  Chart/ScalarExtension.lean        ScalarExtensionInterface, S38Poly from base change (WP-9)
  Assembly/Inputs.lean              Inputs structure                            (WP-10)
  Assembly/PhaseI.lean              twoGeneratorIdentity_of_inputs               (WP-10)
  -- Phase II
  Localization/Construction.lean    build LocalizationInterface                 (WP-11)
  Chart/EtaleDerivations.lean       lifts, commutation, coordinate rigidity      (WP-12)
  Chart/GenericFibre.lean           finite generic fibre from étale over field   (WP-13)
  Chart/ChartDomain.lean            PBW freeness and no zero divisors            (WP-14)
  Weyl/OreDomain.lean               Weyl algebra domain and right Ore            (WP-15)
  Chart/ScalarExtensionConstruction.lean  base change to RatFunc k              (WP-16)
  Chart/SmoothCover.lean            smooth ⇒ finite étale principal cover        (WP-17)
  Assembly/Closure.lean             inputs, universalStatement, #print axioms    (WP-18)
Challenge.lean                      Palomar statement (Mathlib only, one sorry)
Solution.lean                       transport (Phase III, WP-19)
GlobalStaffordTest/                 literal independent consumers (WP-19)
tests/                              consumers and finite oracles
scripts/                            verify.sh, check-*.sh, Palomar tools
docs/                               correspondence, proof graph, verification, runbook
```

Every file starts with a module docstring stating the paper reference
(section, lemma number) and lists `#print axioms` for each public theorem
at the end. Use `namespace GlobalStafford.<Area>`.

## 3. Phase I: project-owned steps over concrete carriers

Phase I proves every project-owned step as a Lean theorem over the actual
carriers, with the literature inputs isolated as explicit `structure`
hypotheses (no `axiom` declarations anywhere). The terminal Phase I
declaration is `GlobalStafford.PhaseI.twoGeneratorIdentity_of_inputs :
Inputs k A → TwoGeneratorIdentity (algebra k A)`.

### WP-1 Operators (Basic, Commutator, ContractivePowers)

Variables: `{k A : Type*} [CommRing k] [CommRing A] [Algebra k A]`, and
where orders are involved nothing more. Open
`AlgebraicAnalysis.DifferentialOperators`.

`Operators/Basic.lean`:

```lean
def multiplicationD (a : A) : algebra (k := k) (R := A)     -- ⟨multiplication a, 0, _⟩
@[simp] theorem coe_multiplicationD (a) : (multiplicationD a : Module.End k A) = multiplication a
theorem multiplicationD_mul (a b) : multiplicationD a * multiplicationD b = multiplicationD (a * b)
theorem multiplicationD_one : multiplicationD (1 : A) = 1
theorem multiplicationD_pow (a) (n) : multiplicationD a ^ n = multiplicationD (a ^ n)
theorem multiplicationD_isUnit {a} (h : IsUnit a) : IsUnit (multiplicationD a)
def orderD (P : algebra k A) : Prop-level: use `(P : Module.End k A) ∈ order r` directly; add
theorem exists_order (P : algebra k A) : ∃ r, (P : Module.End k A) ∈ order r   -- P.property
theorem mul_mem_orderD {P Q} {m n} : ↑P ∈ order m → ↑Q ∈ order n → ↑(P * Q) ∈ order (m + n)
theorem multiplicationD_mem_order_zero (a) : ↑(multiplicationD a) ∈ order 0
theorem smul_mem_order (c : k) : ↑P ∈ order r → ↑(c • P) ∈ order r
theorem sum_mem_order : (∀ i ∈ s, ↑(P i) ∈ order r) → ↑(∑ i ∈ s, P i) ∈ order r
```

`Operators/Commutator.lean` (paper (1.1), (1.2)); define
`ad (f : A) (P : Module.End k A) : Module.End k A := commutator P f` and
its iterate `(ad f)^[j]`:

```lean
theorem ad_apply_mul (f) (P Q) : ad f (P * Q) = ad f P * Q + P * ad f Q           -- from commutator_mul
theorem mul_multiplication (f) (P) : P * multiplication f = multiplication f * P + ad f P
theorem ad_mem_order {f P r} : P ∈ order (r + 1) → ad f P ∈ order r                -- mem_order_succ_iff
theorem ad_iterate_mem_order {f P r j} (h : P ∈ order r) (hj : j ≤ r) : (ad f)^[j] P ∈ order (r - j)
theorem ad_iterate_eq_zero {f P r} (h : P ∈ order r) : (ad f)^[r + 1] P = 0
theorem ad_iterate_eq_zero_of_lt {f P r j} (h : P ∈ order r) (hj : r < j) : (ad f)^[j] P = 0
theorem ad_multiplication (f a) : ad f (multiplication a) = 0
theorem ad_iterate_algebraMem (f) (P) (hP : P ∈ algebra) (j) : (ad f)^[j] P ∈ algebra
/-- (1.1), left form. -/
theorem mul_multiplication_pow (f) (P) (n : ℕ) :
    P * multiplication f ^ n =
      ∑ j ∈ Finset.range (n + 1), (n.choose j) • (multiplication f ^ (n - j) * (ad f)^[j] P)
/-- (1.1), right form. -/
theorem multiplication_pow_mul (f) (P) (n : ℕ) :
    multiplication f ^ n * P =
      ∑ j ∈ Finset.range (n + 1), (n.choose j) • ((-1 : ℤ) ^ j • ((ad f)^[j] P * multiplication f ^ (n - j)))
/-- (1.2). -/
theorem exists_mul_multiplication_pow_eq {f P r n} (hP : P ∈ order r) (hn : r ≤ n) :
    ∃ Q ∈ order r, P * multiplication f ^ n = multiplication f ^ (n - r) * Q
theorem mul_multiplication_pow_truncate {f P r n} (hP : P ∈ order r) :   -- terms j > r vanish
    P * multiplication f ^ n = ∑ j ∈ Finset.range (r + 1), (n.choose j) • (multiplication f ^ (n - j) * (ad f)^[j] P)
```

Proof of (1.1): induction on `n`; `P f^{n+1} = (P f^n) f`; distribute;
`(ad f)^[j] P * f = f * (ad f)^[j] P + (ad f)^[j+1] P`; reindex with
`Finset.sum_range_succ`, `Finset.sum_range_succ'`, `Nat.choose_succ_succ`.
Use `nsmul` (`•` with `ℕ`) to avoid casts; `zsmul` only for the sign. For
the truncated form use `ad_iterate_eq_zero_of_lt` and
`Finset.sum_subset`. Mirror the same for the right form. All of these are
statements in `Module.End k A`; provide `algebra`-level corollaries by
`Subtype.ext` where WP-5 needs them (the products of subalgebra elements
coerce to products of endomorphisms: `Subalgebra.coe_mul`, `coe_pow`,
`coe_sum`).

`Operators/ContractivePowers.lean` (Lemma 1.1):

```lean
theorem pow_eq_multiplication_pow_mul {f P r L} (hP : P ∈ order r) (hL : r < L) :
    ∀ j, 1 ≤ j → ∃ Q ∈ order (j * r),
      (multiplication f ^ L * P) ^ j = multiplication f ^ (j * L - (j - 1) * r) * Q
theorem exists_threshold {r L m : ℕ} (hL : r < L) : ∃ j, 1 ≤ j ∧ m ≤ j * L - (j - 1) * r
```

Induction on `j`; the step uses `exists_mul_multiplication_pow_eq` with
`n = j*L - (j-1)*r ≥ r` (prove `r ≤ j*L-(j-1)*r` from `r < L` with
`omega` after unfolding `j*L-(j-1)*r = r + j*(L-r)`); orders add by
`mul_mem_order`. For `exists_threshold` take `j = m + 1`.

Acceptance: `lake build GlobalStafford.Operators.ContractivePowers`,
axiom reports clean. Test: `tests/OperatorsOracle.lean` instantiating
(1.1) on `Polynomial ℚ` with `f = X`, `P = derivative` for `n ≤ 4` via
`decide`-free `simp`/`norm_num` on a few evaluations.

### WP-2 Squared annihilator and localization interface

`Certificate/SquaredAnnihilator.lean` (paper Section 3), for any `[Ring Λ]`:

```lean
theorem certificate_of_square (d a b₀ B c h U W V : Λ)
    (hc : c = d * a) (hb : B * d * c = d * b₀)
    (hcert : (1 : Λ) = (c * h * d) * (c * h * d) * U + W * ((c * h * d) * (c * h * d)) * V) :
    (1 : Λ) = d * (a * h * d * (c * h * d) * U - b₀ * h * d * V)
              + (B + W * c * h) * d * ((c * h * d) * V)
```

Proof: rewrite `d * (a*h*d) = c*h*d` from `hc`, `d * (b₀*h*d) = B*d*c*h*d`
from `hb`, expand with `mul_add`, `add_mul`, `mul_sub`, `mul_assoc`, then
`hcert`. Do not use `ring`; the ring is noncommutative. `noncomm_ring`
may help after substituting `hc`.

```lean
structure OreData (d B : Λ) where
  c a b₀ : Λ
  hc : c = d * a
  hne : c ≠ 0
  hb : B * d * c = d * b₀
theorem OreData.of_rightOre [NoZeroDivisors Λ] [Nontrivial Λ]
    (hOre : ∀ x y : Λ, x ≠ 0 → y ≠ 0 → ∃ a b : Λ, a ≠ 0 ∧ x * a = y * b)
    (d B : Λ) (hd : d ≠ 0) : Nonempty (OreData d B)
```

Case `B * d * d = 0`: take `c = d, a = 1, b₀ = 0` (then `B d c = B d d = 0`).
Otherwise apply `hOre (B*d*d) d`.

`Localization/Interface.lean`. Fix `f : A`, a type `Af` with
`[CommRing Af] [Algebra k Af] [Algebra A Af] [IsScalarTower k A Af]
[IsLocalization.Away f Af]`.

```lean
structure LocalizationInterface (k A Af) (f : A) [...] where
  ι : algebra (k := k) (R := A) →ₐ[k] algebra (k := k) (R := Af)
  ι_multiplicationD : ∀ a, ι (multiplicationD a) = multiplicationD (algebraMap A Af a)
  ι_mem_order : ∀ r (P : algebra k A), (P : Module.End k A) ∈ order r → (ι P : Module.End k Af) ∈ order r
  ι_injective : Function.Injective ι
  clearance : ∀ Q : algebra k Af, ∃ (l : ℕ) (P : algebra k A),
    multiplicationD (algebraMap A Af f) ^ l * Q = ι P
namespace LocalizationInterface
theorem f_isUnit : IsUnit (multiplicationD (algebraMap A Af f))              -- IsLocalization.Away.algebraMap_isUnit
noncomputable def fInv : algebra k Af := ↑(f_isUnit.unit⁻¹)
theorem fInv_mul, mul_fInv, fInv_commute_multiplicationD, fInv_pow_mul_pow ...
theorem rightClearance (L) (Q : algebra k Af) :
    ∃ (m : ℕ) (P : algebra k A), Q * multiplicationD (algebraMap A Af f) ^ m = L.ι P
theorem rightClearance_family (L) {ι'} [Fintype ι'] (Q : ι' → algebra k Af) :
    ∃ m, ∀ i, ∃ P, Q i * multiplicationD (algebraMap A Af f) ^ m = L.ι P
theorem ι_pow_multiplicationD (a n) : L.ι (multiplicationD a ^ n) = multiplicationD (algebraMap A Af a) ^ n
end LocalizationInterface
```

`rightClearance`: from `clearance` get `l, P` with `f^l Q = ι P`; obtain
`r` with `P ∈ order r`; put `m = l + r`; then `Q f^m = f^{-l} (ι P) f^{l+r}
= f^{-l} ι (P f^{l+r}) = f^{-l} ι (f^{l} Q') = ι Q'` using (1.2) in
`algebra k A` and `ι_multiplicationD`. Common `m` for a finite family by
taking the maximum and multiplying by the extra power.

### WP-3 Old-chart protection (Lemma 1.2)

`Certificate/OldChartProtection.lean`. Context: `g : A`, `Ag` a
localization at `g` with `Lg : LocalizationInterface k A Ag g`; an
arbitrary `f : A`; `d B T A₀ B₀ : algebra k A`; `U V : algebra k Ag`.

```lean
theorem protect_old_chart
    {rd M rV L m : ℕ}
    (hd : (d : Module.End k A) ∈ order rd) (hT : (T : Module.End k A) ∈ order M)
    (hV : (V : Module.End k Ag) ∈ order rV)
    (hL : M + rd + rV < L)
    (hold : (1 : algebra k Ag) = Lg.ι d * U + Lg.ι B * Lg.ι d * V)
    (hclear : multiplicationD f ^ m = d * A₀ + (B + multiplicationD f ^ L * T) * d * B₀) :
    ∃ U' V' : algebra k Ag,
      (1 : algebra k Ag) = Lg.ι d * U' + Lg.ι (B + multiplicationD f ^ L * T) * Lg.ι d * V'
```

Proof script outline:
1. Let `F := B + multiplicationD f ^ L * T`, `fg := multiplicationD (algebraMap A Ag f)`.
   `Lg.ι F = Lg.ι B + fg ^ L * Lg.ι T` (map_add, map_mul, ι_pow_multiplicationD).
2. `E := fg ^ L * (Lg.ι T * Lg.ι d * V)`; `P := Lg.ι T * Lg.ι d * V` has
   order `≤ M + rd + rV` (ι_mem_order, mul_mem_order).
3. `Lg.ι d * U + Lg.ι F * Lg.ι d * V = 1 + E` by `hold` and rearranging.
4. `exists_threshold` gives `j ≥ 1` with `m ≤ j*L-(j-1)*r`; Lemma 1.1 (on
   the coerced endomorphisms; lift back to the subalgebra with `Subtype.ext`)
   gives `(-E)^j = fg ^ m * W` for some `W : algebra k Ag` (write
   `fg^{a} = fg^m * fg^{a-m}`).
5. `Z := ∑ i ∈ Finset.range j, (-E)^i`; `mul_neg_geom_sum (-E) j : (1 - -E) * Z = 1 - (-E)^j`.
6. `fg ^ m = Lg.ι (multiplicationD f ^ m) = Lg.ι d * Lg.ι A₀ + Lg.ι F * Lg.ι d * Lg.ι B₀`.
7. `U' := U * Z + Lg.ι A₀ * W`, `V' := V * Z + Lg.ι B₀ * W`; verify by
   `calc` expanding `1 = (1+E) Z + (-E)^j`.

Acceptance: builds; axiom report clean; an oracle test instantiating the
statement for `A = Polynomial ℚ`, `g = f = X`, `d = derivative`, `B = 0` is
optional but recommended.

### WP-4 Polynomial evaluation and the right-moved conjugation

`Conjugation/PolynomialEvaluation.lean`. Generic part for
`(D : Type*) [Ring D] [Algebra k D]` (`Polynomial D` is a semiring even
when `D` is noncommutative; `X` is central):

```lean
noncomputable def evalNat (N : ℕ) : Polynomial D →+* D :=
  Polynomial.eval₂RingHom' (RingHom.id D) (N : D) (fun a => (Nat.cast_commute N a).symm)
theorem evalNat_C, evalNat_X, evalNat_monomial
noncomputable def scalarPoly (h : Polynomial k) : Polynomial D := h.map (algebraMap k D)
theorem scalarPoly_commute (h) (q : Polynomial D) : Commute (scalarPoly h) q   -- coefficients central
theorem evalNat_scalarPoly (h) (N) : evalNat N (scalarPoly h) = algebraMap k D (h.eval (N : k))
theorem scalarPoly_mul, scalarPoly_add, scalarPoly_ne_zero (injective algebraMap)
/-- A polynomial over a `k`-vector space vanishing at every natural number is zero. -/
theorem eq_zero_of_forall_evalNat_eq_zero [Field k] [CharZero k] (p : Polynomial D)
    (hp : ∀ N : ℕ, evalNat N p = 0) : p = 0
/-- Generalized binomial coefficient as a polynomial: C(t, j). -/
noncomputable def binomPoly [Field k] [CharZero k] (j : ℕ) : Polynomial k :=
  Polynomial.C ((j.factorial : k)⁻¹) * descPochhammer k j
theorem binomPoly_eval_nat (j N : ℕ) : (binomPoly j).eval (N : k) = (N.choose j : k)
  -- descPochhammer_eval_eq_descFactorial, Nat.choose_eq_descFactorial_div_factorial,
  -- Nat.factorial_dvd_descFactorial, cast of division
theorem binomPoly_comp_nsmul (m j : ℕ) : ((binomPoly j).comp (m • X)).eval (N:k) = ((m*N).choose j : k)
```

Proof of `eq_zero_of_forall_evalNat_eq_zero`: for each `φ : Module.Dual k D`
form `q_φ := p.sum (fun i a => Polynomial.C (φ a) * X ^ i) : Polynomial k`;
show `q_φ.eval (N : k) = φ (evalNat N p) = 0` for all `N` (evalNat of a sum
of monomials; `φ` is `k`-linear and `(N:D)^i = algebraMap k D (N^i)`);
`Polynomial.eq_zero_of_infinite_isRoot` (`Set.infinite_range_of_injective
Nat.cast_injective`) gives `q_φ = 0`, hence `φ (p.coeff i) = 0` for all
`φ, i`; conclude with `Module.forall_dual_apply_eq_zero_iff`.

Chart-specific part (`D := algebra k Af` with `u := L.fInv`, the inverse
of `multiplicationD (algebraMap A Af f)`; write `fA := multiplicationD
(algebraMap A Af f)`):

```lean
/-- ρ^{(m)}_t(P) = Σ_{j ≤ r} C(m t, j) (-1)^j ad^j(P) u^j, as a polynomial in t. -/
noncomputable def rho (m r : ℕ) (P : algebra k Af) : Polynomial (algebra k Af) :=
  ∑ j ∈ Finset.range (r + 1),
    scalarPoly ((binomPoly j).comp (m • Polynomial.X)) *
      Polynomial.C ((-1 : ℤ) ^ j • (adD fA j P * u ^ j))      -- adD: ad at the subalgebra level
theorem evalNat_rho (hP : ↑P ∈ order r) (N) :
    evalNat N (rho m r P) = fA ^ (m * N) * P * u ^ (m * N)
/-- E'(t) = c ρ_t(d c) ρ_{2t}(d). -/
noncomputable def squaredInput (c d : algebra k Af) (r₁ r₂ : ℕ) : Polynomial (algebra k Af) :=
  Polynomial.C c * rho 1 r₁ (d * c) * rho 2 r₂ d
theorem evalNat_squaredInput (h₁ : ↑(d * c) ∈ order r₁) (h₂ : ↑d ∈ order r₂) (N) :
    evalNat N (squaredInput c d r₁ r₂) = (c * fA ^ N * d) * (c * fA ^ N * d) * u ^ (2 * N)
theorem squaredInput_ne_zero [NoZeroDivisors (algebra k Af)] (hc : c ≠ 0) (hd : d ≠ 0) ... :
    squaredInput c d r₁ r₂ ≠ 0            -- evalNat 0 = c*d*c*d ≠ 0
```

`evalNat_rho`: evaluate termwise (`map_sum`, `evalNat_scalarPoly`,
`binomPoly_comp_nsmul`), then the right form of (1.1) with `n = m*N`
(truncated at `r`), multiplied on the right by `u^{mN}`, using
`fA^(n-j) * u^n = u^j` (`fA * u = 1`, commute).

`Chart/PolynomialS38.lean`:

```lean
def S38Poly (D : Type*) [Ring D] [Algebra k D] : Prop :=
  ∀ E : Polynomial D, E ≠ 0 → ∃ h : Polynomial k, h ≠ 0 ∧
    ∃ u w v : Polynomial D, scalarPoly h = E * u + w * E * v
theorem exists_admissible_bound [Field k] [CharZero k] {h : Polynomial k} (hh : h ≠ 0) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, h.eval (N : k) ≠ 0
  -- roots finite (Polynomial.finite_setOf_isRoot), image under ℕ ↪ k bounded
```

### WP-5 Theorem 4.1

`Descent/BoundedOrderSource.lean`. Context: `[Field k] [CharZero k]`,
`A` with `[IsDomain A]`, `f : A`, `Af`, `L : LocalizationInterface k A Af f`,
`[NoZeroDivisors (algebra k Af)]`, `hS : S38Poly (algebra k Af)`.

```lean
theorem exists_bounded_order_sources (d B : algebra k A) (od : OreData d B) (hd : d ≠ 0) :
    ∃ (M l : ℕ) (H : Polynomial k), H ≠ 0 ∧
      ∀ N : ℕ, l + M ≤ N → H.eval (N : k) ≠ 0 →
        ∃ T : algebra k A, (T : Module.End k A) ∈ order M ∧
          ∃ U V : algebra k Af,
            (1 : algebra k Af) = L.ι d * U + L.ι (B + multiplicationD f ^ (N - l - M) * T) * L.ι d * V
```

Proof steps (each a `have`; keep them as separate lemmas if the file grows
past ~400 lines):
1. `c' := L.ι od.c`, `d' := L.ι d`; `c' ≠ 0`, `d' ≠ 0` by injectivity;
   choose orders `r₁, r₂` (`exists_order`).
2. `E := squaredInput c' d' r₁ r₂ ≠ 0`; obtain `h, u', w', v'` from `hS`.
3. Coefficients of `w' * C c'`: for each `i ≤ natDegree`, apply
   `L.clearance` to `(w' * C c').coeff i`; take `l := max l_i`
   (`Finset.sup`), and `P_i' := multiplicationD f ^ (l - l_i) * P_i`, so
   `fA ^ l * (w' * C c').coeff i = L.ι P_i'`. Set `M := max ord P_i'`.
   Define `Pt : Polynomial (algebra k A) := ∑ i, C P_i' * X^i`.
   Key identity: `fA ^ l * evalNat N (w' * C c') = L.ι (evalNat N Pt)`
   (both sides are sums over `i` of `N^i`-multiples; `L.ι` is `k`-linear).
4. `H := h`. Fix `N ≥ l + M` with `h.eval N ≠ 0`; let `hN := algebraMap k _ (h.eval N)` (central unit).
5. Evaluate the certificate: `hN = evalNat N E * u'(N) + w'(N) * evalNat N E * v'(N)`;
   substitute `evalNat_squaredInput`: `evalNat N E = e * e * u ^ (2N)` with
   `e := c' * fA ^ N * d'`. Put `U := u^(2N) * u'(N) * hN⁻¹`,
   `W := w'(N) * hN⁻¹`, `V := u^(2N) * v'(N)`, and prove
   `1 = e*e*U + W*(e*e)*V` (move the central scalar `hN⁻¹`).
6. `certificate_of_square` with `h := fA ^ N`, `d := d'`, `a := L.ι od.a`,
   `b₀ := L.ι od.b₀`, `B := L.ι B`, `c := c'` (hypotheses by `map_mul`, `map_sub`,
   injectivity-free): gives `1 = d' * R' + (L.ι B + W * c' * fA ^ N) * d' * S'`.
7. Show `W * c' * fA ^ N = L.ι (multiplicationD f ^ (N-l-M) * T)` with
   `T := hN⁻¹ • Q` where `Q` comes from (1.2) applied to `evalNat N Pt`
   (order `≤ M`, `N - l ≥ M`): `evalNat N Pt * multiplicationD f ^ (N - l) = multiplicationD f ^ (N-l-M) * Q`.
   Chain: `W * c' * fA^N = hN⁻¹ * (evalNat N (w' * C c')) * fA^N`
   `= hN⁻¹ * u^l * L.ι (evalNat N Pt) * fA^N`
   `= hN⁻¹ * u^l * fA^l * L.ι (evalNat N Pt * multiplicationD f ^ (N-l))`
   `= hN⁻¹ * L.ι (multiplicationD f ^ (N-l-M) * Q)`.
   Note `evalNat N (w' * C c') = w'(N) * c'` (`map_mul`, `evalNat_C`).
8. Conclude with `U := R'`, `V := S'`.

Acceptance: builds; `#print axioms` clean (conditional statement).

### WP-6 Theorem 5.1

`Descent/FiniteCoverPatching.lean`. Context: `[Field k] [CharZero k]`,
`[CommRing A] [IsDomain A] [Algebra k A]`, `s : ℕ`, `f : Fin s → A`,
`Af : Fin s → Type u` with instances (or concretely `Localization.Away (f i)`;
check that `Algebra k (Localization.Away (f i))` and `IsScalarTower k A _`
instances resolve, else parametrize), `L : ∀ i, LocalizationInterface k A (Af i) (f i)`,
`hdom : ∀ i, NoZeroDivisors (algebra k (Af i))`, `hS : ∀ i, S38Poly (algebra k (Af i))`,
`hcover : Ideal.span (Set.range f) = ⊤`, `[NoZeroDivisors (algebra k A)]`,
`hOre : ∀ x y : algebra k A, x ≠ 0 → y ≠ 0 → ∃ a b, a ≠ 0 ∧ x * a = y * b`.

```lean
theorem twoGeneratorIdentity_of_charts : TwoGeneratorIdentity (algebra (k := k) (R := A))
```

Proof:
1. Fix `d ≠ 0`. Invariant `Inv (i : ℕ) : ∃ B : algebra k A, ∀ j : Fin s, (j : ℕ) < i →
   ∃ U V : algebra k (Af j), 1 = (L j).ι d * U + (L j).ι B * (L j).ι d * V`.
   `Inv 0` with `B = 0`.
2. Step `Inv i → Inv (i+1)` for `i < s`: let `i' : Fin s := ⟨i, _⟩`. Obtain
   `od : OreData d B` (`OreData.of_rightOre`). Apply WP-5 at chart `i'`:
   `M, l, H`. For each `j < i` choose orders `rV j` of the stored `V j`;
   `rd` an order of `d`. Pick `N := max (l + M) (N₀ H)` plus
   `M + rd + Finset.sup rV + 1 + l + M` (any explicit expression with
   `N ≥ l+M`, `N ≥ N₀`, and `N - l - M > M + rd + rV j` for all `j`).
   Get `T, U, V` for chart `i'`; `F := B + multiplicationD (f i') ^ (N-l-M) * T`.
   Right-clear: `(L i').rightClearance_family ![U, V]` gives `m, A₀, B₀`
   with `multiplicationD (f i') ^ m = d * A₀ + F * d * B₀` (multiply the
   certificate on the right by `fA^m`, use `ι_pow_multiplicationD`,
   injectivity of `(L i').ι`). For each old `j < i` apply
   `protect_old_chart` with `g := f j`, `f := f i'`, `Lg := L j`. For
   `j = i'` use `U, V`.
3. `Inv s`: one `B` with certificates on all charts. For each `i`, right-clear
   to `multiplicationD (f i) ^ (m i) = d * A i + B * d * B' i`; put
   `m := Finset.sup m`, and multiply by `multiplicationD (f i) ^ (m - m i)`
   on the right to get a common exponent.
4. `Ideal.span_pow_eq_top (Set.range f) hcover m` gives
   `Ideal.span ((· ^ m) '' Set.range f) = ⊤`; via `Ideal.mem_span_range_iff_exists_fun`
   (rewrite the image as a range) obtain `a : Fin s → A` with
   `∑ i, f i ^ m * a i = 1` (`Ideal.eq_top_iff_one`).
5. `1 = multiplicationD 1 = ∑ i, multiplicationD (f i) ^ m * multiplicationD (a i)`
   (`multiplicationD_pow`, `multiplicationD_mul`, `map_sum`-style lemma
   `multiplicationD_sum`), substitute step 3, and factor:
   `= d * (∑ i, A i * multiplicationD (a i)) + B * d * (∑ i, B' i * multiplicationD (a i))`
   (`Finset.mul_sum`, `Finset.sum_add_distrib`).

Acceptance: builds; axiom report clean.

### WP-7 Finite-right-span ascent (Lemma 6.1) and Ore transfer

`Chart/FiniteRankAscent.lean`. Generic; candidate for extraction to
`algebraic-analysis` (`AlgebraicAnalysis/Module/FiniteRightSpanAscent.lean`)
in the Phase III extraction wave. Context: `[Ring T] [Nontrivial T]
[NoZeroDivisors T] [OreLocalization.OreSet (Tᵐᵒᵖ)⁰]` (right Ore for `T`, the
convention of `AlgebraicAnalysis.Module.RankTorsion`), `[Ring S]
[Nontrivial S] [NoZeroDivisors S]`, `φ : T →+* S`.

```lean
def FiniteRightSpan (φ : T →+* S) : Prop :=
  ∃ (m : ℕ) (s : Fin m → S), ∀ x : S, ∃ τ : T, τ ≠ 0 ∧ ∃ t : Fin m → T, x * φ τ = ∑ i, s i * φ (t i)
theorem exists_mul_eq_of_finiteRightSpan (h : FiniteRightSpan φ) (d : S) (hd : d ≠ 0) :
    ∃ (y : S) (a : T), a ≠ 0 ∧ d * y = φ a
theorem twoGeneratorIdentity_of_finiteRightSpan (h : FiniteRightSpan φ)
    (hT : TwoGeneratorIdentity T) : TwoGeneratorIdentity S
theorem rightOre_of_finiteRightSpan (h : FiniteRightSpan φ)
    (hφ : Function.Injective φ) :   -- or derive nonvanishing from Nontrivial S
    ∀ x y : S, x ≠ 0 → y ≠ 0 → ∃ a b : S, a ≠ 0 ∧ x * a = y * b
```

Proof of the first theorem. Let `M := S` as a left `Tᵐᵒᵖ`-module by
`op τ • x := x * φ τ` (define the instance locally; check
`Module.compHom`/`MulOpposite` conventions in
`AlgebraicAnalysis.Module.RankTorsion`). Let `V := LocalizedRightModule T M`
over the division ring `Q := FractionRingOp T` (both from `RankTorsion`).
(a) `V` is spanned over `Q` by the images `s i /ₒ 1`: any `x /ₒ τ` equals
`(x * φ σ) /ₒ (τ σ)`-type expressions; use `FiniteRightSpan` on `x` to
write `x * φ σ = Σ s i * φ (t i)`, then `x /ₒ τ = Σ (s i /ₒ 1) • (t i ...)`.
Conclude `Module.Finite Q V`.
(b) Left multiplication by `d` is `Tᵐᵒᵖ`-linear on `M`
(`d * (x * φ τ) = (d * x) * φ τ`); it induces `Ld : V →ₗ[Q] V`. Construct
it with `OreLocalization.liftExpand` or, if simpler, define
`Ld (x /ₒ τ) := (d * x) /ₒ τ` and prove well-definedness with
`OreLocalization.oreDiv_eq_iff`.
(c) `Ld` injective: `(d * x) /ₒ τ = 0 ↔ ∃ σ ≠ 0, (d * x) * φ σ = 0`
(`localized_oreDiv_one_eq_zero_iff` after clearing `τ`), and
`d * (x * φ σ) = 0 → x * φ σ = 0` (`NoZeroDivisors S`, `d ≠ 0`).
(d) Finite-dimensional injective ⇒ surjective
(`LinearMap.injective_iff_surjective` over a division ring with
`Module.Finite`); pick `z` with `Ld z = 1 /ₒ 1`; write `z = y /ₒ a`
(`OreLocalization.ind`); then `(d * y) /ₒ a = 1 /ₒ 1`, so by
`oreDiv_eq_iff` there are `σ ≠ 0`, `σ'` with `(d*y) * φ σ' = φ (a σ)`... 
unwind to obtain `y' := y * φ σ'`, `a' := a * σ` (nonzero in the domain `T`)
with `d * y' = φ a'`.
Second theorem: certificate `1 = a' r + F a' s` in `T`; apply `φ`;
substitute `φ a' = d * y'`: `1 = d * (y' * φ r) + φ F * d * (y' * φ s)`.
Third theorem: from the first, `x * x' = φ a'`, `y * y' = φ b'`; right Ore
in `T` gives `τ₁ ≠ 0, τ₂` with `a' * τ₁ = b' * τ₂`; then
`x * (x' * φ τ₁) = y * (y' * φ τ₂)` and `x' * φ τ₁ ≠ 0` because
`x * (x' * φ τ₁) = φ (a' τ₁) ≠ 0` (injective `φ`, domain `T`).

Acceptance: builds; clean axioms; test in `tests/FiniteRankAscentOracle.lean`
with `T = S = ℚ` (trivial) and `T = ℚ`, `S = ℚ × ℚ` is NOT a domain, so use
`T = Polynomial ℚ`, `S = Polynomial ℚ` with `φ = id` and `x ↦ x` span.

### WP-8 Étale chart data and chart S38

`Chart/EtaleChartData.lean`. Context: `(k : Type u) [Field k] [CharZero k]
(n : ℕ) (C : Type u) [CommRing C] [Algebra k C]
[Algebra (MvPolynomial (Fin n) k) C] [IsScalarTower k (MvPolynomial (Fin n) k) C]`.
Write `B := MvPolynomial (Fin n) k`, `xC i := algebraMap B C (MvPolynomial.X i)`,
`T := PresentedWeyl k n`.

```lean
structure EtaleChartData where
  ∂ : Fin n → Derivation k C C
  ∂_coord : ∀ i j, ∂ i (xC j) = if i = j then 1 else 0
  ∂_comm : ∀ i j, (∂ i).toLinearMap * (∂ j).toLinearMap = (∂ j).toLinearMap * (∂ i).toLinearMap
  coordinateRigidity : ∀ P : Module.End k C, P ∈ algebra (k := k) (R := C) →
      (∀ i, commutator P (xC i) = 0) → P = multiplication (P 1)
  finiteGenericFibre : ∃ (m : ℕ) (c : Fin m → C), ∀ x : C, ∃ b : B, b ≠ 0 ∧
      ∃ t : Fin m → B, algebraMap B C b * x = ∑ i, c i * algebraMap B C (t i)
  noZeroDivisors : NoZeroDivisors (algebra (k := k) (R := C))
```

(No injectivity of `B → C` and no faithfulness of the Weyl action are
required; see WP-7. Nontriviality of `algebra k C` follows from
`Nontrivial C`, which follows from `NoZeroDivisors` plus `Nontrivial`;
require `[Nontrivial C]`.)

Constructions and theorems:

```lean
noncomputable def weylAction (E : EtaleChartData k n C) : PresentedWeyl k n →ₐ[k] algebra k C
  -- freeWeylLift (Matrix.J (Fin n) k) (differentialGenerator E) (differentialGenerator_commutator E),
  -- copying Stafford38.LocalizedWeylAction: generators ⟨multiplication (xC i), 0, _⟩ and ⟨(E.∂ i).toLinearMap, 1, _⟩;
  -- the commutator proof uses ∂_coord and ∂_comm exactly as in LocalizedWeylAction.differentialGenerator_commutator.
theorem weylAction_X (i) : weylAction E (freeWeylGenerator _ (.inl i)) = multiplicationD (xC i)
theorem weylAction_D (i) : weylAction E (freeWeylGenerator _ (.inr i)) = ⟨(E.∂ i).toLinearMap, 1, _⟩
theorem weylAction_algebraMap (b : B) : weylAction E (polynomialToWeyl b) = multiplicationD (algebraMap B C b)
  -- polynomialToWeyl : MvPolynomial (Fin n) k →ₐ[k] PresentedWeyl k n, X i ↦ generator (.inl i);
  -- the coordinate generators commute, so MvPolynomial.aeval applies.
theorem finiteRightSpan_weylAction [OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰]
    [NoZeroDivisors (PresentedWeyl k n)] (E : EtaleChartData k n C) :
    FiniteRightSpan (weylAction E).toRingHom
theorem twoGeneratorIdentity_chart [OreSet ...] [NoZeroDivisors (PresentedWeyl k n)]
    (E : EtaleChartData k n C) (hW : TwoGeneratorIdentity (PresentedWeyl k n)) :
    TwoGeneratorIdentity (algebra (k := k) (R := C))
theorem rightOre_chart (E) [OreSet ...] [NoZeroDivisors (PresentedWeyl k n)] :
    ∀ x y : algebra k C, x ≠ 0 → y ≠ 0 → ∃ a b, a ≠ 0 ∧ x * a = y * b
```

Proof of `finiteRightSpan_weylAction`: take `m, c` from
`finiteGenericFibre`; define the `k`-submodule
`H := {P : Module.End k C | ∃ τ : T, τ ≠ 0 ∧ ∃ t : Fin m → T, P * weylAction E τ = ∑ i, multiplication (c i) * weylAction E (t i)}`
(closure under addition uses a common right multiple in `T`: from
`OreSet (Tᵐᵒᵖ)⁰` extract `∀ τ₁ τ₂ ≠ 0, ∃ σ₁ σ₂, σ₁ ≠ 0 ∧ τ₁ σ₁ = τ₂ σ₂`; state
this once as `weyl_rightOre`). Check the hypotheses of
`AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration.mem_submodule_of_coordinates'`
(the finite-order variant, see AA-1 below): `hmul`: `multiplication x ∈ H`
via `finiteGenericFibre` and `weylAction_algebraMap`; `hright`: for `P ∈ H`
with witness `τ`, use `weyl_rightOre` on the generator `∂_i` and `τ` to get
`∂_i τ' = τ σ`, so `P ∂_i (weylAction τ') = P (weylAction τ) (weylAction σ)`.
Then every `P ∈ algebra k C` lies in `H`, which is the `FiniteRightSpan`
statement with `s i := multiplicationD (c i)`. Coordinate rigidity is the
`hcoordinate` hypothesis restricted to finite-order operators.

Until AA-1 lands, prove a local copy
`mem_submodule_of_coordinates'` in `GlobalStafford/Generic/CoordinateGeneration.lean`
by copying the AA proof and threading `hQ` into the `hcoordinate` call
(the AA proof already has `hQ : Q ∈ algebra` in scope at that point). Remove
the copy when the AA pin is bumped.

### WP-9 Scalar extension interface

`Chart/ScalarExtension.lean`. Context: `[Field k] [CharZero k]`,
`(D : Type u) [Ring D] [Algebra k D]`, `(K : Type u) [Field K] [Algebra k K]`,
`(DK : Type u) [Ring DK] [Algebra K DK] [Algebra k DK] [IsScalarTower k K DK]`,
`(t : K)`.

```lean
structure ScalarExtensionInterface where
  Θ : Polynomial D →+* DK
  Θ_C : ∀ x : D, Commute (Θ (Polynomial.C x)) (algebraMap K DK t)   -- automatic if Θ X is central; keep explicit
  Θ_scalar : ∀ h : Polynomial k, Θ (scalarPoly h) = algebraMap K DK (Polynomial.aeval t h)
  Θ_injective : Function.Injective Θ
  spanning : ∀ Q : DK, ∃ h : Polynomial k, h ≠ 0 ∧ ∃ P : Polynomial D,
      algebraMap K DK (Polynomial.aeval t h) * Q = Θ P
  aeval_ne_zero : ∀ h : Polynomial k, h ≠ 0 → Polynomial.aeval t h ≠ 0    -- t transcendental over k
theorem s38Poly_of_scalarExtension (I : ScalarExtensionInterface ...)
    (hK : TwoGeneratorIdentity DK) : S38Poly D
```

Proof: `E ≠ 0 ⇒ Θ E ≠ 0`; get `1 = Θ E * u + w * Θ E * v`; `spanning`
for `u, w, v` gives `h_u, h_w, h_v` and `u', w', v'`; the elements
`algebraMap K DK (aeval t h)` are central units in `DK`; multiply the
certificate by `h_u h_w h_v` and regroup:
`Θ (scalarPoly (h_u*h_w*h_v)) = Θ (E * u' * scalarPoly (h_w*h_v) + w' * E * v' * scalarPoly h_u)`;
injectivity gives the identity in `Polynomial D` with
`h := h_u*h_w*h_v ≠ 0`, `u := u' * scalarPoly (h_w*h_v)`, `w := w'`,
`v := v' * scalarPoly h_u` (scalar polynomials commute with everything).

### WP-10 Phase I assembly

`Assembly/Inputs.lean`:

```lean
structure Inputs (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] where
  s : ℕ
  f : Fin s → A
  cover : Ideal.span (Set.range f) = ⊤
  Af : Fin s → Type u
  [instCommRing : ∀ i, CommRing (Af i)] [instAlgk : ∀ i, Algebra k (Af i)] [instAlgA : ∀ i, Algebra A (Af i)]
  [instTower : ∀ i, IsScalarTower k A (Af i)] [instLoc : ∀ i, IsLocalization.Away (f i) (Af i)]
  loc : ∀ i, LocalizationInterface k A (Af i) (f i)
  chartS38Poly : ∀ i, S38Poly (algebra (k := k) (R := Af i))
  chartDomain : ∀ i, NoZeroDivisors (algebra (k := k) (R := Af i))
  globalDomain : NoZeroDivisors (algebra (k := k) (R := A))
  rightOre : ∀ x y : algebra (k := k) (R := A), x ≠ 0 → y ≠ 0 → ∃ a b, a ≠ 0 ∧ x * a = y * b
```

(If bundling types with instances in a structure causes elaboration
trouble, replace `Af` by `Localization.Away (f i)` throughout.)

`Assembly/PhaseI.lean`:

```lean
theorem twoGeneratorIdentity_of_inputs (I : Inputs k A) : TwoGeneratorIdentity (algebra (k := k) (R := A))
def UniversalStatementOfInputs : Prop := ∀ (k : Type u) ... (A : Type u) ..., Inputs k A → TwoGeneratorIdentity (algebra k A)
theorem universalStatement_of_inputs : UniversalStatementOfInputs.{u}
/-- Chart producer: étale chart data over k and over K = RatFunc k, plus a scalar-extension
interface, plus the imported Weyl theorem, give the chart hypothesis. -/
theorem s38Poly_of_chartData
    (E : EtaleChartData k n C) (EK : EtaleChartData (RatFunc k) n CK)
    (I : ScalarExtensionInterface k (algebra k C) (RatFunc k) (algebra (RatFunc k) CK) RatFunc.X)
    [OreSet ((PresentedWeyl (RatFunc k) n)ᵐᵒᵖ)⁰] [NoZeroDivisors (PresentedWeyl (RatFunc k) n)] :
    S38Poly (algebra (k := k) (R := C))
  -- twoGeneratorIdentity_chart EK (Stafford38.universalStatement (RatFunc k) n) then s38Poly_of_scalarExtension
#print axioms twoGeneratorIdentity_of_inputs     -- must be [propext, Classical.choice, Quot.sound]
#print axioms s38Poly_of_chartData               -- same (the Weyl import is axiom-clean)
```

Phase I is complete when every WP-1..WP-10 declaration is `done`,
`open_holes` is empty, `scripts/verify.sh --phase-i` passes (build of
`GlobalStafford`, source audit, axiom audit of the Phase I endpoints), and
`docs/paper-lean-specification.md` maps every paper lemma to its Lean name.

## 4. Phase II: discharge every leaf from Mathlib and the pinned dependencies

Phase II replaces each `Inputs` field by a construction. The order below
is by increasing difficulty; WP-11, WP-13, WP-15 and WP-17 are independent
of each other and may run in parallel. Each work package ends with a
theorem producing exactly the corresponding Phase I hypothesis.

### WP-11 Localization interface construction

`Localization/Construction.lean`. Context: `[Field k] [CharZero k]`? (only
`CommRing k` is needed), `[CommRing A] [IsDomain A] [Algebra k A]
[Algebra.FiniteType k A]`, `f : A`, `hf : f ≠ 0`, `Af` with
`IsLocalization.Away f Af`.

Goal: `noncomputable def localizationInterface : LocalizationInterface k A Af f`.

Construction of `ι`:
1. For `P ∈ order r`, define `extendFun P : Af → Af` on a representative
   `IsLocalization.mk' Af a ⟨f^n, _⟩` by
   `Σ_{j ≤ r} (Ring.choose (-(n:ℤ)) j) • IsLocalization.mk' Af (((ad f)^[j] P) a) ⟨f^(n+j), _⟩`
   (equivalently `(-1)^j * (n+j-1).choose j` with the convention that this
   is `1` for `j = 0` and `0` when `n = 0, j ≥ 1`). Prove independence of
   the representative: it suffices (domain `A`) to compare `(a, n)` with
   `(f*a, n+1)`; the difference is the Pascal identity
   `Ring.choose (-(n+1)) j + Ring.choose (-(n+1)) (j-1) = Ring.choose (-n) j`
   together with `((ad f)^[j] P) (f * a) = f * ((ad f)^[j] P) a + ((ad f)^[j+1] P) a`.
   Use `IsLocalization.mk'_surjective (Submonoid.powers f)` and
   `IsLocalization.mk'_eq_iff_eq` to define the function by
   `Classical.choose` and prove the formula for every representative.
2. `extend P` is `k`-linear; it restricts to `P` on the image of `A`
   (`n = 0`).
3. Uniqueness lemma (state and prove first, it drives everything):
   `theorem ext_of_finite_order (Q₁ Q₂ : Module.End k Af) (h₁ : Q₁ ∈ order r) (h₂ : Q₂ ∈ order r)
      (hA : ∀ a : A, Q₁ (algebraMap A Af a) = Q₂ (algebraMap A Af a)) : Q₁ = Q₂`.
   Induction on `r`: `D := Q₁ - Q₂` has order `≤ r` and vanishes on the
   image of `A`; `commutator D (algebraMap f)` has order `≤ r-1` and
   vanishes on the image of `A`, hence is `0` by induction; so `D`
   commutes with `algebraMap f`, hence with its inverse, and
   `D (a / f^n) = f^{-n} D a = 0`.
4. `extend P ∈ order r`: induction on `r` using
   `commutator (extend P) (algebraMap f) = extend (ad f P)` (from the
   explicit formula and Pascal) and then for general `x = a/f^n`:
   `commutator Q (a * f^{-n})` is expressed through commutators with
   `algebraMap a` and with `f^{-n}`; each is of lower order by induction.
   An alternative that avoids this computation: prove
   `extend P ∈ order r` from the identity
   `multiplication (f^m) * extend P = extend (multiplication (f^m) * P)`... 
   (choose whichever closes first; record the choice in the file docstring).
5. Multiplicativity `extend (P * Q) = extend P * extend Q`: both sides have
   finite order and agree on the image of `A`; apply `ext_of_finite_order`.
   Similarly `extend 1 = 1`, additivity, scalar compatibility; package as
   `ι : algebra k A →ₐ[k] algebra k Af` (the order witness of `P` is
   `Classical.choose P.property`; show the definition does not depend on the
   chosen bound by `ext_of_finite_order`).
6. `ι_multiplicationD`: `extend (multiplication a) = multiplication (algebraMap a)` by uniqueness.
7. `ι_injective`: `extend P = 0 → P = 0` since `extend P` restricts to `P`.
8. `clearance`: for `Q ∈ order r` on `Af` and generators `g_1..g_p` of `A`
   (`Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG`), prove
   `theorem values_mem_span : ∀ a : A, Q (algebraMap a) ∈ Submodule.span A (Q '' {monomials of degree ≤ r})`
   (as an `A`-submodule of `Af` via `algebraMap`): induction on `r` and on
   the monomial degree, using `Q (g * a) = g • Q a + (commutator Q g) a`.
   Finitely many values have a common denominator `f^l`; then
   `(multiplication (algebraMap f))^l * Q` maps the image of `A` into it; its
   restriction `P₀ : A → A` is `k`-linear of order `≤ r` (commutators restrict),
   and `extend P₀ = multiplication (f)^l * Q` by `ext_of_finite_order`.

Acceptance: `localizationInterface` builds for every domain of finite type;
`#print axioms` clean. Provide the instance-level corollary
`localizationInterfaceAway : LocalizationInterface k A (Localization.Away f) f`.

### WP-12 Étale derivations, commutation, coordinate rigidity

`Chart/EtaleDerivations.lean`. Context: `B := MvPolynomial (Fin n) k`,
`[CommRing C] [Algebra k C] [Algebra B C] [IsScalarTower k B C]
[Algebra.FormallyEtale B C]` (from `Algebra.Etale B C`).

1. Lifting: `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k B C : C ⊗[B] Ω[B⁄k] ≃ₗ[C] Ω[C⁄k]`.
   Combine with `KaehlerDifferential.linearMapEquivDerivation` on both sides
   and `KaehlerDifferential.mvPolynomialBasis` (basis `d X_i` of `Ω[B⁄k]`)
   to define `liftDerivation (i : Fin n) : Derivation k C C` with
   `liftDerivation i (algebraMap B C b) = algebraMap B C (MvPolynomial.pderiv i b)`.
   Concretely: the `C`-linear map `Ω[C⁄k] → C` is the composite of the
   inverse equivalence with `C ⊗[B] Ω[B⁄k] → C`, `c ⊗ ω ↦ c * (coefficient of d X_i in ω)`.
2. `∂_coord` from `pderiv_X`.
3. Uniqueness: any `k`-derivation `δ` of `C` vanishing on the image of `B`
   is `0`: `δ` corresponds to a `C`-linear map `Ω[C⁄k] → C` that kills the
   image of `C ⊗ Ω[B⁄k]`, which is all of `Ω[C⁄k]` by the equivalence.
   Alternatively: `δ` is a `B`-derivation, `Derivation B C C ≃ (Ω[C⁄B] →ₗ[C] C)`
   and `Subsingleton Ω[C⁄B]` (`Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`).
   Use the second route; it is one line once the instances line up.
4. `∂_comm`: `[∂_i, ∂_j]` is a derivation (`Derivation.commutator` or define
   `⟨⟨[∂_i,∂_j]⟩, leibniz⟩` by hand) vanishing on `B`; by 3 it is zero.
5. `coordinateRigidity`: for `P ∈ order m` commuting with all `xC i`:
   induction on `m`. Show first that `P` commutes with every
   `algebraMap B C b` (`commutator P (b₁ b₂) = commutator P b₁ * b₂ + b₁ * commutator P b₂`
   as endomorphisms, `MvPolynomial.induction_on`). Order `0`: `P` is a
   multiplication. Order `m+1`: for each `c : C`, `commutator P c` has
   order `≤ m` and commutes with all `xC i` (Jacobi:
   `commutator (commutator P c) x = commutator (commutator P x) c` since `c, x` commute),
   so `commutator P c = multiplication (μ c)` with
   `μ c := P (c * 1) - c * P 1`. Show `μ` is a `k`-derivation of `C`
   (Leibniz from `commutator P (c c') = commutator P c * c' + c * commutator P c'`
   evaluated at `1`) vanishing on `B`; by 3, `μ = 0`, so `P` has order `0`.

Deliverable: `noncomputable def etaleChartData_of_etale (hcoreDomain...) : EtaleChartData k n C`
assembling 1–5 with the fields of WP-13 and WP-14.

### WP-13 Finite generic fibre

`Chart/GenericFibre.lean`. Context as in WP-12 plus `[IsDomain C]`
`[Algebra.Etale B C]`.

Let `L := FractionRing B` and `CL := L ⊗[B] C` (or
`Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors B))`; use
whichever has `IsLocalization` and `Algebra.Etale L _` instances with least
friction; Mathlib provides `Algebra.Etale.baseChange : Etale L (L ⊗[B] C)`).
1. `CL` is a domain: it is the localization of the domain `C` at the
   submonoid `B \ 0` mapped into `C`, which consists of nonzero elements
   because `B → C` is injective (see 3 below). Use
   `IsLocalization.isDomain_of_...`/`IsLocalization.isDomain_localization`;
   if using the tensor product, transport along the `IsLocalization`
   equivalence (`IsLocalization.algEquiv`).
2. `Algebra.Etale.iff_exists_algEquiv_prod` over the field `L`: `CL ≃ₐ[L] Π i, Ai i`
   with each `Ai i` a finite field extension. A nontrivial domain has no
   nontrivial product decomposition: `I` has exactly one element (if
   `I = ∅` then `CL` is trivial; if two indices then idempotents). Hence
   `Module.Finite L CL`.
3. Injectivity of `algebraMap B C`: `Algebra.Etale` gives `Module.Flat B C`
   (`Algebra.Smooth`→ flat, `Mathlib/RingTheory/Smooth/Flat.lean`; search
   `Algebra.FormallySmooth.flat` / `Algebra.Smooth.flat` / `Module.Flat.of_...`);
   for `b ≠ 0`, `b • : B → B` injective ⇒ `b • : C → C` injective
   (`Module.Flat.lTensor_preserves_injective_linearMap` with `C ⊗[B] B ≃ C`);
   `b • 1 = 0` would force `C = 0`.
4. From `Module.Finite L CL` get `c : Fin m → C` whose images span `CL`
   over `L` (clear denominators of a finite generating set); for `x : C`,
   write `1 ⊗ x = Σ (b_i / b) • (1 ⊗ c i)` and clear `b`; injectivity of
   `C → CL` (localization of a domain at nonzero elements) turns the
   equation in `CL` into `b * x = Σ c i * t i` in `C`.

Deliverable: `theorem finiteGenericFibre_of_etale : ∃ m c, ∀ x, ∃ b ≠ 0, ∃ t, algebraMap B C b * x = ∑ i, c i * algebraMap B C (t i)`
and `theorem algebraMap_injective_of_etale`.

### WP-14 Chart operator ring is a domain

`Chart/ChartDomain.lean`. Context: `E` as produced by WP-12 (derivations
`∂ i`, coordinates `xC i`, rigidity), `[IsDomain C]`, `[CharZero k]`.

1. `partialMonomial (α : Fin n →₀ ℕ) : Module.End k C := ∏ i, (∂ i).toLinearMap ^ (α i)`
   (well defined since the `∂ i` commute; use `Finset.noncommProd` or a
   fixed product order together with `∂_comm`).
2. Left-`C` linear independence: if `Σ_α c_α • partialMonomial α = 0`
   (finite support) then all `c_α = 0`. Evaluate on
   `algebraMap B C (MvPolynomial.monomial α₀ 1)` for `α₀` minimal in total
   degree among the support: `partialMonomial α (X^{α₀}) = algebraMap (pderiv-iterate)`
   equals `α₀!` if `α = α₀`, and `0` if `|α| ≥ |α₀|` and `α ≠ α₀`
   (`MvPolynomial.pderiv_monomial`), giving `c_{α₀} * α₀! = 0`, so
   `c_{α₀} = 0` in characteristic zero; iterate (strong induction on the
   number of elements of the support of minimal degree).
3. Spanning: every `P ∈ algebra k C` is `Σ_α multiplication c_α * partialMonomial α`
   (finite sum) — from `mem_submodule_of_coordinates'` with
   `H := Submodule.span k {multiplication c * partialMonomial α}` (right
   composition by `∂ i` maps the spanning set into itself using `∂_comm`).
4. Normal-form coefficients: define `coeffs P : (Fin n →₀ ℕ) →₀ C` by
   choice and uniqueness (2+3), the total degree `deg P`, and the top
   symbol `symbol P : MvPolynomial (Fin n) C := Σ_{|α| = deg P} monomial α (coeffs P α)`.
5. Composition rule: `partialMonomial α * multiplication c = Σ_{β ≤ α} (α.choose β) • multiplication (partialMonomial (α - β) c) * partialMonomial β`
   (multivariate Leibniz; by induction on `α` from
   `(∂ i) * multiplication c = multiplication c * (∂ i) + multiplication (∂ i c)`).
   Consequently `deg (P * Q) ≤ deg P + deg Q` and, when both are nonzero,
   the degree-`(deg P + deg Q)` part of `P * Q` has coefficients
   `Σ_{α+β=γ} coeffs P α * coeffs Q β`, that is
   `symbol (P*Q)` restricted to top degree equals `symbol P * symbol Q` in
   `MvPolynomial (Fin n) C`, a domain (`MvPolynomial.instIsDomain`).
6. Conclude `NoZeroDivisors (algebra k C)`: `P, Q ≠ 0 ⇒ symbol P, symbol Q ≠ 0 ⇒ symbol P * symbol Q ≠ 0 ⇒ P * Q ≠ 0`
   (its top coefficients are not all zero, by linear independence).

This is the largest Phase II package (estimate 700–1000 lines). Split into
`ChartDomain/Monomials.lean` (1–2), `ChartDomain/NormalForm.lean` (3–4),
`ChartDomain/Symbol.lean` (5–6) if it exceeds 400 lines. Escalate early if
the Leibniz rule (5) resists; a fallback is a lexicographic leading-term
argument (leading monomial of `P * Q` is the sum of leading monomials,
with coefficient `c_α d_β ≠ 0`) which needs only that the correction terms
in (5) have `∂`-exponent strictly below `α` in the lexicographic order.

### WP-15 Weyl algebra: domain and right Ore

`Weyl/OreDomain.lean`. Goals:

```lean
instance : NoZeroDivisors (PresentedWeyl k n)
instance : OreLocalization.OreSet ((PresentedWeyl k n)ᵐᵒᵖ)⁰     -- right Ore condition for T
theorem weyl_rightOre : ∀ x y : PresentedWeyl k n, x ≠ 0 → y ≠ 0 → ∃ a b, a ≠ 0 ∧ x * a = y * b
```

Routes, in order of preference:
1. Domain via the PBW basis `Stafford38.WeylPBW.presentedPBWBasis` and the
   leading-symbol calculus of `Stafford38/Weyl/LeadingSymbol.lean`,
   `SymbolCompatibility.lean`, `CommutatorSymbol.lean`: locate a theorem
   stating that the principal (top-weight) component of a product is the
   product of principal components (search for `presentedPrincipalComponent`
   and `mul`); the symbol ring `SymbolRing k n = MvPolynomial (PhaseVar n) k`
   is a domain. If no such theorem exists, prove it from
   `presentedCoefficientOrdered_mul` (in `PBW.lean`).
2. Right Ore via right noetherian: `AlgebraicAnalysis.Ore.RightHilbertBasis`
   gives right-Noetherianity of a derivation-Ore stage over a right
   noetherian coefficient ring; `Stafford38/Ore/PairStage.lean` and
   `IteratedPairStage` build the Weyl algebra by iterated stages; transport
   `IsNoetherianRing (·)ᵐᵒᵖ` along `presentedIteratedEquiv`. Then prove the
   generic lemma (also a candidate for AA):
   `theorem rightOre_of_rightNoetherian_domain [IsNoetherianRing Rᵐᵒᵖ] [NoZeroDivisors R] : ∀ x y ≠ 0, ∃ a b, a ≠ 0 ∧ x * a = y * b`
   (if `x R ∩ y R = 0` then `Σ_{i<N} y^i x R` is direct for every `N`, an
   infinite strictly ascending chain of right ideals).
3. Fallback for 2 if the tower transport is too heavy: prove the right Ore
   condition directly for `PresentedWeyl` by the classical
   filtered-dimension count (Goldie's argument): if `xR ∩ yR = 0` then the
   right ideal `xR + yR` has PBW-dimension growth exceeding that of `R`;
   compare `Finrank` of the weight pieces `presentedWeightPiece`. This
   needs the dimension formula for `presentedWeightPiece`; only attempt
   after 2 fails.

Convert the `OreSet` instance from `weyl_rightOre` (nonzero divisors of the
opposite ring; `ore_right_mul_ne_zero`-style obligations are the domain
property).

### WP-16 Scalar extension construction

`Chart/ScalarExtensionConstruction.lean`. Context: `K := RatFunc k`,
`t := RatFunc.X`, `CK := K ⊗[k] C`, `DK := algebra (k := K) (R := CK)`.

1. `Θ₀ (P : algebra k C) : DK := ⟨LinearMap.baseChange K (P : Module.End k C), _⟩`.
   Order preservation: prove by induction on `r` that
   `P ∈ order r → LinearMap.baseChange K P ∈ order r`; for the inductive
   step it suffices to check `commutator (baseChange P) (κ ⊗ₜ c)` for pure
   tensors (`TensorProduct.induction_on` and linearity of the commutator in
   its second argument), where it equals `baseChange (commutator P c)`
   composed with the central scalar `κ`.
2. `Θ₀` is a `k`-algebra homomorphism (`LinearMap.baseChange_comp`,
   `baseChange_id`, `baseChange_add`, `baseChange_smul`).
3. `Θ := Polynomial.eval₂RingHom' Θ₀.toRingHom (multiplicationD (algebraMap K CK t)) (centrality)`;
   `Θ_scalar` by `Polynomial.eval₂` on scalar polynomials.
4. Injectivity: choose a `k`-basis of `K` extending `{t^i}` (or use that
   `Polynomial k → RatFunc k` is injective and `TensorProduct` with a free
   module: `K ⊗[k] C ≃ (basis of K) →₀ C`, `Basis.tensorProduct` with a
   basis of `C` as a `k`-vector space); if `Θ (Σ C P_i X^i) = 0` then for
   every `c`, `Σ t^i ⊗ P_i c = 0`, so each `P_i c = 0`.
5. Spanning: build `EK : EtaleChartData K n CK` (WP-12/13/14 applied over
   `K`, with `Algebra (MvPolynomial (Fin n) K) CK` obtained from
   `Algebra.Etale.baseChange` and `MvPolynomial.algebraTensorAlgEquiv`), so
   coordinate generation over `K` writes any `Q ∈ DK` as
   `Σ_α multiplicationD c'_α * (EK.∂)^α` with `c'_α ∈ CK`, where
   `EK.∂ i = baseChange (E.∂ i)` (by uniqueness of lifts over `K`). Each
   `c'_α = Σ_j κ_j ⊗ c_j`; let `h` be the product of the denominators of the
   finitely many `κ_j` (`RatFunc.denom`), so `aeval t h * κ_j` is the image of
   a polynomial; then `aeval t h • Q = Θ P` for an explicit `P`.
6. `aeval_ne_zero`: `Polynomial.aeval RatFunc.X h = algebraMap k[X] K h`,
   injective (`RatFunc.algebraMap_injective`).

Deliverable: `noncomputable def scalarExtensionInterface : ScalarExtensionInterface k (algebra k C) K DK t`.

### WP-17 Smooth cover by étale charts

`Chart/SmoothCover.lean`. Context: `[Field k] [CharZero k] [CommRing A]
[IsDomain A] [Algebra k A] [Algebra.Smooth k A]`.

1. `Algebra.Smooth.exists_span_eq_top_isStandardSmooth k A : ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ x ∈ s, IsStandardSmooth k (Localization.Away x)`.
2. Finite subcover: `Ideal.span_eq_top_iff_finite` (or
   `Submodule.mem_span_finite_of_mem_span` applied to `1`) gives a
   `Finset`; discard `0` (span unchanged); enumerate as `f : Fin s → A`.
3. For each `x ≠ 0` with `C := Localization.Away x` (a domain by
   `IsLocalization.isDomain_localization`), `IsStandardSmooth k C` gives via
   `IsStandardSmooth.iff_exists_basis_kaehlerDifferential` a finite type
   `I` and `y : I → C` with `Ω[C⁄k]` free on `d y`. (`Finite I`: a basis of
   the finitely generated module `Ω[C⁄k]` — `Module.Finite` from
   `EssFiniteType` + `FormallySmooth` instance in `Smooth/Basic.lean` — is finite:
   `Module.Finite.finite_basis`.) Fix `e : I ≃ Fin n`.
4. Define `Algebra (MvPolynomial (Fin n) k) C` by `MvPolynomial.aeval (y ∘ e.symm)`
   (as `RingHom.toAlgebra`; ensure `IsScalarTower k _ C`).
5. Prove `Algebra.Etale (MvPolynomial (Fin n) k) C`:
   - `FormallyUnramified`: `Ω[C⁄MvPolynomial] = 0` because the map
     `C ⊗ Ω[MvPolynomial⁄k] → Ω[C⁄k]` is surjective (its image contains the
     basis `d y`), and `KaehlerDifferential.exact_mapBaseChange_map` / the
     surjection `Ω[C⁄k] → Ω[C⁄P]` with kernel generated by that image.
   - `FormallySmooth` over `P := MvPolynomial (Fin n) k`: use
     `Algebra.FormallySmooth.iff_subsingleton_and_projective` (in
     `Mathlib/RingTheory/Smooth/Kaehler.lean`): `Ω[C⁄P] = 0` is projective;
     `Subsingleton (H1Cotangent P C)` from the Jacobi–Zariski exact
     sequence `H1Cotangent k C → H1Cotangent P C → C ⊗[P] Ω[P⁄k] → Ω[C⁄k]`
     (`Algebra.H1Cotangent.exact_δ_mapBaseChange`), `H1Cotangent k C = 0`
     (`FormallySmooth k C`, instance `IsStandardSmooth.subsingleton_h1Cotangent`
     or `Algebra.FormallySmooth.iff_subsingleton_and_projective`), and
     injectivity of `C ⊗[P] Ω[P⁄k] → Ω[C⁄k]` (it maps the basis `1 ⊗ dX_i`
     to the basis `d y_i`).
   - `FinitePresentation P C`: `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k P C`.
   Alternative route if the cotangent-complex API is awkward: unfold
   `IsStandardSmooth` to a `SubmersivePresentation` and reorganize it as a
   presentation of relative dimension `0` over the polynomial ring in the
   free variables (`Etale.iff_isStandardSmoothOfRelativeDimension_zero`).
   Record which route was used.
6. Package: for each chart `i`, `EtaleChartData k (n i) (Localization.Away (f i))`
   (WP-12/13/14), over `RatFunc k` as well (WP-16), the localization
   interface (WP-11), the chart domain property, `S38Poly` via
   `s38Poly_of_chartData`.

### WP-18 Global domain, global right Ore, closure

`Assembly/Closure.lean`:
1. `NoZeroDivisors (algebra k A)`: `ι` of any chart is injective and the
   chart operator ring is a domain.
2. Right Ore of `algebra k A`: from `rightOre_chart` for chart `0` (any
   chart) and `rightClearance`: given `x, y ≠ 0` in `algebra k A`,
   `ι x, ι y ≠ 0` in the chart; `ι x * a' = ι y * b'` with `a' ≠ 0`;
   right-clear `a', b'` by a common `f^m`: `a' f^m = ι a`, `b' f^m = ι b`;
   injectivity gives `x * a = y * b`, and `a ≠ 0` since `a' f^m ≠ 0`
   (`f` acts as a unit).
3. `noncomputable def inputs : Inputs k A` and
   `theorem universalStatement : ∀ (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A], TwoGeneratorIdentity (algebra (k := k) (R := A))`.
4. `#print axioms GlobalStafford.universalStatement` must print exactly
   `[propext, Classical.choice, Quot.sound]`.

## 5. Phase III: Palomar packaging

### WP-19 Solution, consumers, verification

1. `Solution.lean`: import `GlobalStafford.Assembly.Closure`, restate the
   Challenge definitions verbatim (same names in namespace
   `GlobalStaffordChallenge`; do NOT import `Challenge`), prove
   `IsOrderLE n P ↔ P ∈ AlgebraicAnalysis.DifferentialOperators.order n`
   by induction (`multiplication`, `commutator` are definitionally the same),
   hence `IsDifferentialOperator P ↔ P ∈ algebra`, and transport
   `GlobalStafford.universalStatement` to `GlobalStaffordChallenge.universalStatement`
   (coerce `d` into the subalgebra, apply, coerce back; the products of
   subalgebra elements coerce to products of endomorphisms).
2. `comparator.json` already names `GlobalStaffordChallenge.universalStatement`.
3. `GlobalStaffordTest/Consumer.lean` and `tests/`: literal consumers
   (a) the Challenge-shaped statement for `A = MvPolynomial (Fin 2) ℚ`
   (which is `Algebra.Smooth`), (b) a chart-level consumer, (c) the
   Phase I conditional theorem; each with `#print axioms`.
4. `scripts/verify.sh`: full build, source audit (exactly one `sorry`, in
   `Challenge.lean`; no `axiom`), pin audit, axiom audit of the endpoints
   listed in `docs/verification.md`, consumers, then
   `scripts/bootstrap-palomar-tools.sh` and `scripts/verify-palomar.sh`
   (Comparator + NanoDa + Lean kernel, sandboxed by Landrun).
5. Independent replay: fresh credential-free clone in a sandbox without
   access to the research repository; record commands, exit codes, tool
   revisions and artifact hashes in `docs/verification-results.json`;
   write `docs/verification.md`.
6. Metadata: `formalization.yaml` (`registration_status:
   public-candidate-not-registered` until a human registers), `CITATION.cff`,
   `.zenodo.json`, `NOTICE`, `docs/release-runbook.md` (human-only actions:
   visibility, signed tag, Zenodo, Palomar form at
   <https://submit.palomar-registry.org/> with repository
   `itpplasma/global-stafford-formal`, the selected commit, `comparator.json`,
   `formalization.yaml`, compared declaration
   `GlobalStaffordChallenge.universalStatement`).
7. Extraction wave to `algebraic-analysis`: `FiniteRightSpanAscent`,
   `rightOre_of_rightNoetherian_domain`, the polynomial-evaluation
   utilities, `mem_submodule_of_coordinates'`; each with a provenance record
   and a same-change pin bump here. Only axiom-clean, application-independent
   declarations move.

## 6. Extensions to `algebraic-analysis` (AA)

| Id | Change | Consumer | Status |
| --- | --- | --- | --- |
| AA-1 | Add `mem_submodule_of_coordinates'` and `mem_subalgebra_of_coordinates'` whose `hcoordinate` quantifies only over `P ∈ algebra`; derive the unprimed theorems from them. Backward compatible. | WP-8, WP-14, WP-16 | done (`faa64814`) |
| AA-2 | `AlgebraicAnalysis/Module/FiniteRightSpanAscent.lean` (WP-7 generic content). | WP-8 | after Phase I |
| AA-3 | `rightOre_of_rightNoetherian_domain`. | WP-15 | after Phase II |
| AA-4 | Polynomial evaluation over a noncommutative `k`-algebra (`evalNat`, `scalarPoly`, vanishing lemma, `binomPoly`). | WP-4 | after Phase I |

Dependency-resolution rule: this repository pins AA in `lakefile.toml`;
`stafford38-formal` pins the older AA commit `dfdd2da0`. Lake uses the root
manifest's revision for a shared package, so after a bump every
`Stafford38` module imported here must still build against the new AA;
`scripts/verify.sh` builds `Stafford38.FoundationClosure` and
`Stafford38.LocalizedDifferentialCorollaries` to check this. AA changes must
be additive.

## 7. Literature leaves (Phase I hypotheses) and their Phase II discharge

| Leaf | Phase I carrier | Phase II source |
| --- | --- | --- |
| Operators extend to `A_f`; left denominator clearance | `LocalizationInterface` | WP-11 (elementary; finite type of `A`) |
| Étale lifting of derivations, Weyl relations, coordinate rigidity | `EtaleChartData.∂, ∂_coord, ∂_comm, coordinateRigidity` | WP-12 (Mathlib `tensorKaehlerEquivOfFormallyEtale`, unramified) |
| Finite generic fibre | `EtaleChartData.finiteGenericFibre` | WP-13 (Mathlib `Etale.iff_exists_algEquiv_prod`, flatness) |
| `D_k(C)` domain | `EtaleChartData.noZeroDivisors` | WP-14 (PBW freeness + symbol) |
| Weyl algebra domain and right Ore | instances in WP-8 hypotheses | WP-15 (stafford38-formal PBW, AA Hilbert basis) |
| Base change to `k(t)` | `ScalarExtensionInterface` | WP-16 |
| Smooth ⇒ finite étale principal cover | `Inputs.f, cover` and chart data | WP-17 (Mathlib `exists_span_eq_top_isStandardSmooth`) |
| Global domain and right Ore | `Inputs.globalDomain, rightOre` | WP-18 (from chart 0 and clearance) |
| Weyl S38 | `Stafford38.universalStatement` (imported, axiom-clean) | none needed |

## 8. Agent workflow

- Work packages are claimed by editing the status column of Section 9
  and committing. One agent per work package; WP-1..WP-4 are sequential
  prerequisites, WP-5 needs WP-1..4, WP-6 needs WP-3 and WP-5, WP-7..WP-9
  are independent of WP-5/6, WP-10 needs all. Phase II packages: WP-11,
  WP-13, WP-15 independent; WP-12 before WP-14 and WP-16; WP-17 after
  WP-12..16; WP-18 last.
- Commit after every green `lake build` of the file being worked on, at
  least hourly, and push to `origin main` immediately. Commit messages
  name the work package and the declarations added.
- A `sorry` may be committed only as a stub of a statement written in this
  plan, listed in `open_holes` (file, declaration, reason). Remove the entry
  in the commit that closes the hole.
- Escalation: after two failed attempts at the same lemma, or one hour
  without progress, stop, write the exact Lean goal state and what was tried
  into `docs/escalations/<wp>-<lemma>.md`, commit, and report "ESCALATE" with
  the file path. The controller reassigns to a stronger model; that model
  appends its resolution to the same file.
- Never modify `Challenge.lean` except to fix a typo in a comment; any change
  to the statement reopens Phase III and must be recorded in
  `docs/paper-lean-specification.md`.
- Never add `axiom`. Never use `native_decide` or `Lean.ofReduceBool`.
- Run `lake env lean --trust=0` on a scratch file with `#print axioms` for
  every completed public theorem before marking it `done`.

## 9. Work-package status

| WP | Title | Phase | Status | Owner | Notes |
| --- | --- | --- | --- | --- | --- |
| WP-1 | Operators: binomial formulas, contractive powers | I | done | sonnet | merged 2026-09-07 |
| WP-2 | Squared annihilator, Ore data, localization interface | I | done | sonnet | merged 2026-09-07 |
| WP-3 | Old-chart protection (Lemma 1.2) | I | done | sonnet | merged 2026-09-07; includes `rightClearance` |
| WP-4 | Polynomial evaluation, ρ, E', S38Poly | I | done | sonnet | merged 2026-09-07 (`RightMoved.lean` holds ρ and E') |
| WP-5 | Bounded-order sources (Theorem 4.1) | I | todo | | |
| WP-6 | Finite-cover patching (Theorem 5.1) | I | done | sonnet | merged 2026-09-07; takes `BoundedSourceProducer` (WP-5 shape) as hypothesis, wired in WP-10 |
| WP-7 | Finite-right-span ascent (Lemma 6.1) | I | done | sonnet | merged 2026-09-07; candidate for AA-2 |
| WP-8 | Étale chart data, Weyl action, chart S38 | I | todo | | needs AA-1 or local copy |
| WP-9 | Scalar extension interface | I | done | sonnet | merged 2026-09-07 |
| WP-10 | Phase I assembly and audit | I | todo | | |
| WP-11 | Localization interface construction | II | todo | | |
| WP-12 | Étale derivations and coordinate rigidity | II | todo | | |
| WP-13 | Finite generic fibre | II | todo | | |
| WP-14 | Chart operator ring is a domain | II | todo | | largest |
| WP-15 | Weyl domain and right Ore | II | todo | | |
| WP-16 | Scalar extension construction | II | todo | | |
| WP-17 | Smooth cover by étale charts | II | todo | | |
| WP-18 | Closure and axiom audit | II | todo | | |
| WP-19 | Solution, consumers, Palomar verification, metadata | III | todo | | |
| AA-1 | Finite-order coordinate generation in AA | I | done; pin bumped to `faa64814` 2026-09-07 | sonnet | |

## 10. Build and verification commands

```sh
lake exe cache get          # Mathlib oleans
lake build                  # GlobalStafford and Solution (default targets)
lake build GlobalStafford.Operators.Commutator   # a single module
scripts/verify.sh           # full audit (Phase III)
scripts/bootstrap-palomar-tools.sh && scripts/verify-palomar.sh
```

The dependency packages `stafford38Formal` and `algebraicAnalysis` are
built from source on first use; expect a long first build.
