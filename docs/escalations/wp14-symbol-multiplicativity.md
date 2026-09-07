# WP-14 escalation: composition rule and symbol multiplicativity (PLAN.md steps 5–7)

Status: steps 1–4 of WP-14 are done, committed, and pushed on branch `wp14`
(commits `7bf8c72`, `48032cc`, `412f51d`, `9995a83`), no `sorry`, `#print
axioms` shows only `propext, Classical.choice, Quot.sound` for every
declaration below. Steps 5–7 (`ChartDomain/Symbol.lean` plus the final
`ChartDomain.lean` assembly and `tests/ChartDomainOracle.lean`) are not
started. This file hands off exactly what remains.

## What is already built

- `GlobalStafford/Chart/ChartDomain/Monomials.lean` (steps 1–2):
  - `partialMonomial (α : Fin n →₀ ℕ) : Module.End k C`, the iterated
    coordinate derivation `∏ i, (∂_i)^{α i}` as a `Finset.noncommProd` over
    `liftDerivation_pow_commute_pairwise` (generalized to an arbitrary
    finset argument `s`, not just `Finset.univ` — this was the key fix that
    made all the `Finset.noncommProd` manipulation tractable without
    dependent-rewrite ("motive is not type correct") failures: never use
    `Set.Pairwise.mono` to transport a commute proof across finsets; instead
    re-derive it fresh with the general lemma, since any two proofs of a
    `Prop` are defeq).
  - `partialMonomial_zero`, `partialMonomial_single`, `partialMonomial_add`
    (multiplicativity: `partialMonomial (α + β) = partialMonomial α *
    partialMonomial β`), `partialMonomial_mem_algebra`.
  - `liftDerivation_pow_algebraMap`, `pderiv_iterate_monomial`,
    `descFactorial_succ'`: the single-variable iterated-derivative-of-monomial
    computation.
  - `partialMonomial_finset_monomial`: the general multi-index formula for
    `partialMonomial α` acting on `algebraMap (B k n) C (monomial β r)`
    (descending-factorial coefficient, truncated-subtracted exponent),
    proved by `Finset.cons_induction`.
  - `partialMonomial_monomial_self : partialMonomial β (algebraMap (monomial
    β 1)) = algebraMap k C (∏ i, (β i)!)`.
  - `partialMonomial_monomial_eq_zero_of_degree_le : β.degree ≤ α.degree →
    α ≠ β → partialMonomial α (algebraMap (monomial β r)) = 0`.
- `GlobalStafford/Chart/ChartDomain/NormalForm.lean` (steps 3–4, needs
  `[IsDomain C]` in addition to the Monomials.lean context):
  - `algebraMap_factorial_ne_zero`.
  - `linearIndependent_partialMonomial : LinearIndependent C partialMonomial`
    in `Module.End k C` viewed as a `C`-module by left multiplication
    (Mathlib's generic `LinearMap.module` instance already gives `(c • P) x
    = c * P x` definitionally — verified, no custom instance needed). Proved
    by `Finset.strongInduction` on the finite support, peeling off a
    minimal-total-degree multi-index at each step (`Finset.exists_min_image`
    with `Finsupp.degree`) and evaluating at the corresponding monomial.
  - `mem_span_partialMonomial : P ∈ algebra k C → P ∈ Submodule.span C
    (Set.range partialMonomial)`, via
    `AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration.mem_submodule_of_coordinates'`
    applied to `(Submodule.span C (range partialMonomial)).restrictScalars k`
    (a `C`-span is automatically a `k`-submodule; `hmul` uses
    `partialMonomial_zero`, `hright` uses `partialMonomial_add` +
    `partialMonomial_single`).

Recurring Lean gotcha hit repeatedly while writing these two files, worth
knowing before continuing: **a bare use of `partialMonomial` (or any
declaration whose only occurrence of the section variable `n` is inside an
instance argument such as `[Algebra.FormallyEtale (B k n) C]`) gets stuck
with a metavariable for `n`** unless `n` is pinned by an explicit, literal
mention in the statement (e.g. ascribe `(0 : Fin n →₀ ℕ)` instead of a bare
`0`, or add a type ascription `(... : (Fin n →₀ ℕ) → Module.End k C)` around
a bare `partialMonomial` passed to `Set.range`, or add `(n := n)` directly).
The fix is always the same: make `n` appear literally in the surface syntax
near the application that needs it.

## The target theorem (do not restate; this is `ChartDomain.lean`)

```lean
theorem noZeroDivisors_algebra_of_etale
    {k : Type u} [Field k] [CharZero k] {n : ℕ} {C : Type u} [CommRing C] [IsDomain C]
    [Algebra k C] [Algebra (MvPolynomial (Fin n) k) C]
    [IsScalarTower k (MvPolynomial (Fin n) k) C]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) k) C]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) k) C)) :
    NoZeroDivisors (algebra (k := k) (R := C))
```

in namespace `GlobalStafford.Chart`, file `GlobalStafford/Chart/ChartDomain.lean`,
importing `ChartDomain/Monomials.lean`, `ChartDomain/NormalForm.lean`, and a
new `ChartDomain/Symbol.lean` for steps 5–7. `hinj` is unused by anything
built so far (it is WP-13's output, supplied here only as a hypothesis) —
check whether the remaining steps need it before dropping it; if not, note
that in the final file's docstring rather than silently ignoring an unused
hypothesis (the `linter.unusedSectionVars`/`unusedVariables` lint will flag
it, `omit`/`_` it explicitly if genuinely unneeded). Also add
`tests/ChartDomainOracle.lean` restating the theorem for `C = MvPolynomial
(Fin 1) ℚ` over itself with `#print axioms` (mirror the pattern of other
`tests/*.lean` files in this repo, e.g. check `tests/` for an existing
`EtaleChartData`-style oracle to copy the shape from).

## What remains: steps 5–7

**Recommended strategy: the PLAN.md fallback (lexicographic leading term),
not the full binomial Leibniz rule.** The full multivariate Leibniz formula
(`partialMonomial α * multiplication c = Σ_{β ≤ α} (α.choose β) •
multiplication (partialMonomial (α − β) c) * partialMonomial β`) is
unnecessary complexity for this goal; PLAN.md §4 WP-14 explicitly names the
lex fallback as sufficient and easier. Only the *weak* one-step commutation
correction is needed:

```text
partialMonomial α * multiplication c
  = multiplication c * partialMonomial α + (a C-linear combination of
    partialMonomial β with β <_lex α, or with β.degree < α.degree)
```

### Step 5: coefficients, degree, symbol

Use `Module.Basis.span linearIndependent_partialMonomial : Module.Basis
(Fin n →₀ ℕ) C (Submodule.span C (Set.range partialMonomial))` (Mathlib,
`Mathlib/LinearAlgebra/Basis/Basic.lean`, `Basis.span`). Every `P ∈ algebra
k C` lands in this submodule (`mem_span_partialMonomial`), so define, for
`P ∈ algebra k C`, `coeffs P : (Fin n →₀ ℕ) →₀ C` as the `repr` of
`⟨P, mem_span_partialMonomial P hP⟩` under this basis (`Basis.repr` gives a
`LinearEquiv` to `(Fin n →₀ ℕ) →₀ C`; note the domain of `Basis.span` is the
*submodule*, so you will be repr-ing a subtype element — the natural
statement is `∃! coeffs, P = ∑ α ∈ coeffs.support, multiplication (coeffs
α) * partialMonomial α`, provable directly from `Basis.span` plus
`linearIndependent_partialMonomial` without necessarily naming a `coeffs`
function if that is more convenient downstream). Prove the reconstruction
identity `P = Finsupp.sum (coeffs P) (fun α c => multiplication c *
partialMonomial α)` or the `Finset.sum` form over `(coeffs P).support`
(watch the exact `Basis.span` API: its `repr` is w.r.t. the *inclusion*
`v : ι → span R (range v)`, i.e. `Basis.span_apply` or similar restates
`(Basis.span hli) i = ⟨v i, _⟩`; you will need to push the coefficients back
out to `Module.End k C` via the submodule's `Subtype.val`/coe, and note the
sum reconstructs `P` in `Module.End k C`, not `multiplication (coeffs P α) *
partialMonomial α` literally — check whether the natural basis pairing gives
you `c • partialMonomial α` (our `Module C (Module.End k C)` smul) rather
than `multiplication c * partialMonomial α`; these are equal by `ext x; simp
[multiplication_apply]`-style unfolding of the smul, matching what
`mem_span_partialMonomial`'s proof already uses (`heq` in
`NormalForm.lean`), but confirm the exact statement shape before committing
to one).

Define `deg P := (coeffs P).support.sup Finsupp.degree` (`0` if `P = 0`, or
just always define it this way; `Finset.sup` over `ℕ` of an empty set is
`0`, which conveniently matches `P = 0` needing no special case as long as
downstream lemmas only ever invoke `deg` on nonzero `P` or handle `0`
gracefully). Define `symbol P : MvPolynomial (Fin n) C := ∑ α ∈
(coeffs P).support.filter (fun α => Finsupp.degree α = deg P), MvPolynomial.monomial α (coeffs P α)`.

Prove `symbol P ≠ 0` when `P ≠ 0`: the filtered support is nonempty (`deg P`
is achieved by some element of the support, `Finset.exists_mem_eq_sup` or
similar), and `MvPolynomial.monomial` is injective on distinct exponents so
the sum's `coeff` at the maximizing `α` recovers `coeffs P α ≠ 0`
(`MvPolynomial.coeff_monomial` plus `Finset.sum_eq_single` reasoning to
isolate one term, mirroring the isolation argument already used in
`linearIndependent_partialMonomial`'s proof in `NormalForm.lean` — that
`Finset.add_sum_erase` / `Finset.sum_eq_zero` pattern generalizes directly).

### Step 6: the weak commutation-correction lemma

Prove, by `Finsupp.induction` on `α` (peeling off one `Finsupp.single i 1` at
a time via `α = Finsupp.single i 1 + α'` — Mathlib's `Finsupp.induction` has
the right shape: base case `α = 0` is `partialMonomial 0 = 1`, trivially
commutes with everything; inductive step needs `partialMonomial (single i 1
+ α') = partialMonomial (single i 1) * partialMonomial α'` from
`partialMonomial_add` and `partialMonomial_single`, then commute the *new*
outermost factor `(liftDerivation i).toLinearMap` past `multiplication c`
using the one-step fact below, THEN commute past `partialMonomial α'` using
the induction hypothesis, picking up two correction terms, each provably of
lower degree/lex order than `α`):

One-step fact (prove first, it is short — this is exactly `commutator`
unfolded via the derivation Leibniz rule, no induction needed):

```lean
theorem liftDerivation_commutator_multiplication (i : Fin n) (c : C) :
    commutator (liftDerivation (k := k) (C := C) i).toLinearMap c =
      multiplication ((liftDerivation (k := k) (C := C) i) c) := by
  ext x
  simp [commutator_apply, Derivation.leibniz, mul_comm]
```

(`Derivation.leibniz : D (a * b) = a • D b + b • D a`; check the exact
`simp` set needed, this is a two-line computation once the right lemmas are
in the `simp` call — do not skip proving this first in isolation, it is the
base case every later induction step reduces to.)

Then the target correction lemma, stated in whichever form (lex or plain
total-degree) turns out easier to push through the induction — **total
degree is likely the path of least resistance** since `Finsupp.degree` and
`degree_single`/`degree_add` are already in scope and used elsewhere in this
file, whereas `Finsupp.Lex` needs a fresh well-order setup:

```lean
theorem partialMonomial_mul_multiplication_sub_comm_mem_lt (α : Fin n →₀ ℕ) (c : C) :
    partialMonomial (k := k) (C := C) α * multiplication c -
        multiplication c * partialMonomial (k := k) (C := C) α ∈
      Submodule.span C
        ((partialMonomial (k := k) (C := C) : (Fin n →₀ ℕ) → Module.End k C) ''
          {β | Finsupp.degree β < Finsupp.degree α})
```

induction skeleton: at each `Finsupp.induction` step (`α = single i 1 + α'`,
`i ∉ α'.support` not actually needed — `Finsupp.induction` peels by support
membership but the algebra only needs `partialMonomial_add` which holds
unconditionally), expand

```text
∂_i·M(α')·mult(c) − mult(c)·∂_i·M(α')
  = ∂_i·(M(α')·mult(c) − mult(c)·M(α'))  +  (∂_i·mult(c) − mult(c)·∂_i)·M(α')
  = ∂_i · [correction ∈ span{deg < deg α'}]  +  mult(∂_i c) · M(α')
```

where `M(α') := partialMonomial α'`. The first term needs "`∂_i` composed on
the left with something in `span{deg < deg α'}` stays in `span{deg <
1+deg α'} = span{deg < deg α}`" — i.e. a lemma `∀ i, Q ∈ span
{partialMonomial β | β.degree ≤ r} → (liftDerivation i).toLinearMap * Q ∈
span {partialMonomial β | β.degree ≤ r + 1}`, provable by
`Submodule.span_induction` on the generic spanning set exactly as
`mem_span_partialMonomial`'s `hright` does it in `NormalForm.lean`, but
composing on the *left* this time (`(∂_i) * partialMonomial β =
partialMonomial (single i 1) * partialMonomial β = partialMonomial (single i
1 + β)` via `partialMonomial_add`/`partialMonomial_single`, and
`(single i 1 + β).degree = 1 + β.degree` via `Finsupp.degree_add` +
`Finsupp.degree_single`). The second term `mult(∂_i c) · M(α')` is already
directly of the target shape with exponent `α'` (degree `= deg α − 1 < deg
α`), no induction needed on it, just `Submodule.subset_span`.

This is genuinely the most delicate part of WP-14 and is exactly the piece
PLAN.md flagged ("escalate early if the Leibniz rule resists"). Budget it
real time; if *this* specific lemma resists two attempts, that is the
correct point for a *second* escalation file
(`docs/escalations/wp14-leibniz-correction.md`) with the precise stuck goal
state, rather than reopening this one.

### Step 7: symbol multiplicativity → `NoZeroDivisors`

Given step 6, for `P, Q ≠ 0` in `algebra k C` with `deg P = p`, `deg Q = q`:
expand `P * Q` using `coeffs P`/`coeffs Q` as finite sums of `multiplication
(coeffs P α) * partialMonomial α * multiplication (coeffs Q β) *
partialMonomial β`. Push each `partialMonomial α * multiplication (coeffs Q
β)` past to `multiplication (coeffs Q β) * partialMonomial α + (span{deg <
α.degree} correction)` via step 6. Collect: the degree-`(p+q)` part of `P *
Q`'s expansion in the `partialMonomial` basis receives contributions *only*
from pairs `(α, β)` with `α.degree = p`, `β.degree = q` (any other pair, or
any correction term, lands at total degree `< p + q`, because a correction
term from `partialMonomial α * multiplication c` has degree `< α.degree` in
the `α`-slot while the `β`-slot degree is unchanged, and `α.degree < p` or
`β.degree < q` for non-top pairs) — and for those top pairs, the exact
multiplication-vs-partialMonomial ordering does not create *further*
corrections beyond what step 6 already accounts for once you multiply out
`multiplication (coeffs Q β) * partialMonomial (α+β)` for each surviving
`(α, β)` and observe the coefficient of `partialMonomial (α+β)` at top
degree is `coeffs P α * coeffs Q β` summed over `α+β` fixed — this is
literally `MvPolynomial.coeff_mul` computed in `symbol P * symbol Q :
MvPolynomial (Fin n) C`. State the key intermediate lemma as: the
degree-`(p+q)` truncation of `coeffs (P*Q)` equals the coefficient function
of `symbol P * symbol Q` (as a polynomial in `MvPolynomial (Fin n) C`).
Since `MvPolynomial (Fin n) C` is a domain (`C` a domain ⇒
`MvPolynomial.instIsDomain`, already in Mathlib, should resolve
automatically once `[IsDomain C]` is in scope) and `symbol P, symbol Q ≠ 0`
(step 5), `symbol P * symbol Q ≠ 0`, so `symbol (P * Q) ≠ 0` (it is *equal*
to `symbol P * symbol Q` restricted/reindexed, not just related — get the
exact equality right, since `symbol` is defined as a sum over the *maximal*
degree slice, and the top slice of `coeffs (P*Q)` restricted to degree
`p+q` is exactly `symbol P * symbol Q`'s coefficients, but you additionally
need `deg (P*Q) = p + q` i.e. that nothing of degree `> p+q` appears in
`coeffs (P*Q)` — that direction is the "`deg(P*Q) ≤ deg P + deg Q`" half,
provable the same way, everything from the expansion lands at degree `≤
p+q`). Once `symbol (P*Q) ≠ 0`, conclude `coeffs (P*Q) ≠ 0` hence (by
`linearIndependent_partialMonomial`, or just directly: `coeffs (P*Q).support`
nonempty ⇒ `P*Q ≠ 0` since `coeffs 0 = 0`) `P * Q ≠ 0`.

Finally:

```lean
instance noZeroDivisors_algebra_of_etale : NoZeroDivisors (algebra (k := k) (R := C)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro P Q hPQ
    by_contra h
    push_neg at h
    exact (symbol multiplicativity contradiction) ...
```
(rephrase to match whatever the cleanest contrapositive shape turns out to
be — the algebra `Subalgebra k (Module.End k C)`'s multiplication is the
`Module.End k C` composition restricted to the subalgebra, i.e. proving
`P.val * Q.val ≠ 0` in `Module.End k C` for `P, Q : algebra k C` nonzero
suffices, then transport through `Subtype.ext_iff`/`Submonoid.coe_mul` as
`EtaleChartData.lean`'s other proofs already do repeatedly — grep this repo
for `Subalgebra.coe_mul` for the idiom).

## Why this was escalated rather than attempted further

Steps 1–4 (this session) already total ~425 lines of non-trivial
`Finset.noncommProd`/`Finsupp` manipulation, each requiring multiple
build-fix iterations for exactly the kind of `n`-metavariable and
dependent-rewrite pitfalls documented above. Steps 5–7 are of comparable or
greater size and novelty (a fresh induction argument, a fresh "top-degree
truncation" bookkeeping layer, and a final domain-transfer argument through
`MvPolynomial`), and PLAN.md itself already flags this specific composition
step as the one likely to need escalation. Rather than rush a large,
easy-to-get-subtly-wrong induction under time pressure and risk a stuck
`sorry` or a broken commit, the finished, `sorry`-free steps 1–4 are
committed and pushed, and this file hands off a concrete, checked-against-the-
actual-file-contents plan for 5–7 to whichever agent (Opus per the
escalation ladder) picks this up next.

## Resolution (Claude Opus, 2026-09-07)

**Status: resolved, no `sorry`.** Steps 5–7 are implemented in
`GlobalStafford/Chart/ChartDomain/Symbol.lean` and assembled in
`GlobalStafford/Chart/ChartDomain.lean`; `tests/ChartDomainOracle.lean` is the
consumer oracle. `#print axioms
GlobalStafford.Chart.noZeroDivisors_algebra_of_etale` reports
`[propext, Classical.choice, Quot.sound]`.

### Route taken

Neither the lexicographic order nor an explicit `coeffs`/`deg`/`symbol` triple
was needed. Two observations collapse the bookkeeping:

1. **The coefficient carrier is `MvPolynomial (Fin n) C` itself**, and its
   product *is* the leading-symbol product. Define once

   ```lean
   def opOf : MvPolynomial (Fin n) C →ₗ[C] Module.End k C :=
     (Finsupp.linearCombination C partialMonomial).comp
       (AddMonoidAlgebra.coeffLinearEquiv (R := C) (S := C)).toLinearMap
   ```

   (`MvPolynomial σ R` is an `abbrev` for the *structure*
   `AddMonoidAlgebra R (σ →₀ ℕ)` in this Mathlib, so the bridge
   `AddMonoidAlgebra.coeffLinearEquiv` is required; the two types are not
   defeq.) Because `LinearIndependent R v` is *by definition*
   `Function.Injective (Finsupp.linearCombination R v)`,
   `linearIndependent_partialMonomial` gives `opOf_injective` in three lines,
   and `mem_span_partialMonomial` plus
   `Finsupp.mem_span_range_iff_exists_finsupp` gives `exists_opOf`. No
   `Basis.span`, no `Basis.repr`, no named `coeffs` function.

2. **`Submodule.map opOf (degLt r)` replaces every "lower order terms"
   phrase**, where

   ```lean
   def degLt (r : ℕ) : Submodule C (MvPolynomial (Fin n) C) where
     carrier := {f | ∀ β ∈ f.support, β.degree < r}
   ```

   (support-based, not `totalDegree < r`, so that `0` is a member also for
   `r = 0`). Being a submodule, it absorbs the sums, the `C`-scalars and the
   negation that the argument produces, and injectivity of `opOf` transports
   membership back to the polynomial side for free.

Declarations, in dependency order (all in `namespace GlobalStafford.Chart`):

| name | statement |
| --- | --- |
| `smul_eq_multiplication_mul` | `c • P = multiplication c * P` in `Module.End k C` |
| `multiplication_mul_multiplication` | `multiplication (a*b) = multiplication a * multiplication b` |
| `smul_mul_assoc'` | `(c • P) * Q = c • (P * Q)` |
| `opOf`, `opOf_monomial`, `opOf_injective`, `exists_opOf` | the normal-form realization map |
| `degLt`, `mem_degLt_iff`, `degLt_mono`, `monomial_mem_degLt`, `mul_monomial_mem_degLt` | the degree filtration |
| `opOf_mul_partialMonomial` | `opOf f * ∂^β = opOf (f * X^β)` (right composition is exact) |
| `liftDerivation_mul_multiplication` | `∂_i * mult c = mult c * ∂_i + mult (∂_i c)` |
| `exists_pred_of_ne_zero` | `α ≠ 0 → ∃ i α', α = α' + single i 1 ∧ α'.degree + 1 = α.degree` |
| `partialMonomial_commutator_mem_aux`, `partialMonomial_commutator_mem` | **step 6**, the weak composition rule |
| `opOf_monomial_mul_sub_mem`, `opOf_sum_mul_sub_mem`, `opOf_mul_sub_mem` | **step 5/7**, the product formula |
| `opOf_mul_ne_zero` | **step 7**, symbol multiplicativity |
| `noZeroDivisors_algebra_of_etale` (`ChartDomain.lean`) | **the WP-14 deliverable** |

### The two points where the naive plan had to be changed

* **Peel the derivation on the *right*, not the left.** The escalation sketch
  wrote `partialMonomial (single i 1 + α') = ∂_i * M(α')` and then needed
  "`∂_i` composed on the left with something of lower degree stays of lower
  degree" — which is itself an instance of the commutation rule being proved,
  i.e. circular. Writing `α = α' + single i 1`, so
  `partialMonomial α = M(α') * ∂_i`, makes the correction terms appear under
  *right* multiplication by `∂_i`, and right multiplication is the exact,
  induction-free `opOf_mul_partialMonomial`. The induction is a plain
  `induction d` on a degree bound with `exists_pred_of_ne_zero` supplying the
  decomposition; the algebraic identity is

  ```text
  M(α')∂_i·mult c − mult c·M(α')∂_i
    = (M(α')·mult c − mult c·M(α'))·∂_i        -- IH for α', pushed right
    + (M(α')·mult(∂_i c) − mult(∂_i c)·M(α'))  -- IH for α' at the derived coefficient
    + mult(∂_i c)·M(α')                        -- a normal form of degree α'.degree
  ```

* **The top-degree slice never has to be constructed.** With the product
  formula `opOf f * opOf g − opOf (f*g) ∈ map opOf (degLt (p+q))`
  (`p := f.totalDegree`, `q := g.totalDegree`), assuming `opOf f * opOf g = 0`
  gives `f * g ∈ degLt (p+q)` by injectivity of `opOf`, while
  `MvPolynomial.totalDegree_mul_of_isDomain` (Mathlib,
  `Mathlib/Algebra/MvPolynomial/NoZeroDivisors.lean`) says
  `(f*g).totalDegree = p + q`, and `Finset.exists_mem_eq_sup` exhibits a
  support element attaining it. Contradiction. So neither a `symbol` function
  nor `homogeneousComponent` is needed anywhere.

### Lean notes for whoever touches this next

* `noncomm_ring` normalizes `-1 • (x * y) * z` and `-1 • (x * (y * z))` to
  different atoms and stalls; `simp only [sub_mul, mul_add, mul_assoc]` followed
  by `abel` closes those goals. Also: never `set A := …` before such a call,
  because the let-bound local becomes an atom distinct from its body.
* The `n`-metavariable pitfall documented above recurs at
  `Finsupp.mem_span_range_iff_exists_finsupp`; it is fixed by giving `v`
  explicitly with a type ascription.
* `hinj` (the WP-13 injectivity of `algebraMap B C`) is **not used**. The
  linear independence of `partialMonomial` only ever evaluates operators on
  images of polynomial monomials and needs `algebraMap k C` injective, which is
  automatic for a field. The hypothesis is kept because `PLAN.md` specifies the
  signature; `set_option linter.unusedVariables false in` precedes the theorem
  and the file docstring records why.

### Left for the controller

`GlobalStafford.lean` is on this session's do-not-edit list, so the line
`import GlobalStafford.Chart.ChartDomain` (which the root-module convention of
`PLAN.md` asks for) has **not** been added; nor has the WP-14 row of
`PLAN.md` Section 9 been moved to `done`. Both are one-line changes for the
merge commit.
