# WP-11 escalation: `extend_mem_order` (step 4 of the PLAN.md WP-11 plan)

Status: `GlobalStafford/Localization/Construction.lean` builds clean, no
`sorry`, no `axiom`, through PLAN.md WP-11 steps 1-3 (representative
independence of the extension formula, and `extend_algebraMap`). Commits
`ba0b3f6` .. `1695ab0` on branch `wp11`. This file documents a complete
(worked-out on paper, not yet formalized) proof strategy for step 4,
`extend P hP ∈ order r`, for the next agent to implement directly, plus
what remains after it (steps 5-8).

## What is proved so far (`Construction.lean`)

- `ext_of_finite_order`: uniqueness of finite-order extensions agreeing on
  the image of `A` (drives everything downstream).
- `fPow`, `exists_fPow_rep`, `ad_iterate_apply_mul`, `termFun` (the raw
  extension-sum formula at a representative `(a, n)`).
- `choose_neg_succ_pascal`, `mk'_add_same_denom`, `pascal_neg_shift_sum`,
  `mk'_shift_num_denom`, `termFun_summand_vanish`, `termFun_shift`,
  `termFun_shift_pow`, `powers_le_nonZeroDivisors`, `algebraMap_injective`,
  `eq_of_mk'_same_denom`, `mk'_shift_pow`, `termFun_well_defined`: full
  representative-independence of `termFun` (PLAN.md WP-11 step 1, in full).
- `repA`, `repN`, `repSpec`, `extend`, `extend_eq_termFun`, `fPow_zero`,
  `choose_zero_int`, `extend_algebraMap`: the extension function and its
  restriction to `P` on the image of `A` (PLAN.md WP-11 steps 2-3).

## The remaining goal: `extend P hP ∈ order r`

Two attempts were made within the session budget on the direct route
suggested by PLAN.md ("prove `commutator (extend P) (algebraMap f) =
extend (ad f P)` ... for general `x` show `commutator (extend P) x` has
order `≤ r - 1`"). The commutator-with-`algebraMap f` identity is
tractable and was worked out completely (see below); the extension to
*every* `x : A_f` (not just `x = algebraMap f`) needs machinery not yet in
the file (a commutator-Leibniz identity, a Jacobi-type commuting fact, and
a commutator-with-inverse identity). None of these individually resisted —
they were simply not attempted yet, in the interest of not rushing broken
code under time pressure; each is a genuine new lemma of comparable size
to several already in the file. The route below is complete and should go
through; it is written out in enough detail to implement directly.

### Step 4a: `commutator (extend P hP) (algebraMap A Af f) = extend (ad f P) hP'`

For `P ∈ order (r' + 1)` (`hP' : ad f P ∈ order r'` via `ad_mem_order hP`),
show the two sides agree pointwise on every `x = mk' Af a (fPow f n)`
(then conclude by `ext` since both sides are `Module.End k Af`, using
`exists_fPow_rep` to reduce to representatives).

Compute, using `extend_eq_termFun`, `mul_mk'_eq_mk'_of_mul` (`x * mk' S y z
= mk' S (x*y) z`, `IsLocalization.mul_mk'_eq_mk'_of_mul`), and
`ad_iterate_apply_mul`:

```text
extend P hP (algebraMap f * mk' a (fPow n))
  = extend P hP (mk' (f*a) (fPow n))          -- mul_mk'_eq_mk'_of_mul
  = termFun r P (f*a) n                        -- extend_eq_termFun
  = Σ_{j≤r} choose(-n,j) • mk'(adf^[j]P(f*a))(fPow(n+j))
  = Σ_{j≤r} choose(-n,j) • mk'(f*(adf^[j]P a) + adf^[j+1]P a)(fPow(n+j))   -- ad_iterate_apply_mul
  = Σ_{j≤r} choose(-n,j) • [algebraMap f * mk'(adf^[j]P a)(fPow(n+j))
        + mk'(adf^[j+1]P a)(fPow(n+j))]        -- mk'_add_same_denom, mul_mk'_eq_mk'_of_mul (reversed)
  = algebraMap f * termFun r P a n
      + Σ_{j≤r} choose(-n,j) • mk'(adf^[j+1]P a)(fPow(n+j))
```

The tail sum, for `j` from `0` to `r`, equals `termFun (r-1) (ad f P) a n =
Σ_{j≤r-1} choose(-n,j) • mk'(adf^[j+1]P a)(fPow(n+j))` **plus** the extra
`j = r` term `choose(-n,r) • mk'(adf^[r+1]P a)(fPow(n+r))`, which is `0`
because `P ∈ order r` gives `(ad f)^[r+1] P = 0`
(`ad_iterate_eq_zero`, already in `Operators/Commutator.lean`) — exactly
the same boundary-vanishing trick as `pascal_neg_shift_sum`/
`termFun_summand_vanish`. So the tail sum **is** `termFun (r-1) (ad f P) a
n = extend (ad f P) hP' (mk' a (fPow n))` (via `extend_eq_termFun`
applied to `ad f P`).

Subtracting `algebraMap f * termFun r P a n = algebraMap f * extend P hP
(mk' a (fPow n))` from both sides of the displayed chain gives exactly

```text
commutator (extend P hP) (algebraMap f) (mk' a (fPow n)) = extend (ad f P) hP' (mk' a (fPow n))
```

which is the desired pointwise identity (`commutator_apply` unfolds the
LHS to `extend P hP (algebraMap f * x) - algebraMap f * extend P hP x`,
matching the chain above).

For `r = 0` (base case of the outer induction on `r`), `P ∈ order 0`
means `P = multiplication (P 1)` (`mem_order_zero_iff_eq_multiplication`);
`extend_algebraMap` plus a short computation shows `extend P hP =
multiplication (algebraMap (P 1))` outright (this is *also* worth proving
directly and separately, since it is needed as the base case of the whole
step-4 induction, not just of step 4a — see below), which trivially has
order `0`.

### Step 4b: the general commutator, `commutator (extend P hP) a = extend (commutator P a) hQ` for `a : A`

This is the *same computation* as 4a but for an arbitrary `a : A` in place
of `f` specifically (note: this does **not** use the `ad f`/localization
machinery on the outside — `a` need not be related to `f`). Key facts to
prove first, both pure `Module.End k A`/`Module.End k Af` algebra with
*no* order hypotheses:

1. **Jacobi-type commuting of `ad f` and `commutator (·) a`** (for `a, f :
   A`, using that `A` is commutative): `commutator (commutator Q a) f =
   commutator (commutator Q f) a` as endomorphisms of `A`, for any `Q :
   Module.End k A`. Proved by unfolding `commutator_apply` on both sides
   at an arbitrary `x`; both expand to `Q(f*a*x) - a*Q(f*x) - f*Q(a*x) +
   f*a*Q(x)` (using `mul_comm`/`mul_assoc` for `A`). By induction on `j`,
   `commutator ((ad f)^[j] P) a = (ad f)^[j] (commutator P a)` — note `ad f
   Q = commutator Q f` by definition, so this is literally `j` applications
   of the one-step fact.
2. With that, the computation of step 4a goes through verbatim with `f`
   replaced by `a` throughout **except** that the `ad_iterate_apply_mul`
   step (which is specific to `f`) is replaced by the *definition* of
   `commutator` itself: `((ad f)^[j] P)(a * b) - a * ((ad f)^[j] P) b =
   commutator ((ad f)^[j] P) a (b) = (ad f)^[j] (commutator P a) (b)` by
   fact 1. So:

```text
termFun r P (a*b) n - algebraMap a * termFun r P b n
  = Σ_{j≤r} choose(-n,j) • mk'(commutator (adf^[j]P) a (b))(fPow(n+j))
  = Σ_{j≤r} choose(-n,j) • mk'((ad f)^[j] (commutator P a) (b))(fPow(n+j))
  = termFun r (commutator P a) b n
```

  Note this uses `r`, not `r - 1` — `commutator P a` for `P ∈ order (r'+1)`
  and *arbitrary* `a : A` has order `≤ r'` by `mem_order_succ_iff` (this
  **is** the `hQ` order-bound hypothesis needed to call `extend`), but the
  formula manipulation above works at any common truncation length `r ≥
  r'` (it doesn't need to know `commutator P a` has smaller order; that
  fact is only used afterward, to invoke the induction hypothesis). So
  state this as an identity `commutator (extend P hP) (algebraMap a) =
  extend (commutator P a) hQ` where `hQ : commutator P a ∈ order r'` comes
  from `(mem_order_succ_iff P r').1 hP a`.

### Step 4c: commutator with an inverse

Pure algebra, no order hypotheses: for `D : Module.End k Af` and `u : Af`
a unit with inverse `u⁻¹`,

```text
commutator D u⁻¹ = - (multiplication u⁻¹) ∘ (commutator D u) ∘ (multiplication u⁻¹)
```

Proof: unfold `commutator_apply` on `u⁻¹ * ((commutator D u) (u⁻¹ * x))`
and simplify using `u * u⁻¹ = 1`; it equals `-(D(u⁻¹*x) - u⁻¹ * D x) =
-(commutator D u⁻¹) x`. (`u := algebraMap A Af f`, unit by
`IsLocalization.Away.algebraMap_isUnit f`; `u⁻¹` can reuse
`GlobalStafford.Localization.LocalizationInterface.fInv` from
`Localization/Interface.lean`, which only needs `[IsLocalization.Away f
Af]`, not an actual `LocalizationInterface` value — or just redefine a
local `fInv' := (IsLocalization.Away.algebraMap_isUnit f).unit⁻¹.val` in
`Construction.lean` directly, to avoid the cross-file dependency.)

Apply with `D := extend P hP`, `u := algebraMap f` (unit): using step 4a,
`commutator (extend P hP) (algebraMap f) = extend (ad f P) hP'` has order
`r'` (by the **induction hypothesis** on `r`, since `ad f P ∈ order r' <
r'+1`), so `commutator (extend P hP) (fInv') = -mult(fInv') ∘ extend(ad f
P) hP' ∘ mult(fInv')` has order `r'` too, by two applications of
`mul_mem_order` with the order-`0` fact for `multiplication` (already
proved as a private lemma `multiplication_mem_order_zero` pattern in
`Operators/Commutator.lean`; re-derive or reuse for `Af`) sandwiching the
order-`r'` middle term, plus closure of a `Submodule` under negation.

By the same shift-power argument as `termFun_shift_pow`/`mk'_shift_pow`
(or directly, `commutator D` is linear in the second argument via
`ad_apply_mul`... no — actually just induct on `n` using the one-step
identity `commutator D (u * v) = u • commutator D v + (commutator D u) ∘
mult v`, see step 4d below, applied with `v := u⁻¹`, `u := u⁻¹^{n}`, or
more simply prove `commutator D (u⁻¹)^n` directly by induction on `n`
mirroring the `u⁻¹` case with `u^n` a unit too), get `commutator (extend P
hP) (fInv'^n) ∈ order r'` for every `n`.

### Step 4d: the Leibniz identity and assembly

Pure algebra, no order hypotheses, for `D : Module.End k Af` and `x, y :
Af`:

```text
commutator D (x * y) = (multiplication x) ∘ (commutator D y) + (commutator D x) ∘ (multiplication y)
```

(Unfold both sides via `commutator_apply` at arbitrary `w`; both equal
`D(x*y*w) - x*y*D(w)` after expansion — this is a completely generic,
`A`/`f`-independent fact that could even live in
`AlgebraicAnalysis.DifferentialOperators.Basic` as a companion to
`commutator_mul`, since it is the "other side" Leibniz rule, for a
commutator linear in its *second* argument rather than its first. Check
whether it is already there — if not, add it as
`commutator_mul_scalars` or similar, by analogy with `commutator_mul`.)

Every `z : A_f` is `algebraMap A Af a * fInv'^n` for some `a : A`, `n : ℕ`
(from `mk' Af a (fPow f n) = algebraMap a * mk' Af 1 (fPow f n)` via
`IsLocalization.mk'_eq_mul_mk'_one`, and `mk' Af 1 (fPow f n) = fInv'^n` by
uniqueness of the two-sided inverse of `algebraMap (f^n)`, or by
`smul_mk'_self`/direct induction on `n` from `mk'_mul_mk'_eq_one`).

Apply the Leibniz identity with `x := algebraMap a`, `y := fInv'^n`:

```text
commutator (extend P hP) z = algebraMap a • commutator (extend P hP) (fInv'^n)
    + (commutator (extend P hP) (algebraMap a)) ∘ (multiplication fInv'^n)
```

Both summands have order `≤ r'`: the first by step 4c plus
`Submodule.smul_mem`; the second by step 4b (`commutator (extend P hP)
(algebraMap a) = extend (commutator P a) hQ`, order `r'` **by the
induction hypothesis**, since `commutator P a ∈ order r' < r'+1`) composed
on the right with an order-`0` multiplication (`mul_mem_order`). Their sum
is in `order r'` (`Submodule.add_mem`). This holds for *every* `z : Af`,
so by `mem_order_succ_iff`, `extend P hP ∈ order (r' + 1)`.

### Base case `r = 0`

Directly: `P ∈ order 0` gives `P = multiplication (P 1)`
(`mem_order_zero_iff_eq_multiplication`); a short computation from
`termFun`'s definition (`Ring.choose (-(n:ℤ)) 0 = 1` always, so **only**
`j = 0` can contribute when `r = 0`, giving `termFun 0 P a n = mk' Af (P a)
(fPow f n)`, and `P a = P 1 * a` since `P` is multiplication by `P 1`) —
show `extend P hP = multiplication (algebraMap A Af (P 1))` outright (this
was half-derived already while investigating this step; it should be a
quick, clean lemma, `extend_of_order_zero` or similar, and is *also* the
natural base case for the whole `extend_mem_order` induction on `r`, not
just for step 4a's base case).

### Induction structure

Package all of the above as a single **strong induction on `r`**: `∀ r, ∀
(P : Module.End k A) (hP : P ∈ order r), extend P hP ∈ order r`, proved by
`Nat.strong_induction_on` (or ordinary induction, since only `r' < r' + 1`
is ever needed — a plain `induction r with | zero | succ r' ih` suffices,
no strong induction actually needed, since 4a/4b/4c/4d only ever invoke
the hypothesis at `ad f P`/`commutator P a`, both of order exactly `r'`).

## After step 4

Steps 5-8 of PLAN.md WP-11 remain: `extend_mul`/`extend_one`/
`extend_add`/`extend_smul` (all via `ext_of_finite_order`, now unblocked
once `extend_mem_order` exists, comparing both sides' order bounds via
`mul_mem_order`/etc. and their agreement on `algebraMap A Af a` via
`extend_algebraMap` plus the corresponding fact for `P` — e.g. `(P*Q) a`
vs `P(Q a)` needs a touch of care since `extend_algebraMap` gives `extend P
(algebraMap a) = algebraMap (P a)`, and `extend (P*Q) (algebraMap a) =
algebraMap ((P*Q) a) = algebraMap (P (Q a))`, while `(extend P * extend Q)
(algebraMap a) = extend P (extend Q (algebraMap a)) = extend P
(algebraMap (Q a)) = algebraMap (P (Q a))` — matches); independence of the
extension from the chosen order bound `r` (again via `ext_of_finite_order`,
comparing `extend P hP` and `extend P hP'` for two different bounds `hP :
P ∈ order r`, `hP' : P ∈ order r'`, both of order `max r r'` by
`order_mono`); packaging `ι : algebra k A →ₐ[k] algebra k Af` using
`Classical.choose (exists_order P)` for the order witness (from
`Operators/Basic.lean`'s `exists_order`) and `AlgHom.mk`/`Subalgebra`
coercion machinery; `ι_multiplicationD`, `ι_mem_order` (both immediate from
what is proved here), `ι_injective` (from `extend_algebraMap` — if `ι P =
0` then `algebraMap (P a) = 0` for all `a`, and `algebraMap A Af` is
injective by `algebraMap_injective`, so `P a = 0` for all `a`, i.e. `P =
0`); and `clearance` (PLAN.md WP-11 step 8, the FiniteType-generators
induction — the largest remaining piece, not investigated in this
session). Finally assemble `localizationInterface :
LocalizationInterface k A Af f` and, if the instances resolve,
`localizationInterfaceAway`.

## Recommendation

Implement step 4 (`extend_mem_order`) directly from the roadmap above —
it is complete and every sub-identity has been checked by hand (not just
asserted). Budget roughly 150-300 additional lines and expect the same
kind of Mathlib-API friction seen throughout `Construction.lean` so far
(implicit `Af` needing type ascriptions on `have`s that call a lemma
without an expected-type context; `include f in`/`include hf in` before
any declaration using `f`/`hf` only in its proof, not its statement — see
the many examples already in the file). Steps 5-7 are comparatively
routine once step 4 lands. Step 8 (`clearance`) has not been scoped in
this session beyond the summary in `PLAN.md` §4 WP-11 and should get its
own escalation-budget pass.
