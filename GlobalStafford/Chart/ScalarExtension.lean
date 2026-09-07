import GlobalStafford.Chart.PolynomialS38
import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity

/-!
# Scalar extension interface (Lemma 6.2 over `k(t)`)

`PLAN.md` WP-9 (Section 3, "WP-9 Scalar extension interface"; paper Section 6, the
scalar extension `D_k(C)[t] → D_K(C_K)`). `ScalarExtensionInterface` packages the
data needed to transport `TwoGeneratorIdentity` on a scalar extension `DK` of a
`k`-algebra `D` back to `S38_poly D`: a ring homomorphism `Θ : Polynomial D →+*
DK` sending the "scalar" polynomials `scalarPoly h` (`h : Polynomial k`) to the
central elements `algebraMap K DK (aeval t h)` of `DK`, injective, and spanning
`DK` up to a nonzero scalar denominator. `s38Poly_of_scalarExtension` is the
transport theorem: `TwoGeneratorIdentity DK` implies `S38Poly k D`.
-/

namespace GlobalStafford.Chart

open Polynomial GlobalStafford.Conjugation AlgebraicAnalysis

variable {k : Type*} [Field k] [CharZero k]
variable (D : Type*) [Ring D] [Algebra k D]
variable (K : Type*) [Field K] [Algebra k K]
variable (DK : Type*) [Ring DK] [Algebra K DK] [Algebra k DK] [IsScalarTower k K DK]
variable (t : K)

/-- The data needed to transport `TwoGeneratorIdentity DK` to `S38Poly k D`, for a
"scalar extension at `t`" `DK` of `D` (paper Section 6): a ring homomorphism
`Θ : Polynomial D →+* DK` that sends scalar polynomials `scalarPoly h`, `h :
Polynomial k`, to the central elements `algebraMap K DK (aeval t h)` of `DK`
(`Θ_scalar`), is injective (`Θ_injective`), and whose image spans `DK` up to a
nonzero scalar denominator (`spanning`); `aeval_ne_zero` records that `t` is
transcendental over `k`, i.e. `aeval t h ≠ 0` for `h ≠ 0`. -/
structure ScalarExtensionInterface where
  /-- The scalar-extension ring homomorphism `Polynomial D →+* DK`. -/
  Θ : Polynomial D →+* DK
  /-- `Θ` sends scalar polynomials `scalarPoly h` to `algebraMap K DK (aeval t h)`. -/
  Θ_scalar : ∀ h : Polynomial k,
      Θ (GlobalStafford.Conjugation.scalarPoly h) = algebraMap K DK (Polynomial.aeval t h)
  /-- `Θ` is injective. -/
  Θ_injective : Function.Injective Θ
  /-- The image of `Θ` spans `DK` up to a nonzero scalar denominator. -/
  spanning : ∀ Q : DK, ∃ h : Polynomial k, h ≠ 0 ∧ ∃ P : Polynomial D,
      algebraMap K DK (Polynomial.aeval t h) * Q = Θ P
  /-- `t` is transcendental over `k`: `aeval t h ≠ 0` for every nonzero `h : Polynomial k`. -/
  aeval_ne_zero : ∀ h : Polynomial k, h ≠ 0 → Polynomial.aeval t h ≠ 0

namespace ScalarExtensionInterface

variable {D K DK t}

omit [CharZero k] [Algebra k DK] [IsScalarTower k K DK] in
/-- The scalar `algebraMap K DK (aeval t h)` is central in `DK`: it commutes with every
`z : DK`. `DK` is a `K`-algebra, so this is `Algebra.commutes`. -/
theorem central (h : Polynomial k) (z : DK) :
    algebraMap K DK (Polynomial.aeval t h) * z = z * algebraMap K DK (Polynomial.aeval t h) :=
  Algebra.commutes (Polynomial.aeval t h) z

omit [CharZero k] [Algebra k DK] [IsScalarTower k K DK] in
/-- A central element can be pulled out of the right factor of a product to the front:
`x * (a * y) = a * (x * y)` when `a = algebraMap K DK (aeval t h)`. The main rearrangement
step used to collect the central scalars `algebraMap K DK (aeval t h_u)`, `..h_w`, `..h_v`
in `s38Poly_of_scalarExtension`. -/
theorem pull_left (h : Polynomial k) (x y : DK) :
    x * (algebraMap K DK (Polynomial.aeval t h) * y) = algebraMap K DK (Polynomial.aeval t h) * (x * y) := by
  rw [← mul_assoc, ← central h x, mul_assoc]

end ScalarExtensionInterface

open ScalarExtensionInterface in
omit [CharZero k] [Algebra k DK] [IsScalarTower k K DK] in
/-- **Lemma 6.2 over `k(t)`** (`PLAN.md` WP-9, paper Section 6): a scalar extension
`DK` of `D` (packaged by `ScalarExtensionInterface`) transports `TwoGeneratorIdentity`
on `DK` to `S38_poly` on `D`.

For `E ≠ 0` in `Polynomial D`, injectivity of `Θ` gives `Θ E ≠ 0`, so
`TwoGeneratorIdentity DK` produces `1 = Θ E * u + w * Θ E * v`. `spanning` applied to
`u`, `w`, `v` gives nonzero `h_u, h_w, h_v : Polynomial k` and `u', w', v' :
Polynomial D` with `algebraMap K DK (aeval t h_u) * u = Θ u'`, similarly for `w, v`.
The scalars `algebraMap K DK (aeval t h)` are central in `DK`, so multiplying the
certificate through by `algebraMap K DK (aeval t (h_u * h_w * h_v))` and regrouping
gives `Θ (scalarPoly (h_u * h_w * h_v)) = Θ (E * (u' * scalarPoly (h_w * h_v)) + w' *
E * (v' * scalarPoly h_u))`; `Θ_injective` yields the `S38_poly` certificate for `E`
with `h := h_u * h_w * h_v`, `u := u' * scalarPoly (h_w * h_v)`, `w := w'`,
`v := v' * scalarPoly h_u`. -/
theorem s38Poly_of_scalarExtension (I : ScalarExtensionInterface (k := k) D K DK t)
    (hK : TwoGeneratorIdentity DK) : S38Poly k D := by
  intro E hE
  have hΘE : I.Θ E ≠ 0 := fun h0 => hE (I.Θ_injective (by rw [h0, map_zero]))
  obtain ⟨w, u, v, hcert⟩ := hK (I.Θ E) hΘE
  obtain ⟨h_u, hhu, u', hu'⟩ := I.spanning u
  obtain ⟨h_w, hhw, w', hw'⟩ := I.spanning w
  obtain ⟨h_v, hhv, v', hv'⟩ := I.spanning v
  refine ⟨h_u * h_w * h_v, mul_ne_zero (mul_ne_zero hhu hhw) hhv,
    u' * scalarPoly (h_w * h_v), w', v' * scalarPoly h_u, ?_⟩
  apply I.Θ_injective
  simp only [map_add, map_mul, I.Θ_scalar]
  rw [← hu', ← hw', ← hv']
  simp only [mul_assoc] at hcert ⊢
  -- Term A: I.Θ E * (a * (u * (b * c))) ⤳ a * (b * (c * (I.Θ E * u)))
  rw [pull_left h_u (I.Θ E) (u * (algebraMap K DK (Polynomial.aeval t h_w) *
        algebraMap K DK (Polynomial.aeval t h_v))),
    pull_left h_w u (algebraMap K DK (Polynomial.aeval t h_v)),
    pull_left h_w (I.Θ E) (u * algebraMap K DK (Polynomial.aeval t h_v)),
    ← central h_v u, pull_left h_v (I.Θ E) u]
  -- Term B: b * (w * (I.Θ E * (c * (v * a)))) ⤳ a * (b * (c * (w * (I.Θ E * v))))
  rw [← central h_u v, pull_left h_u (algebraMap K DK (Polynomial.aeval t h_v)) v,
    pull_left h_u (I.Θ E) (algebraMap K DK (Polynomial.aeval t h_v) * v),
    pull_left h_u w (I.Θ E * (algebraMap K DK (Polynomial.aeval t h_v) * v)),
    pull_left h_u (algebraMap K DK (Polynomial.aeval t h_w))
      (w * (I.Θ E * (algebraMap K DK (Polynomial.aeval t h_v) * v))),
    pull_left h_v (I.Θ E) v, pull_left h_v w (I.Θ E * v)]
  rw [← mul_add, ← mul_add, ← mul_add, ← hcert, mul_one]

#print axioms s38Poly_of_scalarExtension

end GlobalStafford.Chart
