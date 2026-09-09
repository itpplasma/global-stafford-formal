# Verification

Source `b21883a5b3d8f46922713049c3b060523ea3a771` passed Phase I and full verification in an isolated public clone, including 15 Phase I endpoint reports, both terminal endpoint reports, consumers, import audits and source resolution. Comparator accepted the solution with both NanoDa and Lean's kernel. The report SHA-256 is `08b8dcd152806c5033316100a624d8c61a67f9e069c18ac649f3c6612779db67`.

A separate check used Palomar's canonical Challenge compiler, protected alias and search path, Landrun adapter and Comparator. It also passed both kernels. The local host lacks a usable systemd manager, so this second check omitted the outer systemd wrapper while retaining Landrun and the mathematical checks. The external registry record is listed below; this local replay description should not be conflated with the registry's own mechanical/editorial status.

The module-name collision and its reproduced paths are recorded in `verification/module-resolution-b21883a.json`. The frozen legacy Challenge and Solution are retained; the uniquely named submission files preserve their bytes. The source-resolution gate fails before proof checking if Lake selects dependency files. The historical d76051ce report remains under `verification/history/`.

## Logical scope

`GlobalStafford.universalStatement` proves, for every characteristic-zero
field `k` and every smooth integral finitely generated `k`-algebra `A`
(`Algebra.Smooth k A`, `IsDomain A`), that every nonzero element `d` of the
intrinsic algebra of finite-order `k`-linear differential operators on `A`
admits `F, R, S` with `1 = d * R + F * d * S`. `GlobalStaffordSolution.lean` transports it
to `GlobalStaffordChallenge.universalStatement`, the Mathlib-only statement
of `Challenge.lean`, whose differential operators are defined by
Grothendieck's inductive commutator condition without forming a subalgebra.
Both endpoints depend only on `propext`, `Classical.choice`, and
`Quot.sound`; there are no project or literature axioms, no proof
placeholders outside the deliberate placeholder in each byte-identical Challenge template, and no
`Lean.ofReduceBool` dependency. The statement correspondence with the paper
proof is in [paper-lean-specification.md](paper-lean-specification.md).

The upstream Weyl-algebra theorem is imported from the public
`stafford38-formal` repository at the exact consumed pin below and is rebuilt
from source in the replay; its own verification record is that repository's.
The older revision `784b59925beb9a480519142336bd6434f6eeef16` is a
historical inspection pin from the informal proof development, not the pin of
the reviewed build. See
[provenance-literature-novelty.md](provenance-literature-novelty.md).

## Reproduction

From the snapshot commit with Elan and the build tools (Rust `cargo`, Go)
installed:

```sh
lake exe cache get
lake build
scripts/verify.sh
scripts/bootstrap-palomar-tools.sh
scripts/verify-palomar.sh
```

| Component | Exact consumed pin |
| --- | --- |
| Project Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| AlgebraicAnalysis | `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8` |
| Stafford38 formal | `e77e176c381ca2d6b20c030f9227f1b031415d2e` |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` (Lean `4.34.0-rc1`) |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

These values agree with `lake-manifest.json` and the machine-readable
`docs/verification-results.json` for the reviewed source. Historical reports
under `docs/verification/history/` retain their historical pins and are not
current reproduction instructions.

`scripts/verify.sh` resolves every source import, checks the pins, builds
every `GlobalStafford` module and the imported Stafford38 endpoints against
the shared AlgebraicAnalysis pin, audits the sources (one `sorry`, in
`Challenge.lean`; no `axiom`, `native_decide`, or `Lean.ofReduceBool`),
prints the axioms of the endpoints in `docs/endpoints.txt` under
`--trust=0`, builds `Challenge` and `Solution`, audits their loaded
environments (`scripts/check-import-closure.sh`: the Challenge closure is
Lean core and Mathlib's dependency closure only, excluding AlgebraicAnalysis
and Stafford38; the Solution excludes Challenge), and runs the literal
consumers in `tests/` under `--trust=0`. `scripts/verify-palomar.sh` pins
the tool revisions, exports and compares
`GlobalStaffordChallenge.universalStatement` with Comparator, and submits
the exported proof to NanoDa and to Lean's default kernel inside Landrun's
sandbox through the adapted wrapper.

## Tests and oracles

The `tests/` directory holds one literal consumer per work package (Phase I
and Phase II), each ending in `#print axioms`, and finite computations on
`Polynomial ℚ` and `MvPolynomial (Fin 1) ℚ` that exercise the definitions
independently of the general theorems (binomial formulas, the extension of
the derivative to `ℚ[X]_X`, chart data on the polynomial ring).

## Palomar record

- entry ID: `PALOMAR-2026-09-05-000007`
- version: `2`
- <https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2>

## Review scope

Mechanical proof verification does not certify novelty or historical priority.
A broad literature audit is now documented in
[provenance-literature-novelty.md](provenance-literature-novelty.md). It found
no prior proof of the exact theorem and strong evidence of novelty, including
a 2026 expert survey that still records a weaker adjacent `D(X)` generation
problem as open. Absolute priority, journal acceptance, and independent human
expert review remain separate and are not claimed by the machine report.
