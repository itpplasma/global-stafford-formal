# Verification

No verification snapshot exists yet. This document is completed by WP-19
(`PLAN.md`) after Phase II closes.

## Planned logical scope

The endpoint `GlobalStafford.universalStatement` and the Palomar solution
`GlobalStaffordChallenge.universalStatement` (via `Solution.lean`) must
depend only on `propext`, `Classical.choice`, and `Quot.sound`. The
endpoint list audited by `scripts/verify.sh` is `docs/endpoints.txt`; the
Phase I list (conditional theorems) is `docs/phase-i-endpoints.txt`.

## Planned reproduction

```sh
lake exe cache get
lake build
scripts/verify.sh
scripts/bootstrap-palomar-tools.sh
scripts/verify-palomar.sh
```

| Component | Pin |
| --- | --- |
| Project Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| AlgebraicAnalysis | `dfdd2da091a9d67e7a29cc7914f192d746a2400d` |
| Stafford38 formal | `784b59925beb9a480519142336bd6434f6eeef16` |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` (Lean `4.34.0-rc1`) |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The Challenge permits Lean core and the Mathlib dependency closure only;
`scripts/check-import-closure.sh` audits the loaded environment and
excludes `AlgebraicAnalysis` and `Stafford38` from the Challenge, and
`Challenge` from the Solution.
