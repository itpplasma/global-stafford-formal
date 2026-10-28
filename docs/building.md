# Building and verification

## Pins

| Component | Revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| [AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) | `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8` |
| [stafford38-formal](https://github.com/itpplasma/stafford38-formal) | `e77e176c381ca2d6b20c030f9227f1b031415d2e` |

These are set in `lean-toolchain` and `lakefile.toml` and resolved in
`lake-manifest.json`. Lake fetches the two project dependencies into
`.lake/packages/algebraicAnalysis` and `.lake/packages/stafford38Formal`;
separate sibling clones are not needed. Do not run `lake update` as routine
setup. An older stafford38-formal revision
(`784b59925beb9a480519142336bd6434f6eeef16`) appears in dated research
records only; it is not the dependency used by the build.

## Build and verify

```sh
lake exe cache get
lake build                 # GlobalStafford, GlobalStaffordSolution
scripts/verify.sh          # full check
scripts/verify.sh --phase-i
```

The full mode builds the library, checks pins, audits the sources (no
`sorry` outside the challenge files, no axiom declarations), prints and
checks the axioms of the endpoints in `docs/endpoints.txt`, and checks the
import closures of the challenge and solution files. `--phase-i` uses the
intermediate endpoint list `docs/phase-i-endpoints.txt`. Both modes write
logs to `.lake/verification/`, so run them one after the other.

## Making a correction

For a correction to the paper, identify the mapped Lean declarations in
[paper-lean-specification.md](paper-lean-specification.md) and their
downstream consumers, make the smallest change, and rerun
`scripts/verify.sh`. A changed proof needs a fresh independent replay before
the recorded verification applies to it.

Some lemmas proved here could move upstream to AlgebraicAnalysis. That
requires axiom-clean library proofs, rewiring here, and a compatibility build
of the stafford38-formal endpoints at the shared pins.

## TeX dossier

`docs/dossier/build.sh` builds `docs/dossier/global-stafford-dossier.pdf`
and its source-hash manifest. It needs LuaLaTeX, latexmk, TikZ and the DejaVu
fonts.
