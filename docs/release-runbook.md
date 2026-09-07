# Human release runbook

These are instructions for later human-authorized actions. Nothing here
grants authorization to change visibility, publish tags or deposits,
register with Palomar, or submit a manuscript. Independent expert review and
the author's release decision are separate from the machine checks.

## Preconditions

1. `PLAN.md` shows `phase_iii_status: done`, `open_holes: []`.
2. `scripts/verify.sh` passes on a fresh credential-free clone that has no
   access to the research repository; `docs/verification-results.json`
   records the commit, pins, tool revisions, commands, exit codes and hashes.
3. `scripts/bootstrap-palomar-tools.sh && scripts/verify-palomar.sh` pass in
   that clone (Comparator, NanoDa, Lean kernel; Landrun sandbox).
4. `formalization.yaml` `verification.commit` and `report` are filled in and
   `status.sorry_count` is `1` (the Challenge placeholder only).

## Select the verified snapshot

```bash
proof_commit='<verified snapshot SHA>'
formal_commit=$(git rev-parse HEAD)
git fetch origin
git verify-commit "$formal_commit"
git merge-base --is-ancestor "$proof_commit" "$formal_commit"
git merge-base --is-ancestor "$formal_commit" origin/main
test -z "$(git status --porcelain)"
git diff --exit-code "$proof_commit" "$formal_commit" -- . \
  ':(exclude)README.md' ':(exclude)CITATION.cff' ':(exclude)NOTICE' \
  ':(exclude)formalization.yaml' ':(exclude)docs/**' ':(exclude).zenodo.json'
```

## Repository visibility, signed tag, Zenodo

The repository is private. Making it public, signing a release tag
(`git tag -s v1.0.0-rc1 ...`), enabling the Zenodo GitHub integration and
publishing a GitHub release are human decisions; follow the pattern of
`stafford38-formal/docs/release-runbook.md`. Record only identifiers that
Zenodo actually issues.

## Palomar

After the repository is public and submission is explicitly authorized, the
responsible human opens <https://submit.palomar-registry.org/> and enters:

| Field | Value |
| --- | --- |
| Repository | `itpplasma/global-stafford-formal` |
| Commit | the selected 40-character `$formal_commit` |
| Project directory | repository root (leave blank) |
| Comparator configuration | `comparator.json` |
| Formalization metadata | `formalization.yaml` |
| Compared declaration | `GlobalStaffordChallenge.universalStatement` |

Retain the returned status-page link and review the result there before
separately deciding on registration. No Palomar ID exists before
registration. This runbook provides no automated submission command.
