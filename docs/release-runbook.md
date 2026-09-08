# Release and submission runbook

The author explicitly authorized the three coordinated software releases and
confirmed the Zenodo integrations on 2026-09-08. WP-20 owns the dependency
upgrade and fresh verification required for this release. Human expert review
and Palomar registration remain separate from machine checking and publication.

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
proof_commit='d76051ce227f41c0fb21f114ffd61890f3b6b99b'
formal_commit=$(git rev-parse HEAD)
git fetch origin
git verify-commit "$formal_commit"
git merge-base --is-ancestor "$proof_commit" "$formal_commit"
git merge-base --is-ancestor "$formal_commit" origin/main
test -z "$(git status --porcelain)"
git diff --exit-code "$proof_commit" "$formal_commit" -- . \
  ':(exclude)README.md' ':(exclude)CITATION.cff' ':(exclude)NOTICE' \
  ':(exclude)formalization.yaml' ':(exclude)docs/**' ':(exclude).zenodo.json' \
  ':(exclude)PLAN.md' ':(exclude)scripts/record-verification.py'
```

## Companion PDF and source artifacts

The Stafford38 pattern uses separate source archives and checksums, a Challenge
dossier reading the actual Lean files, and a proof-map supplement. Its latest
GitHub release on inspection (8 September 2026) is `v1.0.2`; its citation file
records concept DOI `10.5281/zenodo.22390721` and version DOI
`10.5281/zenodo.22391362` for `v1.0.1`. Those identifiers belong to Stafford38.
Global Stafford has no DOI in the current record.

After selecting a clean metadata-bearing commit with the unchanged proof bytes
above, build and inspect the companion, including its map links:

```bash
docs/dossier/build.sh
release_dir=$(mktemp -d /tmp/global-stafford-release.XXXXXX)
git archive --format=tar.gz --prefix=global-stafford-formal/ \
  --output="$release_dir/global-stafford-formal.tar.gz" "$formal_commit"
cp docs/dossier/global-stafford-dossier.pdf "$release_dir/"
cp docs/dossier/build-manifest.json "$release_dir/"
cp docs/verification-results.json "$release_dir/"
(cd "$release_dir" && sha256sum global-stafford-formal.tar.gz \
  global-stafford-dossier.pdf build-manifest.json verification-results.json \
  > SHA256SUMS)
printf '%s\n' "$release_dir"
```

The source archive contains the TeX and map sources and the build script. The
PDF and its manifest are generated artifacts attached separately. Inspect the
archive with `tar -tzf`; dependencies remain pinned external packages. The
canonical paper stays in the research repository; this companion does not
publish a separate paper repository or replace its manuscript authority.

Use `docs/release-notes.md` as the reviewed release description and
`.zenodo.json` as the deposit metadata. After the separately authorized
visibility change and signed tag, the final GitHub release command can use
`--notes-file docs/release-notes.md` and attach the four artifacts plus
`SHA256SUMS`. Enable the Zenodo GitHub integration before publishing that
release. Record only the issued concept and version DOIs in a follow-up
citation update; do not invent a DOI or carry over a Stafford38 identifier.

## Repository visibility, signed tag, Zenodo

The repository was made public under Apache-2.0 on 8 September 2026,
with the author’s explicit authorization. The author confirmed the Zenodo
GitHub integration on 8 September 2026. No tag,
GitHub release, Zenodo deposit or Palomar registration was created by the
visibility change. Follow the Stafford38 release pattern and record only
identifiers that Zenodo actually issues.

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
