# Release procedure

Current published software release: **v1.0.6**.

The author explicitly authorized the v1.0.6 literature documentation release. Do not create a further release merely
because documentation is edited on `main`. A new release is warranted only for
an explicitly authorized release event or a substantive correction that should
be frozen as a new immutable software snapshot.

## Mathematical verification boundary

The current mathematical verification record is tied to source
`b21883a5b3d8f46922713049c3b060523ea3a771` and report SHA-256
`08b8dcd152806c5033316100a624d8c61a67f9e069c18ac649f3c6612779db67`.
The consumed mathematics pins are recorded in `lake-manifest.json` and
`docs/verification-results.json`:

- AlgebraicAnalysis `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`;
- Stafford38 formal `e77e176c381ca2d6b20c030f9227f1b031415d2e`;
- Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`;
- Lean `v4.33.0`.

The historical Stafford38 inspection pin `784b5992...` must never replace the
consumed pin in current reproduction instructions.

Documentation-only provenance/literature edits after the verified snapshot do
not retroactively change that report. If Lean proof sources, dependency pins,
Challenge/Solution bytes, Comparator configuration, or verifier scripts change,
run a new independent replay and record a new verification source/report before
claiming the changed mathematics verified.

## Palomar record

Current linked record:

- `PALOMAR-2026-09-05-000007`
- version `2`
- <https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000007&version=2>

A GitHub software release does not by itself create or bump a Palomar registry
version. Do not infer a new Palomar version from a new tag.

## Provenance and novelty gate

Before a release description makes novelty claims, read
`docs/provenance-literature-novelty.md`. The permitted current formulation is
that the 2026-09-09 audit found no prior proof of the exact theorem and strong
novelty evidence, including a 2026 expert survey that still lists a weaker
smooth-affine `D(X)` two-generator problem as open. Do not claim that the
literature search certifies absolute historical priority or first publication.

## Packaging checklist for a future authorized release

1. Refresh `main` and identify the exact target commit.
2. Confirm whether changes are proof-affecting or documentation-only.
3. For proof-affecting changes, complete a fresh isolated replay and update
   `docs/verification-results.json`; for documentation-only changes, retain the
   existing verification report and say explicitly that proof bytes are
   unchanged.
4. Check `CITATION.cff`, `.zenodo.json`, `formalization.yaml`, README,
   `docs/release-notes.md`, and the dossier for the same release version,
   dependency pins, provenance wording, and Palomar ID/version.
5. Build the dossier and its source-hash manifest.
6. Preserve historical reports/tags; never rewrite a past release to make it
   appear to contain later verification.
7. Publish only after explicit author authorization, then verify the GitHub and
   Zenodo release metadata.

Human expert review, journal submission, Palomar editorial status, software
release status, and machine proof verification remain separate processes.
