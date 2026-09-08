# Release procedure

The corrective release v1.0.3 uses the unique GlobalStaffordChallenge and GlobalStaffordSolution modules through comparator.json. Its checked source and exact dependency pins are recorded in docs/verification-results.json. Phase I/full verification and both standard and canonical-Challenge comparisons passed locally; hosted Palomar acceptance remains separate.

Sign and publish the release only after the recorded checks pass. Preserve the frozen statement, existing tags and historical reports. The release includes its overview PDF and machine-readable evidence. Verify the Zenodo archive after its publication event succeeds.

The author submits Stafford38 first using comparator-fixed-source.json, then Global Stafford using comparator.json. Use the full release commit, repository root and formalization.yaml. A failed submission's old commit cannot acquire a later fix; submit the corrective release commit.
