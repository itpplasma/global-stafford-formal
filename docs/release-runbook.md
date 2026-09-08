# Release procedure

The author explicitly requested immediate release tags on 2026-09-08 for Palomar submission before the additional dependency replay. Release v1.0.0 uses AlgebraicAnalysis v0.3.0 and Stafford38 v1.1.0 at the exact pins in lake-manifest.json. The repository is public under Apache-2.0 and Zenodo integration is enabled.

Preserve the historical verification record at d76051ce. New-pin replay remains pending under WP-20; do not describe the old report as verification of this release. Build and retain the companion PDF in the tagged tree, sign the tag, publish the GitHub release, and verify the resulting Zenodo archive. Do not move an existing tag.

The author submits Stafford38 first using comparator-fixed-source.json, then Global Stafford using comparator.json. Both use the full release commit, repository root, and formalization.yaml. A registered identifier requires its actual receipt.
