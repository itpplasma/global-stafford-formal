# Proof-source provenance

## Status

Global Stafford Phase I, Phase II and the isolated replay/packaging phase are complete in this repository. Human paper review remains separate.

## Upstream research proof

Authoritative research repository: `itpplasma/global-stafford`.

Read the research sources in this order when checking paper-to-Lean correspondence:

1. `PLAN.md` — live research status, exact theorem and consumed dependency pins;
2. `notes/source-changing-descent-2026-09-07.md` — complete source-changing descent proof candidate, Theorem 6.3;
3. `notes/source-descent-adversarial-review-2026-09-07.md` — independent-context model review and repairs;
4. `docs/proof-graph.yaml` — candidate dependency chain;
5. `docs/provenance-prior-art-novelty-2026-09-09.md` — literature/provenance boundary.

There is no separate paper repository: the paper/proof note remains in `itpplasma/global-stafford`. The formal `PLAN.md` records the historical paper revision and the exact Stafford38/algebraic-analysis pins consumed by the verified build.

## Formal read order

For formal maintenance read this repository's `PLAN.md`, `docs/paper-lean-specification.md`, `docs/verification-results.json`, and `docs/release-runbook.md` after the research proof sources above.

The research repository is a provenance/specification source, not a build dependency.