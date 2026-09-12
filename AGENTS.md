# Agent rules — global-stafford-formal

This repository owns the Lean 4 formalization of the Global Stafford theorem
(same-divisor identity `1 = dR + FdS` in `D_k(A)` for every smooth integral
affine `A` over a characteristic-zero field) and its Palomar interface.
`PLAN.md` is the sole live plan and status; read it completely before any
edit. The internal informal exposition, working notes, research history, and
superseded routes live in the private research repository
`itpplasma/global-stafford`; they are records of the same research development,
not a separately published or presented prior source. Do not import from that
repository and do not need it to build or verify this formalization.

## Non-negotiable rules

- Every step in `PLAN.md` is implemented exactly as specified unless the
  specification is mathematically wrong; in that case stop, write
  `docs/escalations/<wp>-<name>.md` with the counterexample or the failing
  goal, commit, and report `ESCALATE`.
- No `axiom` declarations. No `native_decide`, `Lean.ofReduceBool`,
  `decide` on large goals, or `unsafe`. Literature inputs are fields of the
  `structure`s named in `PLAN.md` Section 7 during Phase I and are proved in
  Phase II.
- A `sorry` may exist only as a stub of a statement written in `PLAN.md`,
  registered in the `open_holes` list of `PLAN.md` in the same commit.
- `Challenge.lean` is frozen. It imports only Mathlib and contains exactly one
  `sorry`. `Solution.lean` never imports `Challenge`.
- Keep the noncommutative order: products in `D_k(A)` are compositions,
  `d` stays where the paper puts it, `f^m R` is a right ideal, coefficients
  pass operators only through the binomial formulas of WP-1.
- Dependency pins (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`)
  change only through a work package that says so; never run `lake update`.
- Commit after every green build of the file you are editing, at least once
  per hour, with a message naming the work package and the declarations; push
  to `origin main` immediately after each commit (`git pull --rebase` first).
- Tests need an independent oracle (a literal consumer with `#print axioms`,
  or a finite computation checked by `norm_num`/`simp` on a concrete ring),
  not a restatement of the patch.
- Update the status table in `PLAN.md` (Section 9) when claiming, finishing,
  or blocking a work package. Record escalations and their resolutions under
  `docs/escalations/`.

## Escalation ladder

1. Implementing agent (Claude Sonnet): two attempts per lemma or one hour.
2. Claude Opus: reads the escalation file, resolves or re-specifies.
3. Claude Fable (controller): mathematical re-specification, plan change,
   or research-repository change.

## Style

Mathlib naming and sidedness conventions; `namespace GlobalStafford.<Area>`;
module docstring naming the paper lemma; `#print axioms` for every public
theorem at the end of the file; no `set_option maxHeartbeats` above
`800000` without a comment explaining why.

## Publication policy

No visibility change, tag, release, DOI, Palomar registration, or
manuscript submission without explicit human authorization. The
`docs/release-runbook.md` lists those human actions; agents prepare, humans
execute.

## Proof-source provenance

Read `docs/proof-source-provenance.md` before changing proof or provenance
status. The complete source-changing-descent proof candidate and its review
record live in `itpplasma/global-stafford`; the exact proof note, adversarial
review, proof graph, and consumed dependency pins are listed there. There is no
separate paper repository. This formal repository is already Phase I/II/III
complete; upstream proof files are for correspondence and maintenance, not a
new theorem queue.
