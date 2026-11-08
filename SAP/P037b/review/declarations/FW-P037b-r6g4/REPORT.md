# Omission review

Both omissions are justified under the explicit rule permitting omission when a target has no proved row. The fingerprints in `findings.json` match `closure.json`.

- **P037-T16 — omission_ok, none.** `claims.json` sets `no_lean` to `true`, with empty `rows` and `coverage_judgments`. The recorded absence of credited declarations is accurate. The canonical claim concerns the printed school-level tables and their procedure descriptions; there is no target-credited declaration from which to obtain a faithful restricted statement by glue. The audit note's discussion of P037-T4 supplies neither an additional claim clause nor a credited row. The recorded reason does not misdescribe this target.
- **P037-T17 — omission_ok, none.** `claims.json` likewise sets `no_lean` to `true`, with empty `rows` and `coverage_judgments`. The recorded absence of credited declarations is accurate. The canonical claim reports the printed disciplinary-report reduction estimates. References to P037-T6 in the definitions and audit note do not supply credited rows for this target, and restating another target's arithmetic would not remedy the omission under the review rules. The recorded reason does not misdescribe this target.

The unit's Challenge contains neither target. No new proofs or Lean compilation were needed because neither target has a credited declaration to inspect or combine. No paper search was needed.
