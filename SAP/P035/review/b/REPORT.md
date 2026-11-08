Audited all 3 targets and both Challenge theorem stubs in the required order.
The blind readings were saved in `reading.md` before reading `claims.json`;
`claim-stage.json` was saved before reading `record.json`. Record review required
no change to either claim-stage verdict.

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity counts: none 3; minor 0; major 0. There are no adverse findings.

- **P035-T1 — correct_whole.** The statement matches the full validator-v2
  counterexample, including the independent finite design, six frequencies,
  pointwise observed equality, zero versus positive campaign effects, arbitrary
  rational and real weighted observed laws, and failure of identification. Its
  overall effect uses exactly the canonical raw enrollment shares. It makes no
  assertion about the initiative's actual effect.
- **P035-T2 — correct_restricted.** The two mathematical campaign clauses are
  present, including full enablement of each year's contrast. The docstring and
  record accurately identify the excluded empirical estimate and instruction to
  replace publication wording, and explicitly disclose the absence of a separate
  health-message mediator. The fixed finite models provide valid existential
  witnesses to nonidentification; they do not add a premise assuming it.
- **P035-T3 — omission_ok.** The printed empirical campaign attribution cannot
  be decided by this finite counterexample. Its proposed universal identification
  interpretation is already refuted by T1. Both the canonical note and the record
  correctly distinguish failure of that inference from a finding that the actual
  initiative had no effect.

The independent file `scratch/Check.lean` imports only `SAP.P035.Defs` and compiles
successfully with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It proves
calibration of D and C, equality of their observed laws, zero and positive campaign
effects, the exact overall effect, the LCMs, and all of `T2Statement`, without
using either Challenge stub. Exact rational arithmetic independently checked the
six frequencies and thresholds, all finite success counts, the independence
factorization, and normalization of the design. Every latent support is nonempty;
every denominator is positive; natural subtraction agrees with ordinary
subtraction because the thresholds are ordered. There are no infinite sums,
improper expectations, contradictory hypotheses, or empty index types.
