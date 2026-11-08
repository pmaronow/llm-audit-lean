All five declarations are **faithful**, with severity **none**. The recorded
`whole` decisions and the theorem docstrings accurately describe their scope.
The step-2 conclusions in `claim-stage.json` required no change after reading
the record.

| Declaration | Review result |
| --- | --- |
| `SAP.P016b.T12` | Includes the directional mean property, both nonempty-group KS failures, arbitrary-score exact-tail validity, and every entry of the finite-design tables. |
| `SAP.P016b.T13` | Includes the exchangeable rank calculation, complete finite-design witness, independent observed/reference sampling, mixture formulas, bounds, five decimal prefixes, strict comparisons, and positive zero-p probability. It concerns the archived weak rule and does not claim to refute the printed strict rule. |
| `SAP.P016b.T14` | Includes all five canonical clauses. Strict positivity in exact-tail clause (e) comes from its explicit reference to T12(iii); the iid clause permits zero-weight atoms. |
| `SAP.P016b.T15` | Includes all three exact witnesses. The full adjustment vectors retain the controls, the ECDF values distinguish the two thresholds, and the diagonal excludes the stated truth. |
| `SAP.P016b.T16` | Includes all corrected adjustment identities and parameter dependence, control ECDF invariance, the ECDF count, and membership of the truth in the separately indexed family. |

Every listed closure declaration was read, including generated auxiliaries and
the finite-law constructor and projection. The source definitions use actual
finite counts, sums, normalized probability weights and coordinate adjustments.
None hides the desired conclusion. Required denominators are nonzero, natural
subtraction does not truncate in the stated uses, and probability-measure
assumptions prevent `toReal` of infinite mass. The nonempty domains of empirical
distributions and group statistics preserve their ordinary meaning.

The review followed the required order: `reading.md` was saved before opening
the claims, and `claim-stage.json` was saved before opening the record. Both
`scratch/Nonvacuity.lean` and `scratch/ExchangeableNonvacuity.lean` compiled
successfully with `sap-lean`, importing definitions without the Challenge
stubs. These checks construct positive and zero-atom laws, genuine decreasing-KS
witnesses, balanced assignments, an exchangeable tie-free probability law for
every reference count, the complete T15 witness, and a T16 instance satisfying
all its simultaneous hypotheses. The supplied Comparator certification is
the proof evidence for the audited declarations; the scratch files check
their interpretation and nonvacuity independently.

`findings.json` contains exactly five entries with fingerprints copied directly
from `closure.json`; both JSON output files were parsed and validated.
