The audit covers all 11 targets and all 10 Challenge theorems. There is one minor restriction-disclosure issue; no mathematical falsehood, unfaithful definition, or vacuous theorem was found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 8 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity counts: none 10; minor 1; major 0.

**P027-T10 — restriction_inaccurate, minor.** The canonical population/design includes a start uniformly distributed on `[0,8)`. [Random8Witness](/home/ubuntu/sap/tasks/CHFID-P027a-a/SAP/P027a/Defs/Part7.lean:72) asserts the finite four-atom design, its moments, and intervalwise selection equivalences, but does not identify a continuous uniform-start measure or its induced sampling law. The [restriction docstring](/home/ubuntu/sap/tasks/CHFID-P027a-a/SAP/P027a/Challenge/Part1.lean:84), repeated in `record.json`, does not disclose this omission. Omitting the size generator and a Gaussian event-probability assertion concerns the generation of sizes and outcomes, not the randomness in the sampling start. The retained finite witness is correct and nonvacuous.

Fix: add this sentence to the T10 restriction docstring and its record entry: “The continuous uniform-start measure on [0,8) and its induced four-atom sampling law are not identified explicitly.” No theorem change is needed for this restricted package. This omission was already recorded in T10's step-2 reason before reading the record; the step-2 `narrower` classification has not changed.

T12 is correct_whole. T1–T6, T11 and T13 are correct_restricted: their remaining restrictions accurately disclose the formal scope. In particular, T4 distinguishes preservation on positive-weight atoms from the exact common-indicator representation used for its bias formulas; T5 and T6 avoid asserting which implementation produced the table; and T2, T6 and T11 keep ratios of outcome expectations distinct from ratios for each realized population. The recorded restriction text matches each corresponding docstring. Audit-history notes and credited-row lists were not treated as additional hypotheses or as deletions from the canonical claims.

T9 is omission_ok. Its canonical statement includes a formal reading of the table as grouped-estimator averages, as well as a claim about the simulations' actual implementation. T5 and T6 supply explicitly limited numerical incompatibility and estimator comparisons. The supplied files do not contain the generated populations or simulation code needed to certify the implementation assertion. Omitting a separate T9 theorem is defensible; the full provenance assertion remains uncertified. No claim that the printed passage itself is false was substituted for the conditional reading. The paper's aggregation recommendation and the supplement's reporting language were checked against the [main paper, p. 237](https://www150.statcan.gc.ca/n1/pub/12-001-x/2013001/article/11831-eng.pdf#page=9) and [supplement, pp. A3–A4 and A8](https://cyrussamii.com/wp-content/uploads/2013/08/smj_suppl.pdf#page=3).

The blind reading was saved in [reading.md](/home/ubuntu/sap/tasks/CHFID-P027a-a/reading.md) before either JSON input was opened; its SHA256 is `8526bb53bc83cfc47a153b9c0473e29cb93350fc016109e8a365b4458f6ee336`. [claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P027a-a/claim-stage.json) was saved before `record.json` was opened. No step-2 classification was changed after consulting the record.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully, importing only the supplied Defs. It checks valid positive finite designs, an unequal-size aggregation antecedent, the moment predicates, nonzero calibrated parameters, and a general integrability lemma for systematic indicators. [The exact-arithmetic check](/home/ubuntu/sap/tasks/CHFID-P027a-a/scratch/finite_audit.py) passed for the finite witnesses, all four rounding rectangles, the 120-unit moments, twelve centered-family comparisons, twelve alternating-family cases, all six PPS configurations, and the cap sums. Its detailed output is [finite-audit.json](/home/ubuntu/sap/tasks/CHFID-P027a-a/scratch/finite-audit.json). T12's infinite-law normalization and moments were also checked mathematically using its probability generating function, as explained in `findings.json`. No Solution or Comparator files were read, no `lake` command was run, and at most one Lean process ran at a time.
