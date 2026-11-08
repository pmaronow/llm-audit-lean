# P027b declaration review

All five declarations are **faithful**, severity **none**. Each was reviewed
separately with its complete elaborated definition closure. `reading.md` was
saved before opening `claims.json`; `claim-stage.json` was saved before opening
`record.json`. Reading the record changed no claim-stage conclusion.

| Declaration | Assessment |
|---|---|
| `SAP.P027b.T14` | All C1–C3 fixed-population and model-average witnesses, normalizations, strict rankings, and relative biases are present. The rounded table rows are comparison context. |
| `SAP.P027b.T15` | All five clauses are present: sample formulas, population variance, second-moment model averages, exact bias rankings, ratios, and limits. |
| `SAP.P027b.T16` | The Gaussian witness has the required fair common stratum, genuine independent errors, positive variances, ordinary Pearson discrepancy, and both stratum-mean variance conventions. The conditional assertion is also correct. |
| `SAP.P027b.T17` | The moment-based pair correlation, divisor-1 heterogeneity definition, discrepancy, both conversions, monotonicity, limit, and six exact labels are covered. |
| `SAP.P027b.T18` | All first/joint inclusion and covariance cases, including the diagonal and M=1 boundary, are covered. The separate outcome-index correction is a definition, as the canonical claim expressly permits. |

The counterexample readings were checked against their settings. For T14 the
reading is a reversal of the **bias** ranking at fixed M, followed by a large-M
model-average discrepancy. Its conditions are the specified fixed populations
or independent standard Gaussian generated errors, independent uniform stratum
draws, the stated mean-scale estimators, and genuine finite expectations; each
condition is met. For T16 the reading is disagreement with **ordinary Pearson
correlation** for two distinct units sharing a randomly chosen stratum. Its
conditions are a fair common sign, separate independent standard Gaussian
errors, alpha=1/2, and finite second moments with positive variances; each is met.
Neither theorem labels the canonical counterexample assertion itself false,
and neither claims to determine the authors' intended correlation convention.

Both scratch checks compiled using `/home/ubuntu/sap/tools/sap-lean`:
`scratch/BlindChecks.lean` prints all 103 distinct closure declarations, including
the listed generated proof constants; `scratch/Nonvacuity.lean` independently
constructs the Gaussian noise and sign/Gaussian pair models, verifies every
moment premise, and supplies the finite population/design instances. The final
nonvacuity compilation exited 0 without diagnostics and invokes no audited
theorem. Finite moments, positive denominators, guarded pair divisions, and
positive-probability conditioning exclude all relevant junk-value effects.
The limit sequences' M=0 values do not affect their limits at infinity.

All five `whole` decisions and the Challenge docstrings accurately describe
the mathematical statements. One ancillary provenance sentence is stale:
`record.json:18` says T14's C2–C3 are omitted, although
`SAP/P027b/Defs/WholeW1.lean:59` and
`SAP/P027b/Defs/WholeW1.lean:69` explicitly include them. This is an obsolete
`rows_not_used` explanation, not a declared restriction or a statement defect;
the record's `whole` decision and null restriction are correct. That explanation
should say the standalone arithmetic row is unused because the actual model
expectations are established through the moment calculations.

`findings.json` contains exactly one entry per target, with fingerprints copied
from `closure.json`. Both JSON deliverables were parsed and their target sets
checked with Python. No SAP source file was changed.
