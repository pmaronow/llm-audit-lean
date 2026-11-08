# P044 declaration review

All five declarations are **faithful**, with severity **none**. Their recorded
`whole` decisions are correct. No step-2 conclusion changed after reading the
record.

The blind reading was saved in [reading.md](reading.md) before opening the
claims or record. [claim-stage.json](claim-stage.json) records the subsequent
comparison. I inspected all 133 distinct declarations in the combined closures,
including generated matchers, recursors, projections and auxiliary types.

| Declaration | Coverage checked |
| --- | --- |
| `SAP.P044.T1` | The complete twelve-unit witness, actual counts and exposure mapping, both bank/observation laws, all exact and simulated-input moments, strict shortfalls, and both fixed-table classes and their symmetries. |
| `SAP.P044.T2` | The exact structural-zero surplus identity and conservativeness for every supported finite design, both T1 shortfalls, the exhaustive matching family including 10,000 rows and first-row reuse, and the additional error-transfer identity and inequality. |
| `SAP.P044.T3` | The complete star witness, all six exposure vectors and marginal probabilities, equal observed data and distinct targets, arbitrary-statistic impossibility, and unconditional observed-only HT means and biases. |
| `SAP.P044.T4` | All clauses (a)–(d): support-qualified unbiasedness, necessity through an unobservable schedule perturbation, the fixed common-support estimand, and complete-randomization formulas and degree criteria, including the specified examples. |
| `SAP.P044.T5` | The triangle arithmetic, positive-probability negative events, distinct baseline law, CDF expression, Gaussian moments and shifts, and nonisolated-graph comparison, with finite second moments. |

The sampling laws meet the canonical conditions. T1 explicitly calls for a
uniform 65-element subset of the 66 assignments. T2's matching banks uniformly
permute the exhaustive design; their included observation is their first row.
Neither canonical target requires independence among these bank rows. T1, T3
and T5 are themselves canonical counterexample assertions, so proving them is
properly classified as `whole`.

The definitions implement the stated notions. The hard-coded clique tables are
connected to actual counted exposures and smoothed retained-bank tables by
explicit conclusions in T1. The HT variance sums use ordered pairs and the
specified structural-zero adjustments. T4 retains the original exposure map
and design when selecting the common-support subset. T5 counts distinct
endpoints of two-edge walks, including first neighbors, and uses Gaussian
variance 1/16 for the additive noise. Its source-code identification is external
provenance exactly as stipulated in the canonical claim.

There is no material junk-value dependence. Positive marginal hypotheses or
observed-term guards protect HT divisions. Population and subset denominators
are nonzero. The complete-randomization bounds prevent empty sample spaces and
incorrect truncated subtraction. Clique subtraction deletes a row that is
actually counted. All Gaussian transformations are measurable, and the L²
assertions ensure actual finite moments. The square-root argument is positive.

[scratch/Nonvacuity.lean](scratch/Nonvacuity.lean) contains independent examples
for the finite designs, transfer premises, missing-support perturbation, finite
witnesses and Gaussian-model data. The scratch proofs use definitions and
Mathlib rather than the certified Challenge stubs. It compiled successfully
with `/home/ubuntu/sap/tools/sap-lean` (exit 0). Closure inspection output is in
[scratch/closure-print.log](scratch/closure-print.log). Both JSON outputs parse;
all five theorem names, target IDs, and fingerprints match `closure.json`.

Final machine-readable verdicts and fingerprints are in
[findings.json](findings.json).
