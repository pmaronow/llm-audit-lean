All five declarations are **faithful**, with severity **none**, relative to their
canonical claims and definitions.

| Declaration | Result | Reason |
| --- | --- | --- |
| `SAP.P026a.T1` | faithful / none | Both prescribed counterexamples, their support certificates, literal-domain failure, and exact estimator values and biases are included. |
| `SAP.P026a.T2` | faithful / none | All corrected estimator formulas, exact biases, conservativeness, sharp-null characterization, strict example and fixed-residual versions are covered. |
| `SAP.P026a.T3` | faithful / none | The canonical directed-support repair, covariance and variance results, residual versions, nonimplication witness and attained numerical-design minima are covered. |
| `SAP.P026a.T4` | faithful / none | The nonlinear fits use permitted pairwise-independent inputs and violate the printed multi-outcome assertion under all its conditions. Both prescribed examples and their biases are included. |
| `SAP.P026a.T5` | faithful / none | Both whole-vector premises, unbiasedness, full-vector factorization, scalar case, additive case, and independent-unit/block applications are covered. |

The record's `whole` decisions and the Challenge docstrings agree with these
statements. T1 and T4 fully state the canonical counterexample claims; their
refutations concern the printed assertions themselves. No step-2 conclusion
changed after reading the record.

No substantive hypothesis was hidden or assumed as a conclusion. Every
relevant denominator is positive or protected by the expressly specified
zero-joint convention. T1 distinguishes undefined literal equation [34] from
its explicitly omitted-term continuation. All moments used here are finite
sums.

The blind reading was saved in [reading.md](reading.md) before opening the
canonical claims. [claim-stage.json](claim-stage.json) was saved before opening
the record. [claim-audit.md](claim-audit.md) gives the clause comparisons and
condition-by-condition refutation checks.

Validation passed: `sap-lean scratch/BlindCheck.lean` printed every generated
closure auxiliary; `sap-lean scratch/Nonvacuity.lean` constructed nonvacuous
instances and genuine witnesses using Defs alone; and
`python3 scratch/recompute.py` independently checked the finite numerical
claims in exact rational arithmetic. The nonvacuity compilation has one
stylistic linter warning and no errors. JSON parsing, fingerprints and the
one-entry-per-declaration requirement were checked with Python.
