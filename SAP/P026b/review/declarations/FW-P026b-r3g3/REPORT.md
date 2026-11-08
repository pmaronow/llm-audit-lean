# Declaration review

| Declaration | Claim coverage | Verdict | Severity |
| --- | --- | --- | --- |
| `SAP.P026b.T23` | Whole | faithful | none |
| `SAP.P026b.T24` | Whole | faithful | none |

The blind expansion and boundary analysis were saved in `reading.md` before
opening the claims. Both claim-stage conclusions in `claim-stage.json` remain
unchanged after reading the record. The record's `whole` decisions and both
Challenge docstrings accurately describe the statements.

T23 includes the exact affine HT identity, the necessary and sufficient
intercept-or-balance criterion, a supported failure of general HT location
invariance, and generalized-estimator scaling under identical transformations
of outcomes and predictions. Its single-unit witness has genuine positive
treatment and control probabilities. The rational witness and a real-valued
realization were checked independently.

T24 includes both residual identities, the original-unit variance expression
for predictions fixed across assignments, both cluster arm variances, and
the full, split, and off-diagonal covariance expressions. Cluster totals are
actual sums over a surjective partition. Positive disagreement between
distinct cluster indicators is part of standing assumption S7. Equation [30]
retains contributions from zero directed cross-arm joint probabilities;
the incorrect intermediate positivity argument quoted in the claim is not
asserted by the theorem. All six equation assertions [25]–[30] are covered.

Every marginal denominator is positive, and every population denominator is
the cardinality of a nonempty finite population. Finite probability sums
supply the required measurability and moments. No additional substantive
hypothesis, assumed conclusion, placeholder definition, or consequential junk
value was found.

`scratch/Blind.lean` compiled successfully and exposed all generated auxiliary
proofs in the two closures. `scratch/Nonvacuity.lean` also compiled successfully
with `/home/ubuntu/sap/tools/sap-lean`. It constructs both experiment types,
checks the complete T23 witness, and tests T24 on an unequal-cluster design
with a zero directed joint probability: true, split and off-diagonal
covariances all equal `-159/4`. A nonzero fixed-prediction example has actual
generalized variance and displayed residual variance both equal to `373/8`.
Both JSON deliverables were parsed and their declaration coverage checked
with Python.
