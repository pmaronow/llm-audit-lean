All five declarations are **faithful**, with severity **none**. Their full
statement dependency closures were reviewed independently. `reading.md` was
saved before opening `claims.json`; `claim-stage.json` was saved before opening
`record.json`. The record's five `whole` decisions agree with the claim-stage
readings, which were not changed afterward. No source changes are proposed.

| Declaration | Coverage |
| --- | --- |
| `SAP.P005a.T1` | All five parts of the specified six-unit counterexample, including the decomposed bound, positive gap, shifts and centered comparison. |
| `SAP.P005a.T2` | Both arms, arbitrary fixed arrays, unchanged expectation, repaired centered variance bound, and all stated product-moment and variance proof steps. |
| `SAP.P005a.T3` | All six parts of the sixteen-unit counterexample: regularity, moments, category distribution, two failed bounds, and valid third/centered comparisons. |
| `SAP.P005a.T4` | The complete finite chain, intermediate raw leverage moment, both coefficient estimates, deterministic right-hand-side order, variance order and scaled variance order. |
| `SAP.P005a.T5` | All five parts of the six-unit sign counterexample, including both individual expectations and the reversed-sign comparison. |

The printed readings and witness conditions were checked separately:

* **T1:** The uncentered expression is asserted to bound covariance variance
  for arbitrary fixed arrays, n≥4, and either nonempty arm under complete
  randomization. The witness has n=6, treated size four, real fixed arrays,
  and all 15 assignments equally weighted. No covariate or Assumptions 1–3
  conditions belong to this lemma. Its positive gap is 11531/14400.
* **T3:** The first two printed expressions are asserted to bound the treated
  leverage/outcome covariance variance under the paper's finite conditions.
  The witness has n=16, d=1, balanced allocation, exact standardization,
  second moments bounded by K=1, and all three regression matrices invertible
  under every assignment. Both positive gaps are confirmed. The third
  expression and the asymptotic rate are not refuted.
* **T5:** The printed identity asserts that the control-minus-treatment ν3
  expectation equals its displayed weighted population covariances. The
  witness has n=6, d=1, treated size two, fixed standardized covariates,
  second moments bounded by K=28, allocation between 1/4 and 3/4, and positive
  arm variances under all 15 uniform assignments. The actual component is
  217/2500; the displayed value is -217/2500.

These are genuine counterexamples to the quoted displays. The canonical
targets themselves assert those counterexamples, so their `whole` labels
are appropriate. No sequence embedding mentioned only in audit history was
mistaken for an additional canonical clause.

The definitions use the correct finite uniform design, arithmetic means,
covariance divisor, centering, leverage, arm matrices and signed ν3 terms.
Relevant designs and denominators are nonempty/nonzero; square roots have
positive arguments; κ is an actual finite maximum. T4's arbitrary values at
n=0,1 do not affect its eventual claims. Dimension zero has the ordinary
empty-dimensional interpretation. Finite real arrays need no additional
measure-theoretic assumptions.

Validation passed: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`, using
definitions and Mathlib without the audited theorems; and
`python3 scratch/exact_checks.py`, using exact rational arithmetic over all
15, 12,870 and 15 counterexample assignments. The Lean checks include concrete
finite hypotheses, standardization and moment checks, and an entire sequence
satisfying T4's hypotheses. All conditionals are jointly satisfiable.
The output JSON files were parsed and checked for complete target coverage
and exact fingerprint copying.
