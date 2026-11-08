Statement audit completed for both targets. There are no adverse findings.

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 0 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 2, minor 0, major 0. Items requiring a correction or an omission explanation: none.

The blind expansion was saved in [reading.md](reading.md) before opening `claims.json`. The comparison with the canonical statements and their required definitions was saved in [claim-stage.json](claim-stage.json) before opening `record.json`. Both stage-2 verdicts were `whole`; neither changed after reading the record. Audit-history notes and unused-helper lists were not used to add or remove target clauses.

For **P036-T1**, `T1Statement` covers all canonical parts (i)–(iii): the corrected indicator/coefficient roles, both conditional-mean statements, the unique minimizer of the actual unadjusted least-squares objective, and the two exact and rounded coefficient calculations. Measurability of the assignment and covariates gives genuine sub-sigma algebras. The probability-measure and integrability hypotheses imply integrability of the predictor and response and sigma finiteness of the trimmed measures, so Mathlib's exceptional conditional-expectation and integral branches do not supply the result. Positive arm probabilities exclude division by zero in conditional arm means.

The finite OLS claim assumes only the two nonempty arms required by the canonical statement. It does not assume the candidate coefficients minimize the objective: it asserts that property for the independently defined residual sum of squares. Algebraically the objective is the two within-arm sums of squares plus `n0*(b0-mean0)^2 + n1*(b0+b1-mean1)^2`. Positive arm sizes therefore give both the stated coefficients and uniqueness. Binary outcomes are imposed only for the table specialization. The architect's `whole` decision and null restriction are accurate; the docstring describes the corrected mathematical content.

For **P036-T2**, `T2Statement` covers all canonical parts (a)–(e). The HC2 definition is the matrix sandwich assembled from actual design rows, residuals and leverages; it is not defined by the desired Neyman identity. Both inverse products are asserted, connecting the explicit inverse array to the actual Gram matrix and the regression coefficients. The theorem also includes the full design variance, both expected sample variances, the exact expectation gap and the constant-effect equivalence, not just the final conservativeness inequality.

The assignment set is precisely all subsets of the required cardinality, and Mathlib's `Finset.expect` is their uniform arithmetic average. From `n1,n0 >= 2` and `n1+n0=N`, one obtains `N >= 4`, nonempty averaging support, positive population-variance divisors, and `1-h_i > 0` for every unit. Every subtraction in a variance denominator is in the reals. The usual single- and pair-inclusion probabilities under this distribution yield the stated first and second moments; the resulting gap is the population variance of the unit effects divided by `N`. A sum of nonnegative squared deviations vanishes exactly when every unit effect equals the same constant. No conservativeness conclusion is assumed as a hypothesis.

T2 is whole relative to the **canonical corrected claim**. Its restriction to an intercept and treatment indicator, fixed potential outcomes, complete randomization and variance conservativeness in expectation is already in that claim. The Challenge docstring states those conditions and the minimum arm sizes. It does not claim a refutation of the printed hedged table note, a bound at every realized assignment, expected-standard-error conservativeness, or a result for covariate-adjusted columns. The architect's `whole` decision and null restriction are accurate. The record's unused helper rows do not identify any missing target conclusion; there are no omitted targets.

A source check of printed pp. 595–596 of the [paper](https://albayanres.com/books/1693343304.pdf) agrees with the supplied regression passage, arm sizes, response counts and the unadjusted coefficient and standard-error entries. This checks the paper-specific inputs; the canonical corrected assertions determine the audited mathematical scope.

Nonvacuity and numerical validation are recorded in [findings.json](findings.json). The command `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully. That file imports only `SAP.P036.Defs`, supplies concrete probability and finite-population instances, proves realizability of both 189-unit binary count inputs, and checks the displayed rational coefficients and variances without using either Challenge stub.

The independent command `python3 scratch/check_exact.py` also passed; its exact results are saved in [scratch/verification.json](scratch/verification.json). It derives the inverse from the Gram determinant and computes HC2 from the sandwich before checking the arm formulas. It checks every assignment for all 256 binary potential-outcome pairs on four units (18 constant-effect cases and 238 strict-gap cases), unequal-arm populations with negative and fractional outcomes, and a six-unit example. Simple nonvacuity examples give `(E[HC2], Var)=(1/8,1/16)` with varying effects and `(1/4,1/4)` with constant effects. Both table variances and every requested rounding cell are checked with rational arithmetic, including square-root cells by squaring their positive endpoints. These finite checks support the mathematical review; they are not a proof of the universal Challenge theorems.

All requested JSON artifacts were parsed and checked with Python 3. No Solution or Comparator proof was inspected, and no proof-certification judgment is made here.
