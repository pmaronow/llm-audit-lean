# Review of SAP.P026b.T18–T22

All five declarations are **faithful**, severity **none**. Every declaration in each listed statement closure was read, including generated proof auxiliaries. `reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved before opening `record.json`. The record required no changes to the claim-stage conclusions. The `different` entries in that intermediate file indicate the polarity of valid refutations, not a fidelity defect.

**T18 — valid refutation.** Printed reading: under the finite binary design, a deterministic function of any collection of observed outcomes whose individual treatment indicators are each independent of the focal treatment must have zero covariance with that treatment.

The witness satisfies every relevant condition:

- The four XOR allocations have nonnegative real weights summing to one; each treatment and control marginal is 1/2.
- Potential outcomes are fixed, with treatment outcome 1 and control outcome 0, so each fitting outcome equals its treatment indicator.
- Both fitting treatment indicators separately satisfy independence from the focal indicator, including the quantified test-function definition.
- The polynomial fit uses only those two observed outcomes and no other randomness. All functions are measurable and all moments exist on this finite space.
- The fit equals the focal indicator, giving covariance 1/4. This contradicts the canonical general rule itself. Joint-vector independence is not a condition of that printed rule. The correct single-input footnote and correct independent-design examples need not fail for this refutation to succeed.

The full witness and covariance were independently proved in `scratch/T18Check.lean`.

**T19 — valid refutation.** Printed reading: the selected FE (Cov.), G (Linear), and G (Logit) entries are the stated moments, to three decimals, for Table 1 under the Section 7.1 estimators and all 90 equiprobable assignments.

The fixed population, both independent uniform within-block choices, cluster memberships, and sharp-null outcomes match that setting. FE is the treatment coefficient after removing stratum fixed effects and the covariate. The linear residual vector equals the cluster sums from the specified opposite-block OLS fits, checked exactly. Logistic likelihoods fit the appropriate data; predictions intentionally use the other block's coefficients, as required by [Section 7.1, p. 148](https://joelmidd.github.io/papers/AronowMiddleton_A%20class%20of%20unbiased%20estimators.pdf#page=14). Cluster sums, the population divisor 16, and the variance formula match the prescribed estimators.

No undefined fit is exploited: all 90 FE denominators are positive, with minimum 2710/993. In each logistic stratum a negative outcome at covariate 2 lies between positive outcomes (0 and 4, or 1 and 4). The compiled separation inequalities force every separating direction to zero. Thus the log likelihood is coercive and, because its design has rank two, strictly concave, giving a unique finite maximizer. The coefficient selector's fallback is inoperative.

Exact rational enumeration gives FE mean approximately −0.013987426269439, outside the interval rounding to −0.012. Already this entry contradicts the asserted conjunction. The theorem and docstring correctly assert that the selected entries cannot **all** hold; they do not assert that each entry fails.

**T20 — whole.** Both masking identities, unbiasedness of both HT totals, and ATE unbiasedness are stated for every finite binary assignment law with positive marginals. `UnitExperiment` encodes precisely those law conditions. No independence, equal inclusion probability, or fixed treatment count is added.

**T21 — whole.** The target uses `T21WholeStatement`, not the older Part5 definition. It includes the supported actual-difference-in-means identity and unbiasedness in (a), the original-unit cluster contrast and unbiasedness under the canonical conditions in (b), and a genuine real-valued bias witness for (c). Distinct cluster indicators are required as in the standing assumptions. The cluster theorem adds no fixed realized cluster count. The witness has both unit arms nonempty on support, expected difference in means 1/9, and ATE and expected HT zero.

**T22 — whole.** Zero covariance implies both generalized-total identities and ATE unbiasedness. Fixed predictions and their zero covariances are explicit. The adjustment identity is assignmentwise and outside the covariance antecedent. Its definitions use the same prediction for both arms, exactly as stipulated.

The independent file `scratch/InstanceChecks.lean` compiled successfully, constructing every probability/partition field and the required unit and cluster hypotheses, including the supported bias witness and a nonzero fixed prediction satisfying T22. `scratch/NumericalCheck.py` and its JSON output contain the exact T19 enumeration. A full independent Lean numerical recomputation was not completed; the certified original proof is accepted as instructed. Detailed check status is in `scratch/verification.json`.

All meaningful divisors are positive. Truncated natural subtraction is protected by strict inequalities. Empty-arm means occur only off support where they cannot affect asserted expectations. Logistic log arguments are positive, variances are nonnegative, and no integral, infinity, extremum, or limit default supplies a conclusion. No correction is needed.
