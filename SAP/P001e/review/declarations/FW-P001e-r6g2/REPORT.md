# Review of P001-T82 through P001-T86

All five declarations are faithful to their recorded scope. T82–T85 state their
whole canonical claims. T86 is accurately labelled and documented as restricted.
There are no adverse findings.

The review followed the required order: `reading.md` was saved before opening
`claims.json`; `claim-stage.json` was saved before opening `record.json`. No
stage-2 conclusion changed after reading the record. Every declaration in the
five dependency closures, including generated numeral proofs, was inspected.

| Declaration | Claim comparison and record assessment |
| --- | --- |
| T82 | The measurable probability kernel is constrained by the actual disintegration identity. Its probability, Bernoulli mean and conditional-mean version agree; boundedness, uniqueness almost surely, the impossible-range characterization and the printed-threshold tautology cover the canonical correction. `whole` is correct. |
| T83 | Almost-sure binarity and positive mass of both responses represent the support assumption. Conditional independence and uniform positivity are exactly the two printed MAR conditions. The recorded outcome uses the correct sentinel and both expectation identities are present. `whole` is correct. |
| T84 | The cell likelihood is the Bernoulli likelihood of the specified twelve observations. The unique ML parameter, fitted probability, two estimator values and their gap match the canonical counterexample. The canonical statement itself specifies the exact-equality reading being tested, so `whole` and the docstring's qualified language are correct. |
| T85 | Actual observed sample fibers produce the defined counts and sums. All grouping identities, the all-outcome-vectors criterion and the saturated stabilization identities are present. Positive weights beyond probabilities only generalize the algebra; no canonical case is excluded. `whole` is correct. |
| T86 | The one-unit conditional and unconditional mean-one identities and the reciprocal-weight inequality and equality criterion are present. The pointwise version assumptions and omitted sample formula, sample mean-one conclusion, fitted-propensity convergence and efficiency discussion are explicitly disclosed in both the docstring and record. `restricted` is correct. |

The printed reading tested by T84 is: finite-support covariates and an ML
binary-choice propensity fit force exact equality of the realized IPW and
post-stratification plug-in estimators. Its witness meets the relevant conditions:

- Three covariate values, each observed four times, give finite discrete support.
- Response counts `(2,3,2)` give binary response, respondents and nonrespondents
  in every cell, and strictly positive estimator denominators.
- The respondent outcomes give cell sums `(3/4,3/2,3/4)`; unobserved latent
  outcomes can all be set to `1/4`, with recorded nonresponses equal to `-99`.
- The sample likelihood is exactly the three-cell logit likelihood, whose
  unique ML fit is the one asserted by T84.
- Compatibility with i.i.d. sampling and MAR is substantive: take independent
  uniform `X` on `{-1,0,1}`, uniform latent `Y` on `{1/4,1/2,3/4}`, and
  Bernoulli response of probability `7/12`. Draw twelve independent units.
  This population satisfies MAR with uniform positivity and the true logit
  parameter `(log(7/5),0)`. The specified ordered completed sample has positive
  probability `(7/108)^7 (5/108)^5`.

Thus this witness does not rely on dependent sampling, a nonmeasurable variable,
an undefined quantity, or a misspecified propensity model. It verifies the
canonical counterexample; it does not refute that canonical assertion.

All ordinary expectations and probability conversions are used on finite
measures with the required integrability. Propensity denominators are positive
where used, up to null sets where the statement permits versions. Logistic
probabilities and likelihood log arguments are strictly positive. No empty
sample, empty-cell division, nonintegrable-integral default, or infinity-to-real
conversion changes any conclusion. The definitions neither encode the
conclusions as hypotheses nor replace the statistical notions with placeholders.

Lean validation used only `/home/ubuntu/sap/tools/sap-lean`, with at most two
processes concurrently and no `lake` invocation. `scratch/BlindPrint.lean`
checks the target types and prints all closure auxiliaries.
`scratch/Nonvacuity.lean` constructs a fair two-point probability space realizing
all hypotheses of T82, T83 and T86, and a genuine two-cell sample realizing all
hypotheses and saturation for T85. It also constructs T82's full kernel witness.
`scratch/T84Witness.lean` reconstructs the twelve-unit sample, checks all cell
summaries, identifies the grouped sample likelihood and computes the two
estimator values and the gap directly. These witness checks import definitions
without using the Challenge theorem stubs.
