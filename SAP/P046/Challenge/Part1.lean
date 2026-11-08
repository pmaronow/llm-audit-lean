import SAP.P046.Defs
import SAP.P046.Defs.WholeW2
import SAP.P046.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P046

/-- P046-T1; Proposition 3, p. 7 (PDF p. 6), Appendix A, p. 15 (PDF p. 14).
The specified continuous counterexample satisfies all standing assumptions. Its three
category probabilities and joint count law, exact sample-statistic reductions, equivalent
strict exclusion tests, 5151 feasible states and 1946 failures give the exact recorded
noncoverage probability, exceeding 119/10^9 and alpha=10^(-7). The closed interval
undercovers and the non-strict population tail also exceeds alpha. The decimal probability
is specified by its exact rational value. Usual measure-theoretic conditions are assumed. -/
theorem SAP.P046.T1 : SAP.P046.T1WholeStatement := by sorry

/-- P046-T2; Appendix A, proof of Proposition 3, p. 16 (PDF p. 15).
The specified valid continuous design has mu=1/2 and a covariate event of probability
2^(-100). For every covariate vector in this event and every treatment vector, the design
outcomes, HT and the conditional centre mu_W vanish, and the absolute population error
is 1/2. Almost everywhere on the event the actual conditional mean is zero, distinct
from mu; the conditional tail is one while the full printed right side is 1/20.
Usual measure-theoretic conditions are assumed; conditional expectations are asserted
only up to almost-everywhere equality. -/
theorem SAP.P046.T2 : SAP.P046.T2WholeStatement := by sorry

/-- P046-T3; corrected Proposition 3, p. 7 (PDF p. 6), proof pp. 15–16
(PDF pp. 14–15). The two-error and known-bound intervals have population coverage
at least nominal. All corrected proof steps are included: conditional factorization and
means, conditional independence and ranges, fixed and covariate-measurable random
threshold bounds, i.i.d. regression sampling, triangle inclusion and union bound, strict
positivity radius bound and inverse-square-root width rate, and the alternative's i.i.d.
summands and Hoeffding calculation. Usual measure-theoretic conditions are assumed. -/
theorem SAP.P046.T3 : SAP.P046.T3WholeStatement := by sorry

/-- P046-T4; Proposition 4(c), p. 8 (PDF p. 7), treated-case weighted-loss reading.
The specified continuous counterexample has exact balanced fits g_0, with all training
loss decompositions and minimizer characterizations, the unique population minimizer,
the scalar summand table, event probabilities and moments, and bounded i.i.d. summands.
Both finite-sample variances and Gaussian limits reverse the printed efficiency ordering.
Zero is outside the family and its weighted L2 closure; the potential-outcome variance
and positive risk gap are explicit. Usual measure-theoretic conditions are assumed;
sample sizes in estimator formulas are positive. -/
theorem SAP.P046.T4 : SAP.P046.T4WholeStatement := by sorry

/-- P046-T5; corrected Proposition 4(c), p. 8 (PDF p. 7).
The zero-benchmark square-integrable working-family theorem and the family-free direct
risk-comparison theorem give both Gaussian limits and the efficiency ordering.
The genuine extended L2 errors converge in probability; individual fitted functions
may have infinite error on events whose probabilities vanish. Finite limit risk implies
square integrability. The fixed-summand variance identity and equivalence of weighted
and ordinary L2 norms are included. Usual measure-theoretic conditions are assumed;
functions are measurable and Gaussian variance zero denotes a point mass. -/
theorem SAP.P046.T5 : SAP.P046.T5WholeStatement := by sorry

/-- The printed claim is false: P046-T6; Proposition 3, p. 7 (PDF p. 6), Appendix A,
pp. 15–16 (PDF pp. 14–15).
The universally quantified population-centred tail bound with the printed random radius
fails for a valid study. -/
theorem SAP.P046.T6 : T6Statement := by sorry

/-- P046-T7; Proposition 2, p. 6 (PDF p. 5), supporting text p. 7 (PDF p. 6).
HT is integrable and unbiased, uniformly root-n consistent for each common positive
positivity constant, and asymptotically normal with the stated summand variance,
including the variance-zero convention. -/
theorem SAP.P046.T7 : T7Statement := by sorry

/-- P046-T8; Proposition 4(a), p. 8 (PDF p. 7), Appendix A, p. 16 (PDF p. 15).
The cross-fitted regression estimator is finite-sample unbiased whenever its
expectation exists, including cancellation between nonintegrable predictions.
The consistency identity, three-term expansion, HT expectation chain,
opposite-fold conditional independence, and fitted-term expectation and
cancellation chains are included. Component expectation chains are asserted
when their individual expectations exist. The usual measure-theoretic
conditions are assumed. Arbitrary deterministic folds include roughly equal folds. -/
theorem SAP.P046.T8 : SAP.P046.T8WholeStatement := by sorry

/-- P046-T9; Proposition 4(b) and 4(d), p. 8 (PDF p. 7).
For balanced deterministic opposite-fold fits, mean-square convergence to any
two fixed L2 functions gives root-n consistency. L2 consistency in probability
for the true regression gives the normal limit with variance equal to the
numerical Hahn efficiency bound, including its zero-variance convention.
Extended squared errors allow infinite-error events of vanishing probability;
no finite-sample L2 condition is added on the fitted functions. The usual
measure-theoretic conditions are assumed. -/
theorem SAP.P046.T9 : SAP.P046.T9WholeStatement := by sorry

/-- P046-T10; Proposition 1, p. 6 (PDF p. 5).
Every measurable observed-data estimator sequence has a positive error threshold with
failure probability bounded away from zero along arbitrarily large sample sizes and valid
population laws, so uniform consistency over the unrestricted class fails. -/
theorem SAP.P046.T10 : T10Statement := by sorry
