import SAP.P024.Defs.WholeW2
import SAP.P024.Defs.WholeW3
import SAP.P024.Defs.WholeW1
import SAP.P024.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P024-T1; p. 174 (PDF p. 8), first paragraph of the single-medium crossover section.
The four-period randomized-onset witness establishes the canonical counterexample.
It refutes the reading that design-unbiased effect estimation or valid sharp-null
inference under randomized timing requires a constant untreated outcome path.
The fixed nonconstant trend admits the stated unbiased estimator, variance, and
exactly calibrated valid sharp-null test. -/
theorem SAP.P024.T1 : SAP.P024.T1Statement := by sorry

/-- P024-T2; corrected timing sentence, p. 174 (PDF p. 8).
Current-exposure overlap permits unbiased timing estimation and fixed sharp-null paths
permit valid uniform randomization tests, while the actual raw before-after contrast is biased. -/
theorem SAP.P024.T2 : SAP.P024.T2Statement := by sorry

/-- P024-T4; consistency sentence, p. 171 (PDF p. 5).
The dominant-cluster populations establish the canonical counterexample.
They refute the reading that a growing number of independently assigned clusters
alone, without a condition controlling their population shares, guarantees consistency
of the individual-level difference in means. The theorem includes the independent
and complete-design formulas, limits, conditional mean, population shares, and
six-cluster numerical checks. -/
theorem SAP.P024.T4 : SAP.P024.T4Statement := by sorry

/-- P024-T5; corrected consistency sentence, p. 171 (PDF p. 5).
Uniformly bounded individual potential outcomes, a common cluster treatment
probability uniformly bounded away from zero and one, and a vanishing largest
cluster share imply consistency: one fixed eta > 0 satisfies
eta <= p_K <= 1-eta for every K. This holds under
independent assignment or complete cluster randomization. The squared-share
condition is equivalent. Bias can still be appreciable with a few dozen unequal
clusters: a 24-cluster, 12-treated example with outcomes in [0,1] has effect 2/3,
mean estimate 23/57 and bias -5/19, of magnitude greater than 1/4. Without no
dominance, bounded outcomes and interior independent assignment do not suffice:
the dominant-cluster sequence has error probability tending to one for every
empty-arm extension. Populations, effects, and probabilities may change, while
the outcome bound and probability margin remain uniform over the sequence. -/
theorem SAP.P024.T5 : SAP.P024.T5WholeStatement := by sorry

/-- P024-T6; between-subjects design, p. 170 (PDF p. 4).
For explicit subclasses of the paper's equal-probability individual-assignment description,
the treatment-arm outcome mean minus the control-arm outcome mean is unbiased
for the finite subject-pool average effect. Potential outcomes are fixed,
assignment is implemented as planned, all outcomes are observed, there is no
interference, and assignment is the sole randomness. The design is complete
individual randomization with 1 <= m < N, or independent common-p individual
assignment, 0 < p < 1, conditional on both arms being nonempty. The result
also covers fixed counts almost surely with actual common probabilities m/N,
and every nonempty-arm law uniform conditional on the realized count.
The Bernoulli conditioning event has positive probability; its conditional
masses are the parent masses divided by that probability. Population sizes
are at least two and both realized arms have positive denominators.
The usual measure-theoretic conditions are assumed; all laws, outcomes, and
expectations in this finite formulation are measurable and finite.
Restriction: require either a count m fixed almost surely with 0 < m < N and
every actual unit marginal m/N, or a law on proper nonempty subsets uniform
conditional on its treatment count. Complete randomization and independent
common-p assignment conditioned on nonempty arms are included. Arbitrary
equal-marginal dependent laws with varying treatment counts are not covered. -/
theorem SAP.P024.T6 : SAP.P024.T6WholeStatement_W2 := by sorry

/-- P024-T7; corrected conditional clustering component, p. 171 (PDF p. 5),
with the individual-level estimand on p. 172 (PDF p. 6).
For K >= 2 independent common-p Bernoulli cluster assignments, 0 < p < 1,
the nonempty-arm event has probability 1-p^K-(1-p)^K > 0, for arbitrary
positive cluster sizes. Conditional masses are the actual parent masses divided
by that probability. Equal positive cluster sizes give unbiased individual
difference in means conditionally on this event, and each allocation equals
the difference of the two cluster means. For sizes (1,2), zero control outcomes
and treatment outcomes zero in the small cluster and one in the large cluster,
the fair parent law instead gives effect 2/3 and conditional mean 1/2, with the
two conditional allocations equiprobable and estimates zero and one. Every
empty-arm extension is allowed. Independence refers to the parent law. -/
theorem SAP.P024.T7 : SAP.P024.T7WholeStatement := by sorry

/-- P024-T8; fixed-quota specialization of weighted blocked estimation,
p. 173 (PDF p. 7), and Note 4, p. 177 (PDF p. 11).
The actual-probability Horvitz–Thompson estimate equals on every allocation the
population-share weighted average of ordinary within-block differences in means,
and both estimators are unbiased for the individual average effect among randomized units.
Restriction: each predetermined block has a fixed quota 0 < m_b < N_b on every
assignment, and every unit in that block has actual treatment probability m_b/N_b.
These are additional design assumptions relative to the canonical statement;
variable block treatment counts and unequal within-block propensities are not covered.
Balanced nonuniform laws and dependent assignments across blocks are allowed.
Potential outcomes are fixed, depend only on own treatment, and are all observed.
Excluded units are outside the estimand. All population, arm-count and probability
denominators are positive; all expectations are finite sums on a finite design. -/
theorem SAP.P024.T8 : SAP.P024.T8WholeStatement_W3 := by sorry
