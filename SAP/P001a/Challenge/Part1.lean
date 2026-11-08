import SAP.P001a.Defs
import SAP.P001a.Defs.WholeW1
import SAP.P001a.Defs.WholeW2
import SAP.P001a.Defs.WholeW3
import SAP.P001a.Defs.WholeW4

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5 u6 u7 u8

/-- The printed claim is false: A finite-moment geometric law has uniformly vanishing scaled CDF perturbations with unit mean difference quotients.
P001-T1; pp. 118, 120 (PDF pp. 136, 138), Section 3.3.1 and footnote 31.
Restriction: States the normalized finite-second-moment mass/CDF witness, mean quotients, variance limit and uniform vanishing directions. Does not separately assert the base variance value, explicit equality of the two supports, the shifted-CDF/decomposition identities, the exact sup-norm equality or its finite 1/n bound, or a generic negation of Hadamard differentiability. -/
theorem SAP.P001a.T1 : SAP.P001a.T1Statement := by sorry

/-- P001-T2; pp. 109, 119–120 (PDF pp. 127, 137–138).
The empirical mean equals the sample mean and has the finite-positive-variance Gaussian limit, while a finite-variance geometric witness violates the zero-direction requirement for a Hadamard derivative. -/
theorem SAP.P001a.T2 : SAP.P001a.T2Statement.{u1} := by sorry

/-- P001-T3; pp. 166–168 (PDF pp. 184–186), Definition 4.3.7.
The fixed independent gap-uniform law has continuously differentiable conditional-mean extensions with arbitrary derivatives at its mean, refuting the reading that all global CEF extensions must determine the same derivative there even outside the printed CEF domain.
Restriction: States the fixed gap-support extension witness and negates the stronger global-extension contract pda_at_mean_printed_contract. Drops the claim of refuting the printed PDA definition under the domain/existence reading: the mean in this example is outside the positive-density CEF domain, and the unequal derivatives are those of global extensions. No counterexample with an admissible PDA evaluation point is asserted. -/
theorem SAP.P001a.T3 : SAP.P001a.T3Statement := by sorry

/-- P001-T4; pp. 167–168 (PDF pp. 185–186), Definition 4.3.7.
Continuous local CEF representatives agree on an open set whenever they agree
Lebesgue almost everywhere there. Equality requires no derivative. Every existing
coordinate derivative at the covariate mean transfers, with the same value.
The positive-PDF neighborhood condition implies this version independence but
is not necessary, as the uniform PDF with a hole at its mean demonstrates. -/
theorem SAP.P001a.T4 : SAP.P001a.T4WholeStatement := by sorry

/-- P001-T5; pp. 168–169 (PDF pp. 186–187), Definition 4.3.9.
The squared-residual polynomial sieve with J_n = floor(n^(3/4)) satisfies J_n → infinity
and J_n/n → 0. For iid independent U[0,1] covariates and standard Gaussian outcomes,
the CEF is smooth and zero, all moments exist, and least-squares fits with Borel measurable
coefficients exist. Every such fit has, for every 0 < delta ≤ 1 and epsilon > 0, local squared L2
error exceeding epsilon with lower limiting probability at least 1/2 along n = t^4;
it therefore fails local L2 consistency on a region of positive probability mass.
For a separate degree-floor(sqrt(n)) sequence, fits with Borel measurable coefficients
also exist, and every such sequence satisfies Pr[|fit_(t^2)(1)| > 1/4] ≥ 1/4 for every
integer t ≥ 2, including experiments with no coupling across sample sizes. Thus the
printed rate condition is insufficient for the stated local
consistency; no assertion about consistency at slower degrees is made. The usual
measure-theoretic conditions are assumed. -/
theorem SAP.P001a.T5 : SAP.P001a.T5WholeStatementW4 := by sorry

/-- P001-T6; pp. 168–169 (PDF pp. 186–187), Definition 4.3.9.
Polynomial least squares admits a measurable minimizing selection, including
singular designs. On compact support a continuous CEF and bounded conditional
variance give L2 consistency under growing degree, vanishing dimension/sample
ratio and a stable population-normalized Gram matrix. The attained support
supremum gives the general envelope rate. For uniform covariates on every
nondegenerate compact interval the envelope is at most K², the Euclidean
operator-norm deviation probability is at most 4(K³−K)/n, and the cubic rate
suffices for Gram stability. -/
theorem SAP.P001a.T6 : SAP.P001a.T6WholeStatement := by sorry

/-- The printed claim is false: The clipped pooled Bernoulli MLE converges to the marginal success probability instead of the fixed-covariate KL targets.
P001-T7; p. 195 (PDF p. 213), Theorem 5.2.8.
Restriction: States the four-atom wrong-target example, unique clipped likelihood maximization, finite probability bounds, incompatible conditional targets and the changed-covariate-marginal limit. Omits the displayed KL derivative formulas and the exact positive averaged-KL gap (1/2) log(4/3). -/
theorem SAP.P001a.T7 : SAP.P001a.T7Statement.{u1,u2} := by sorry

/-- P001-T8; pp. 195–196 (PDF pp. 213–214), Theorem 5.2.8.
Averaged conditional KL equals finite iterated conditional entropy minus finite
expected log density. Its minimizers are precisely the expected-log maximizers.
Uniform convergence in probability of the positive-sample log criterion and
vanishing approximate maximization error give consistency at every separated
maximum; exact product maximizers are included. Compactness and a continuous
unique maximum imply separation. Consistency does not require finite entropy
or finite KL. A true model has zero KL, and uniqueness identifies its parameter.
All conditional laws are probability kernels; the reference measure is arbitrary. -/
theorem SAP.P001a.T8 : SAP.P001a.T8WholeStatement := by sorry

/-- The printed claim is false: The unrestricted three-component mixture likelihood is unbounded along the specified normal-scale collapse path on the three-point sample.
P001-T9; pp. 198–201 (PDF pp. 216–219), Section 5.2.5 and Example 5.2.11.
Restriction: States unboundedness on the exact three-point collapse path and absence of an admissible maximizer. Omits the displayed componentwise and C/scale lower bounds, the prescribed scale C/(|B|+1), and the general positive-sample path and bound (general positive-sample unboundedness is packaged under T10). -/
theorem SAP.P001a.T9 : SAP.P001a.T9Statement := by sorry

/-- P001-T10; pp. 198–201 (PDF pp. 216–219), Section 5.2.5 and Example 5.2.11.
The unrestricted mixture has no likelihood maximizer on any nonempty positive sample, while every nonempty stated compact restriction has a continuous likelihood attaining its maximum. -/
theorem SAP.P001a.T10 : SAP.P001a.T10Statement := by sorry

/-- P001-T11; pp. 198–199 (PDF pp. 216–217), Section 5.2.5.
The zero-weight mixture counterexample refutes the reading that representation by a proper subset of components alone ensures consistency of the displayed full-vector MLE: two distinct full parameters produce identical iid experiments, so no estimator is consistent at both, despite attained likelihood maxima.
Restriction: States the normalized identical iid experiments, compactness, likelihood continuity and attainment, finite two-target estimation bound, impossibility for every estimator and an attained MLE selection that fails at a truth. The two truths are nonidentified zero-weight boundary parameters. Does not refute the contextual claim with the identification and uniqueness conditions of Theorem 5.2.6 retained, and establishes no regular-efficiency counterexample at an interior truth with nonsingular full-parameter information. Omits the separate uniform likelihood upper bound of one and the binomial-count rewriting of the sample mass. -/
theorem SAP.P001a.T11 : SAP.P001a.T11Statement := by sorry

/-- P001-T12; p. 199 (PDF p. 217), Section 5.2.5, corrected subset sentence.
A freely variable zero-weight component makes the full vector unidentified:
the densities, observation laws, every iid sample law and finite expected logs
agree, and no estimator is consistent at both distinct vectors. Compactness,
continuity, unique identification and uniform positive-sample log-criterion
convergence imply consistency of every measurable maximizer. Under the explicit
common-set C2, centered L2 score, positive information, information identity,
continuous integrable expected Hessian and uniform sample-Hessian conditions,
each such interior ML maximizer has root-n limit N(0,I inverse). Separately, QMD
of the normalized fixed-dominator model implies that every regular asymptotically
linear estimator's influence covariance minus I inverse is positive semidefinite.
QMD is used only for this information bound. The argmax and local-normality
principles are given for arbitrary finite real criteria and specialize to the
fitted mixture; the information principle allows arbitrary dominating measures.
Thus unused free coordinates must be removed before a full-vector assertion. -/
theorem SAP.P001a.T12 : SAP.P001a.T12WholeStatement := by sorry

/-- P001-T13; p. 233 (PDF p. 251), footnote 15 and Table 6.3.1.
The explicit unbiased hot-deck design refutes the universal bias-only calibration reading: its bootstrap-variance expectation limit is strictly below its sampling-variance limit, and its bootstrap variance is inconsistent.
Restriction: States the explicit hot-deck mean and scaled-variance limits, positive bootstrap gap, variance inconsistency, uniform second-moment bound and occupancy inequalities. Adds finite second-moment premises for every sample statistic and bootstrap variance to exclude undefined expectations. Omits separate MAR/MCAR, overlap and continuous-score assertions, root-n tightness, uniform integrability as a predicate, and the bootstrap-standard-error inconsistency conclusion. Does not claim to evaluate the reported empirical numbers or the literal hedged assurance. -/
theorem SAP.P001a.T13 : SAP.P001a.T13Statement.{u1,u2} := by sorry

/-- P001-T14; p. 233 (PDF p. 251), footnote 15.
The explicit hot-deck design has inconsistent bootstrap variance and exact conditional variance equal to the sum of squared donor-reuse weights divided by sample size squared.
Restriction: States the explicit hot-deck bootstrap failure and the exact conditional weighted-sign and variance identities. Adds finite second-moment premises for the sample statistic and bootstrap variance. Omits separate MAR/MCAR, overlap, continuous-score and root-n-tightness assertions and any conclusion about confidence-interval calibration or the reported standard error. -/
theorem SAP.P001a.T14 : SAP.P001a.T14Statement.{u1} := by sorry

/-- P001-T15; pp. 264, 279–280 (PDF pp. 282, 297–298), Section 7.2.4 and footnote 20.
The displayed matching design has an inconsistent true-score bootstrap variance and a consistent additive score-intercept estimate.
Restriction: Only the displayed mathematical matching example is stated: true-score bootstrap failure and consistency of the estimated intercept. Adds finite second-moment premises for the statistic and bootstrap variance. Does not refute the literal hedged footnote or the reported numbers, does not use the wrong_credit row, and omits the estimated-score statistic failure, score-match equalities, explicit design admissibility predicates, root-n tightness, gap decomposition and standard-error conclusion. -/
theorem SAP.P001a.T15 : SAP.P001a.T15Statement.{u1,u2} := by sorry

/-- P001-T16; pp. 264, 279 (PDF pp. 282, 297), Section 7.2.4 and footnote 20.
Estimated additive scores preserve the matching statistic and its bootstrap failure, and squared control-reuse weights give the conditional variance.
Restriction: States estimated-score bootstrap failure, intercept consistency, equality of all sample and resample matches/statistics, and the conditional weighted-sign variance identity. Adds finite second-moment premises for the estimated statistic and bootstrap variance. Omits the separate claim that score consistency alone need not give a root-n rate, the first-step-adjusted parametric variance estimator and confidence-interval discussion, separate design admissibility predicates, root-n tightness, and a bootstrap-standard-error conclusion. -/
theorem SAP.P001a.T16 : SAP.P001a.T16Statement.{u1,u2} := by sorry

/-- P001-T17; p. 270 (PDF p. 288), Section 7.2.8.
The twelve-atom null law has a baseline-first causal realization with W unchanged
by treatment, the displayed conditional masses, overlap, conditional variance,
eight population moments, and unique restricted and full population fits.
For every iid realization, the conventional F and HC0 Wald statistics have the
displayed positive almost-sure limits after division by n, diverge, and reject
with probability tending to one at the stated critical values. An actual
240-observation exact-count sample exists; every ordering of it has the stated
OLS coefficients, residual sums and F=5056/177, rounding to 28.6.
The infinite iid experiment exists, so this is a realizable counterexample to
nominal size under conditional independence alone. -/
theorem SAP.P001a.T17 : SAP.P001a.T17WholeStatement := by sorry

/-- P001-T18; p. 270 (PDF p. 288), Section 7.2.8.
Conditional independence and a linear treatment CEF preserve that CEF after
adding placebo covariates and make their uniquely optimal population
coefficients zero. Under iid sampling and the stated second moments and Gram
rank, actual OLS has its sandwich Gaussian limit and n times residual HC0
converges to that covariance. Every nonempty tested block with nonsingular
limiting covariance has a calibrated chi-square Wald test and its inverted
joint coefficient region. Without the CEF specification, zero placebo
coefficients mean no added linear predictive content; the explicit independent
placebo example instead has slope 4/17. -/
theorem SAP.P001a.T18 : SAP.P001a.T18WholeStatement := by sorry

/-- The printed claim is false: The positive countable joint masses have equal complete discrete arm supports and propensities tending to the boundary without a uniform positive margin.
P001-T19; pp. 271–272 (PDF pp. 289–290), Section 7.3.
Restriction: States the two summable positive countable cell-mass sequences with arm totals one half, pointwise interior propensities and no uniform positivity margin. Omits the explicit 4/(k+6) propensity rate and ceiling-selected covariate. Positive cells and equal discrete supports are represented by the mass sequences; no separate support predicate is asserted. -/
theorem SAP.P001a.T19 : SAP.P001a.T19Statement := by sorry

