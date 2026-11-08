import SAP.P001c.Defs.WholeW2
import SAP.P001c.Defs.WholeW1
import SAP.P001c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P001-T49; p. 87 (PDF p. 105), opening paragraph and Theorems 2.3.7–8;
Definition 2.3.6, p. 86 (PDF p. 104).
Every affine predictor has its intercept as its value at zero and each slope as
its unit coordinate increment and partial derivative. Every MSE-minimizing affine
predictor has a residual with zero mean, zero coordinate-product expectations,
and zero coordinate covariances, including singular designs and zero regressors. -/
theorem SAP.P001c.T49 : SAP.P001c.T49WholeStatement := by sorry

/-- P001-T50; Example 3.1.3, p. 94 (PDF p. 112), and the functional and
plug-in displays, pp. 118–119 (PDF pp. 136–137).
Finite-population PMFs and moments, the example with variance 17/2, the minus-sign
variance functional and the empirical mean and variance satisfy the corrected formulas. -/
theorem SAP.P001c.T50 {Ω : Type*} [mΩ : MeasurableSpace Ω] : SAP.P001c.T50Statement Ω := by sorry

/-- P001-T51; p. 99 (PDF p. 117), Definition 3.2.6 and the following paragraph.
The bad-event limit zero, within-epsilon limit one, and every eventual probability
lower bound in [0,1) are equivalent. The measurable singleton-indicator sequence
under the geometric law converges in probability to zero, but its within-1/2
probability is 1-2^(-(n+1)) at every n, so the printed endpoint p=1 fails. -/
theorem SAP.P001c.T51 : SAP.P001c.T51WholeStatement := by sorry

/-- P001-T52; Theorem 3.2.9 and footnote 12, p. 102 (PDF p. 120).
Indicator expectations equal measurable-event probabilities and each fixed empirical
CDF ordinate consistently estimates its population ordinate under IID sampling. -/
theorem SAP.P001c.T52 {Ω : Type*} [mΩ : MeasurableSpace Ω] : SAP.P001c.T52Statement Ω := by sorry

/-- P001-T53; proof of Theorem 3.2.19, p. 107 (PDF p. 125);
Theorem 3.2.19, p. 106 (PDF p. 124), and Theorem 3.2.8, p. 100 (PDF p. 118).
The normalized masses 7/8^(k+1) at 2^k are realized by an infinite IID sequence
with mean 7/6, second moment 7/4, variance 7/18, and infinite fourth moment.
Its squares are integrable but have infinite extended variance, refuting the
printed proof's inference of the finite-variance WLLN hypothesis for the squares.
The finite-variance WLLN and the sample-variance expectation and consistency
theorems still hold, in particular for this sequence. -/
theorem SAP.P001c.T53 : SAP.P001c.T53WholeStatement := by sorry

/-- P001-T54; Theorem 3.2.19 and its proof, pp. 106–107 (PDF pp. 124–125);
Theorem 3.2.7, p. 100 (PDF p. 118).
The WLLN holds for IID integrable variables, and the two-variable continuous
mapping theorem holds without independence. Under finite positive population
variance, the sample mean and sample second moment converge to their population
values; the plug-in variance has expectation (n-1)/n times population variance
and converges to that variance. Only a second moment is needed. -/
theorem SAP.P001c.T54 : SAP.P001c.T54WholeStatement := by sorry

/-- P001-T55; Definition 3.2.32 and footnote 23, pp. 113–114 (PDF pp. 131–132);
Definition 3.2.20, p. 107 (PDF p. 125), and Theorem 3.2.33, p. 114 (PDF p. 132).
With the estimator's hats restored, variance and standard-error consistency are equivalent
to their centered forms and to each other. For iid observations of finite positive variance,
the unbiased sample variance is n/(n−1) times the plug-in variance; divided by n it is an
unbiased estimator of the sample mean's variance, for n at least two. The exact identity
n Var(sample mean)=Var(X), the root-n limit, both consistencies and both centered forms hold.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001c.T55 : SAP.P001c.T55WholeStatement := by sorry

/-- P001-T56; Theorem 3.3.6 and footnote 31, p. 120 (PDF p. 138), read with
Definition 3.2.28, p. 112 (PDF p. 130).
The constant and quadratic Bernoulli functionals give degenerate plug-in limits,
supporting the canonical counterexample to the book's positive-variance conclusion.
The constant functional has zero derivative and no positive-variance normal limit,
while the quadratic Bernoulli plug-in has the exported differentiability, exact
second-moment formula and degenerate probability limit.
Restriction: Omit the explicit constant-statistic and normal CDF values and continuity
at zero; for the quadratic example omit separate assertions of boundedness and
nonconstancy, F(0)=1/2, identification of its derivative as zero, the binomial law and
the scalar second-moment formula's convergence to zero. No IID realization is constructed. -/
theorem SAP.P001c.T56 {Ω : Type*} [mΩ : MeasurableSpace Ω] : SAP.P001c.T56Statement Ω := by sorry

/-- P001-T57; Theorem 3.3.6 and footnote 31, p. 120 (PDF p. 138);
Definition 3.2.28, p. 112 (PDF p. 130), with the non-degeneracy correction.
Every real IID empirical-CDF process has a tight Brownian-bridge outer limit in
the sup norm. A CDF-domain functional Hadamard differentiable on any subspace
carrying that bridge almost surely has a centered Gaussian derivative limit,
possibly degenerate, with finite variance. Its measurable scalar plug-in converges
in distribution to that law. Positive derivative variance gives asymptotic
normality with phi squared equal to that variance; zero variance gives a point mass.
No closedness of the tangent subspace or moment assumption on the observations
is required. -/
theorem SAP.P001c.T57 : SAP.P001c.T57WholeStatement := by sorry
