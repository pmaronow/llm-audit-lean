import SAP.P015a.Defs.WholeW1
import SAP.P015a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

/-- P015-T1; p. 261 (PDF p. 12); positivity display on p. 261 (PDF p. 12); Expression (8) on p. 255 (PDF
p. 6).
The full canonical rare-overlap counterexample holds: at epsilon = 1/1000000, the observed-outcome
IPW estimator is unbiased and consistent with the stated exact moments and deviation bounds, and the
actual nonsingular population OLS coefficient is the effective causal mean.
The family refutes treating approximately no weight as a positive threshold for failure of strict
endpoint positivity. The estimator moments, every-sample-size bounds, and pointwise consistency are
at epsilon = 1/1000000; positivity and arbitrarily small effective-profile mass are asserted
separately for every 0 < epsilon < 1/2. -/
theorem SAP.P015a.T1 : SAP.P015a.T1Statement := by sorry

/-- P015-T2; p. 261 (PDF p. 12), right column; positivity display on p. 261 (PDF p. 12); $\tau_i(d, d')$
and (11) on p. 260 (PDF p. 11).
The full canonical four-atom counterexample holds: every regression weight is positive, treatment 1
is absent at profile 1, and two observationally identical outcome worlds have different nominal and
effective effects and no common consistent observed-data estimator.
The counterexample concerns positivity for a fixed distinct treatment pair at every
effective-population profile. It retains positive within-profile variance, so it does not refute
positivity understood only as some within-profile treatment variation. -/
theorem SAP.P015a.T2 : SAP.P015a.T2Statement.{u} := by sorry

/-- P015-T3; p. 261 (PDF p. 12); estimated weights $\hat w_i = \tilde D_i^2$ on p. 255 (PDF p. 6).
The full canonical finite-sample counterexample holds: a sample of probability 1/256 from a binary
population with positive overlap has fitted weights (0,0,1/4,1/4), nonsingular controls Gram matrix,
and full-regression Gram determinant 2.
The counterexample concerns inferring population positivity failure from exactly zero estimated
sample-profile weights. Its population conditional variances remain 1/4; it does not contradict the
exact-zero implication for population profile weights. -/
theorem SAP.P015a.T3 : SAP.P015a.T3Statement := by sorry

/-- P015-T13; p. 265 (PDF p. 16), left column. The corrected inverse-logit derivative and affine Taylor
polynomial hold, and the printed fraction differs from the derivative at probability one half. -/
theorem SAP.P015a.T13 : SAP.P015a.T13Statement := by sorry

/-- P015-T12; p. 257 (PDF p. 8), left column. At logit(p), for 0 < p < 1, the
inverse-logit's first Taylor polynomial is p + p(1-p)(a-logit(p)), with a local
quadratic remainder. The complex Taylor radius is exactly sqrt(logit(p)^2+pi^2).
On every smaller real closed interval the Taylor errors have the stated uniform
Cauchy bound, using the attained finite maximum on an intermediate complex circle,
and this bound tends to zero. The explicit 200-observation, full-rank binary data
have a unique finite logistic ML estimate with both predictors outside the disk;
every Taylor degree has probability error at least 49/100 there. No accuracy of
coefficients or weights is asserted. -/
theorem SAP.P015a.T12 : SAP.P015a.T12WholeStatement := by sorry

/-- P015-T8; pp. 264–265 (PDF pp. 15–16); main text pp. 256–257 (PDF pp. 7–8).
The Bernoulli gradient is the residual score multiplied by m'/(m(1-m)); an admissible
ML fit satisfies its zero equation. Logistic has multiplier one. Common-dispersion
scalar canonical families have gradient s^-1 times the residual score, with mean κ'
for their normalized response laws and locally analytic cumulants, including
Bernoulli logit and Poisson log link.
Probit has the nonconstant normal-density multiplier and the explicit residual-root
counterexample. The exact first Taylor polynomial of the full score includes h' B;
division by a nonzero h gives its linearized equation, while mean-only linearization
gives the OLS normal equation after an invertible affine reparameterization. The
equations coincide when h'=0 or Bδ=0; logistic and symmetric probit give the first
case, and the square-link causal model exhibits a discrepancy in general. These
are Taylor-polynomial identities. No nonlinear-score quadratic remainder or blanket
extension to ordered, multinomial, or duration models is asserted. The Cox score
illustrates the additional risk-set terms and their dependence on the risk sets. -/
theorem SAP.P015a.T8 : SAP.P015a.T8WholeStatement := by sorry

/-- P015-T5; pp. 264–265 (PDF pp. 15–16); main text pp. 256–257 (PDF pp. 7–8).
The specified 72-observation odds-link data have admissible means, full rank, a zero substituted
residual equation, multiplier 1/eta, a genuine nonzero score, likelihood directional derivatives,
and nonmaximality at the displayed parameter.
This realizes the whole canonical 72-observation residual-root/nonmaximum example. It refutes the
reading that every root of the inverse-link-substituted residual equation is an ML estimate. It does
not contradict the printed necessary implication that an ML estimate solves that equation. -/
theorem SAP.P015a.T5 : SAP.P015a.T5Statement := by sorry

/-- P015-T6; pp. 264–265 (PDF pp. 15–16); main text pp. 256–257 (PDF pp. 7–8).
The specified 48-observation probit data have full rank, a well-defined normal quantile, a zero
substituted residual equation, the exact genuine score with treatment coordinate strictly above
13/625, likelihood directional derivatives, and nonmaximality at the displayed parameter.
This realizes the whole canonical 48-observation probit residual-root/nonmaximum example. It refutes
the reading that every substituted residual root is an ML estimate. It does not contradict the
printed necessary implication that an ML estimate solves the substituted equation. -/
theorem SAP.P015a.T6 : SAP.P015a.T6Statement := by sorry

/-- P015-T7; p. 257 (PDF p. 8); pp. 264–265 (PDF pp. 15–16).
At the common outcome mean 1/4, the a = 1/16 and a = 0 laws have unique admissible
expected-likelihood maximizing branches near epsilon = 0 with treatment derivatives
120/119 and 1; the first law has OLS treatment coefficient epsilon. The theorem includes
the moment and score derivatives and the treatment-preserving change of basis.
Restriction: Retains all specified finite-law, causal-model, moment, score, maximizing-branch, OLS and
same-mean derivative facts. The square-link family is fitted as a working model without
requiring correct conditional-mean specification. At a = 1/16 and epsilon = 0, the true
probabilities at X = -1, 0, 1 are 5/16, 1/8, 5/16, while the likelihood maximizer fits 1/4.
Omits a refutation of Appendix C's first-order scaling assertion under its correctly specified
conditional-probability model reading; the derivative discrepancy concerns population
expected-likelihood projections allowing misspecification. -/
theorem SAP.P015a.T7 : SAP.P015a.T7Statement := by sorry

/-- P015-T16; p. 259 (PDF p. 10), left column. The 0.077 log-point conversion is about eight percent,
exponentiated fitted contrasts equal the exponentiated coefficient, and the four-observation OLS
example separates this factor from arithmetic mean spending. -/
theorem SAP.P015a.T16 : SAP.P015a.T16Statement := by sorry

/-- P015-T4; p. 261 (PDF p. 12); positivity display on p. 261 (PDF p. 12); Expression (8) on p. 255 (PDF
p. 6).
For discrete covariates and finite second moments, endpoint positivity implies positive conditional
variance, zero variance is degenerate, and the binary equivalences and effective-law reversal hold,
with the explicit multivalued-support and fitted-zero examples.
Restriction: Retains formal clauses (i)-(iii), the multivalued-support and fitted-zero
counterexamples, and the rare-overlap positivity and arbitrarily-small-effective-mass family for
every 0 < epsilon < 1/2. Estimator unbiasedness, moments, deviation bounds, and consistency are
asserted only at epsilon = 1/1000000, rather than jointly with arbitrarily small effective-profile
mass. Omits the empirical Jensen country-contribution assertion. -/
theorem SAP.P015a.T4 : SAP.P015a.T4Statement.{u,v} := by sorry

/-- P015-T19; p. 255 (PDF p. 6), left column. For general measurable covariates and square-integrable
treatment, the conditional mean of the squared residual is conditional variance and has the usual
binary propensity formula. -/
theorem SAP.P015a.T19 : SAP.P015a.T19Statement.{u,v} := by sorry
