import SAP.P029b.Defs
import SAP.P029b.Defs.WholeW1
import SAP.P029b.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P029b

/-- P029-T14; p. 500, Assumption 2; pp. 496–497, Section 3.1.
With boundary probabilities allowed, the saturated ordered binomial likelihood has
the unique separate-rate or pooled maximizer and compliance score max(r1-r0,0).
The interior nested parameters, finite bias and extreme-event probability,
contraction and tail bound, per-stratum and simultaneous finite-stratum consistency,
and one-sided unbiasedness (requiring only a nonempty treated arm) all hold.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P029b.T14 : SAP.P029b.T14WholeStatement := by sorry

/-- P029-T15; p. 498, footnote 6.
The constant-score counterexample satisfies the five IV assumptions and Assumptions
1–3, with receipt-arm means 3/4 and 1/4 and ATE and population ICSW equal to one.
Both inverse empirical-CDF and type-7 quantiles of its nonempty half-score vectors
exist and equal one half, including at every positive power level n^(-alpha).
The cutoff therefore does not tend to zero; no scores or weights change.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P029b.T15 : SAP.P029b.T15WholeStatement := by sorry

/-- P029-T16; p. 498, footnote 6, corrected.
The type-7 changed count is at most floor(1+(n-1)lambda), and its fraction is at
most lambda+1/n. The inverse empirical-CDF convention obeys the same bounds.
At fixed positive power levels both changed fractions vanish. Quantiles preserve
common lower bounds; half-score cutoffs exist and stay one half. The pointwise
inverse-weight and bounded weighted-mean bounds hold. Under the printed finite-
profile iid, overlap, integrability and uniform score consistency conditions,
ordinary and Winsorized ICSW have the stated common limit and vanishing difference,
with ATE identification under Assumption 1. The usual measure-theoretic conditions,
including measurable scores and cutoffs, are assumed. Ratios use their real-valued
extension on undefined samples; no eventual-definedness assumption is imposed. -/
theorem SAP.P029b.T16 : SAP.P029b.T16WholeStatement := by sorry

/-- P029-T17; p. 497, footnote 3 and equation (7), corrected.
The one-sided nested Bernoulli likelihood reduces to the treated-arm likelihood,
and their maximizer predicates agree. For every interior probability the printed
additive factor has the stated two formulas and is at least one; at three quarters
it gives seven quarters and five quarters instead of the Bernoulli probabilities.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P029b.T17 : SAP.P029b.T17WholeStatement := by sorry

/-- P029-T18; pp. 496–497, Section 3.1; p. 504, equation (9) and the estimator display.
Under random assignment and no defiers, the type partition, conditional compliance
and receipt formulas, positive-AC nested representation, and interior probability
range hold. Every law with no always-takers, conditional compliance probability one half at the profile,
and assignment probability one half gives the printed misconditioning discrepancy. With existing weighted expectations and positive
compliance almost surely, weighted ITT equals the corrected covariate-law integral
in (9), which cancels to (10). The single-hat sample display equals Section 3.3.
The usual measure-theoretic conditions are assumed, including measurable versions
of the conditional means and integrability of the displayed expectations.
No uniform positive lower bound on compliance is required for the integral identity. -/
theorem SAP.P029b.T18 : SAP.P029b.T18WholeStatement := by sorry

/-- P029-T19; supplement pp. A1-A2, baseline and misspecified simulation designs.
Independent uniform covariates and shared coefficients, normal errors of standard
deviation three (baseline), logistic errors of location zero and scale three
(nonlinear design), standard normal outcome errors, and independent uniformly
balanced assignment realize the corrected recipes for every even sample size.
Thresholded indices give binary disjoint types, monotone potential treatments and
the stated type characterizations. The corrected treatment is the realized potential
treatment; an assigned complier receives treatment. The printed treatment equation
can have no solution or two solutions. The printed outcome and effect formulas obey
the potential-outcome identity. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P029b.T19 : SAP.P029b.T19WholeStatement := by sorry

/-- The printed claim is false: P029-T20; p. 499, Assumption 1 and the following paragraph.
Typical mean ignorability need not imply latent ignorability under the IV assumptions,
and a separate baseline-selection law satisfies latent ignorability with unequal
received-treatment potential-outcome means. -/
theorem SAP.P029b.T20 : T20Statement := by sorry

/-- The printed claim is false: P029-T21; p. 499, the sufficient-conditions paragraph.
Both printed independence implications fail, while constant effects give the stated
population identities under uniform positive overlap.
The constant-effect component adds measurable conditional-mean versions and a uniform
positive lower bound for the compliance score, and asserts the profile identities only
at profiles of positive probability and positive score. It does not assert the same
constant-effect result under positivity without that uniform bound, or sample limits.
The marginal refutation is stated for independence of the complier indicator. -/
theorem SAP.P029b.T21 : T21Statement := by sorry

/-- P029-T22; supplement p. A2 (design), p. A5 (text), p. A6 (Figure A3,
Noise (Homogeneous) panel), and p. A7 (Table A3).
For a supplied array of 2500 estimates and a supplied benchmark of five, empirical
RMSE is the square root of the average squared error about that benchmark.
Restriction: Records only the scoring convention. Omits the simulation design and
estimator implementations, including alpha = 0.275; any connection to historical
estimates or datasets; identification of the sample average effect, population ATE,
or LATE with five; and every numerical entry and graphical result of Table A3 and
Figure A3. No simulation output or implementation is validated or refuted. -/
theorem SAP.P029b.T22 : T22Statement := by sorry

/-- The printed claim is false: P029-T23; p. 498, Section 3.3; package compliance.score.R,
lines 88-91, and icsw.tsls.R, lines 28-37.
An exact minimizer of the package's inside-log criterion in an interior nested Bernoulli
model with positive observation weights does not minimize the weighted negative log likelihood.
This refutes the exact observation-weight fitting contract, and makes no assertion
against the article's bootstrap recommendation or about numerical solver performance. -/
theorem SAP.P029b.T23 : T23Statement := by sorry

/-- P029-T25; p. 495, equations (3)-(4); pp. 497-498, the gender example.
The five IV assumptions give both ITT identities and the LATE ratio, the defined
sample Wald estimator equals the centered bivariate IV coefficient, and the gender
example has values one half, 2/17 (rounding to 0.12), and one half. -/
theorem SAP.P029b.T25 : T25Statement := by sorry

/-- P029-T26; p. 498, Section 3.4; pp. 504-505, Appendix equations (8)-(14).
The population weighted-moment identities hold and ICSW converges to the ATE with
uniform consistency of the scores over the growing observed sample.
Restriction: Adds the maximum-in-sample score-error convergence in ICSWConditions,
measurable estimates in (0,1], iid joint draws, integrable potential outcomes,
measurable conditional-mean versions, second-countable Borel covariates, and the
explicit overlap and Assumption 1 conditions on the covariate-law support.
It does not prove consistency from the paper's pointwise Assumption 2 alone.
The sample conclusion states only consistency of the final Wald ratio; it omits the
Appendix's two separate convergence assertions for the sample weighted outcome-arm
difference and the sample weighted receipt-arm difference.
The sample ratios must additionally be eventually defined along almost every draw
sequence. Finite initial undefined samples use the usual real-valued extension. -/
theorem SAP.P029b.T26 : T26Statement := by sorry

/-- The printed claim is false: P029-T27; pp. 499-500, paragraph on failure of Assumption 1.
Failure of latent ignorability need not produce
asymptotic bias. An iid randomized twelve-atom law has strict positive overlap,
interior nested receipt probabilities, heterogeneous effects, and failure of
Assumption 1 at both profiles. Its ATE and every observed outcome are zero.
Saturated nested ML scores are consistent on an event of probability tending to one,
and the zero extension of ICSW converges to the zero ATE. The usual measure-theoretic
conditions are satisfied. -/
theorem SAP.P029b.T27 : SAP.P029b.T27WholeStatement := by sorry
