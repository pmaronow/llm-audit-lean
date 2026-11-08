import SAP.P005a.Defs.WholeW1
import SAP.P005a.Defs.WholeW2
import SAP.P005a.Defs.WholeW3
import SAP.P005a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P005a

/-- P005-T1; Appendix A.2, Lemma A.1, pp. 1510–1511 (PDF pp. 9–10).
The six-unit counterexample has all the stated means, coefficients, moments,
expectation, variance, bound and positive gap. Covariance and its variance are
unchanged by constant shifts; the printed bound changes under centering, and
its centered value bounds the variance. -/
theorem SAP.P005a.T1 : SAP.P005a.T1WholeStatement := by sorry

/-- P005-T2; Appendix A.2, Lemma A.1, p. 1511 (PDF p. 10).
For either nonempty arm, the printed expectation and the variance bound with
both vectors centered hold. Covariance is location invariant, the centered
sample-product mean has the simple-random-sampling variance, the product of
centered sums has the stated exact expectation and variance and their bound,
and the generic variance-difference inequality gives the repaired bound.
The printed bound is recovered when both population means are zero. -/
theorem SAP.P005a.T2 : SAP.P005a.T2WholeStatement := by sorry

/-- P005-T3; Appendix B.2, item 2, p. 1517 (PDF p. 16).
The standardized regular sixteen-unit counterexample satisfies all stated
moment and allocation conditions. Its leverage vector, mean and constant
leverage-product, three-category probabilities and covariance values, exact
variance, both failed bounds and positive gaps, and the valid third-expression
and centered-bound comparisons have the stated numerical values. -/
theorem SAP.P005a.T3 : SAP.P005a.T3WholeStatement := by sorry

/-- P005-T4; Appendix B.2, item 2, p. 1517 (PDF p. 16).
For either arm the centered leverage and outcome moments give every inequality
in the repaired finite variance chain, including the intermediate raw leverage
second moment. The two allocation coefficients obey the stated bounds.
Under Assumptions 1–3 the numerical right-hand side and the actual variance
are O(nκ²+κd/n), and the variance after division by n is
O(κ²/n+κd/n³). Dimension zero is allowed, including along a sequence. -/
theorem SAP.P005a.T4 : SAP.P005a.T4WholeStatement := by sorry

/-- P005-T5; Theorem 4.1, last display, p. 1509 (PDF p. 8).
The printed claim is false: the specified six-unit population satisfies the
finite-sample assumptions, has positive variances under all fifteen assignments,
and gives 217/2500 for the third bias component while the printed formula gives
-217/2500. All individual means, moments, coefficients and expectations are
included; reversing both printed signs gives the actual component. -/
theorem SAP.P005a.T5 : SAP.P005a.T5WholeStatement := by sorry

/-- P005-T6; Theorem 4.1, last display, p. 1509 (PDF p. 8).
For centered covariates, both third-moment identities, their signed bias components and the corrected control-minus-treatment formula hold exactly. -/
theorem SAP.P005a.T6 : T6Statement := by sorry

/-- P005-T7; Theorem 4.1, pp. 1509--1510 (PDF pp. 8--9), footnote 8.
The printed claim is false: the explicit one-covariate spike sequence satisfies
Assumptions 1--3 and every-assignment regularity, yet its remainder is not of
the printed stochastic order. The statement includes all grid identities,
pointwise bounds, exact leverage and slopes, fitted-line calculations, sharp
bounds, probability-one even-size tails and both exact finite minima. -/
theorem SAP.P005a.T7 : SAP.P005a.T7WholeStatement := by sorry

/-- P005-T9; Theorem 4.1, p. 1510 (PDF p. 9), and Appendix B.3, p. 1517 (PDF p. 16).
Under Assumptions 1--3 and every-assignment invertibility, the repaired condition
kappa log(2d) tending to zero implies the full interacted expansion with remainder
O_p(sqrt(kappa d/n)). The two repaired logarithms have the stated inequalities
and equivalent limits. The repaired condition implies vanishing leverage and the
printed condition, and is equivalent to the printed condition plus vanishing
leverage on the dimension-one subsequence. -/
theorem SAP.P005a.T9 : SAP.P005a.T9WholeStatement := by sorry

/-- P005-T10; Appendix B.4, last display, pp. 1518--1519 (PDF pp. 17--18).
The printed claim is false: the six-unit standardized regular population has
printed treated expectation 4913/1200 instead of 20/3, while the derived weight
is unbiased. All fifteen-assignment positivity, leverage, population covariance,
assignmentwise and expected gaps, and rational scaling identities are included. -/
theorem SAP.P005a.T10 : SAP.P005a.T10WholeStatement := by sorry

/-- P005-T11; Appendix B.4, corrected last display, pp. 1518--1519 (PDF pp. 17--18).
The corrected arm expressions cancel the inverse assignmentwise, have the exact
generic expectation, and are unbiased with the derived arm-size weights. The
cancelling treated weight equals its unsimplified expression and is unique for
arms of size at least two; singleton expectations require no division by s-1.
The printed treated weight has the stated bias. Standardization gives d/n <=
kappa <= 1 and h_i <= n. Under Assumptions 1--3 both corrected arm remainders
are O_p(sqrt(kappa/n)), from any starting size, with no extra rate assumption. -/
theorem SAP.P005a.T11 : SAP.P005a.T11WholeStatement := by sorry

/-- P005-T12; Appendix B.4, display introduced by “Similarly”, p. 1518 (PDF p. 17).
The printed claim is false: for the six-unit population with a=(-3,-2,-1,0,1,5),
x=sqrt(3/20)a, y(1)=0 and y(0)=a², all 15 assignments have positive treated and
control Gram matrices. The population is standardized, has bounded second
moments and allocation 1/3, and has h_i=(3/20)a_i² and mean leverage one.
The control slope decomposes into its population slope and the three nu terms;
the mean control covariate and its population-slope product have expectation
zero. The nuisance-product and fitted-slope-product expectations both equal
31085815448171/17062566567774 (approximately 1.822). The printed estimator has
expectation 12010469/846720 (approximately 14.18), so is biased; replacing the
treated inverse by the control inverse gives exactly the nuisance expectation.
The arm sizes, variance scaling, coefficient 1/8 and all rational-coordinate
identities hold assignment by assignment. -/
theorem SAP.P005a.T12 : SAP.P005a.T12WholeStatement := by sorry

/-- P005-T13; Appendix B.4, corrected display introduced by “Similarly”, p. 1518 (PDF p. 17).
The control bias estimator with the control inverse has the required expectation chain, component expectations and coefficient identities. -/
theorem SAP.P005a.T13 : T13Statement := by sorry

/-- P005-T14; Appendix B.2, pp. 1515–1516 (PDF pp. 14–15), and Remark 2,
p. 1507 (PDF p. 6). The corrected debiased expansion, inverse cancellation,
arbitrary-vector residual identities, centered arm-mean identities and actual
bias decomposition hold. A standardized everywhere regular four-unit example
shows that the printed treated-set control sum can differ from the control
residual mean. One function of the assignment, covariates and observed outcomes,
chosen before the potential outcomes, gives the inverse bias component. -/
theorem SAP.P005a.T14 : SAP.P005a.T14WholeStatement := by sorry
