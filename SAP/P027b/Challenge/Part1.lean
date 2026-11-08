import SAP.P027b.Defs
import SAP.P027b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P027-T14; supplement Section B, p. A2 and Table A1, p. A5.
At M=5 the two fixed populations have the stated true variances, all three expected
estimates, biases, and reversed bias rankings. Independent standard Gaussian errors
give the model-averaged biases 2/5 versus 1/10 at alpha=0 and 18/5 versus 41/10 at
alpha=2, again reversing the ranking. At M=500 and alpha=0 the model averages of the
conditional sampling variance, corrected estimate, and collapsed estimate are
499/1000, 499/500, and 1/2, with relative biases 1 and 1/499. All outcome expectations
exist and the relative-bias denominator is positive. The rounded simulation rows
are comparison context, rather than additional exact expectation identities.
-/
theorem SAP.P027b.T14 : SAP.P027b.T14WholeStatement := by sorry

/-- P027-T15; supplement Section B, pp. A1–A2.
The sample formulas, fixed-population variance, model expectations, nonnegative biases,
exact parameter-qualified ranking, and finite ratios and limits give the corrected comparison.
-/
theorem SAP.P027b.T15 : SAP.P027b.T15Statement := by sorry

/-- P027-T16; supplement Section B, p. A2, with labels on pp. A5–A6.
For an equally likely common stratum and independent standard Gaussian errors,
alpha=1/2 gives zero outcome means, variances 5/4, covariance 1/4, and Pearson
correlation 1/5. The printed ratio is 1/3 and exceeds that correlation by 2/15.
The two fixed means average to zero; their divisor-1 variance is 1/2, giving the
printed variance ratio, while their divisor-2 variance is 1/4, equal to the variance
of the random stratum effect. Conditional on either stratum the outcome variances
are one and their covariance and correlation are zero. All variables used in
these correlations have finite second moments, and each conditioning event has
probability 1/2. This compares the printed parameter with ordinary Pearson
correlation and does not identify the authors' intended convention.
-/
theorem SAP.P027b.T16 : SAP.P027b.T16WholeStatement := by sorry

/-- P027-T17; supplement Section B, p. A2, Table A1 and Figure A1, pp. A5–A6.
The printed heterogeneity parameter uses divisor-1 stratum-mean variance, and its conversion
to ordinary same-stratum correlation has the stated comparison, monotonicity, limit, and labels.
-/
theorem SAP.P027b.T17 : SAP.P027b.T17Statement := by sorry

/-- P027-T18; supplement Section B, pp. A1–A2; main p. 233.
Independent uniform stratum draws have diagonal inclusion 1/M, distinct same-stratum
joint inclusion zero, cross-stratum inclusion 1/M squared, and the stated covariances.
The separate outcome-index correction is the definition stratumOutcomes.
-/
theorem SAP.P027b.T18 : SAP.P027b.T18Statement := by sorry

/-- P027-T19; supplement Sections A and C, pp. A1, A3–A4, and Table A3, p. A8, rows 30,40,50,60.
Exact periodic-design expectations and model moments, signal-canceling diagonalization,
Gaussian chi-square laws and tail bounds give the stated tiny probabilities for the printed means.
Ratios require positive expected variance, and Gaussian law and tail assertions require positive
noise variance, exactly as in the accepted canonical claim; no deterministic exclusion is asserted.
-/
theorem SAP.P027b.T19 : SAP.P027b.T19Statement := by sorry

/-- P027-T20; Proposition 1 and its following paragraph, p. 234, Section 2.2.
The expected HT variance estimate equals the true total variance plus the ordered zero-pair
bias A; common-sign outcomes give nonnegative bias, and examples realize either sign.
-/
theorem SAP.P027b.T20 : SAP.P027b.T20Statement := by sorry

/-- P027-T21; Proposition 2 and proof, pp. 235–236, Section 3.
For positive conjugate exponents the correction is unbiased for A-star, which bounds both
signs of A, giving the exact corrected expectation and conservativeness for arbitrary outcomes.
-/
theorem SAP.P027b.T21 : SAP.P027b.T21Statement := by sorry

/-- P027-T22; Corollary 1 and proof, pp. 236–237, Section 3.1.
Equality of the conjugate powers and opposite-sign equality on every zero-inclusion pair
suffice for the corrected estimator to be unbiased.
-/
theorem SAP.P027b.T22 : SAP.P027b.T22Statement := by sorry

/-- P027-T23; Corollary 2, p. 237, Section 3.2.
The displayed quadratic estimator is the exponent-two specialization and is conservative.
-/
theorem SAP.P027b.T23 : SAP.P027b.T23Statement := by sorry

/-- P027-T24; Corollary 3 and proof, pp. 237–238, Section 3.2.
On every sample the quadratic estimator attains the minimum among all positive constant
conjugate-exponent corrected estimators, with equality at the pair (2,2).
-/
theorem SAP.P027b.T24 : SAP.P027b.T24Statement := by sorry
