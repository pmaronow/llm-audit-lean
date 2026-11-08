import SAP.P026b.Defs
import SAP.P026b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P026-T13, equations [17] (corrected), [18] and [19], pp. 141–142 (PDF pp. 7–8).
Both generalized arm-total expectations and the ATE bias equal the stated covariance expressions,
for arbitrary assignment-dependent real predictions. -/
theorem SAP.P026b.T13 : SAP.P026b.T13Statement := by sorry

/-- P026-T14, Table 2 p. 149, Table 1 p. 147, Section 7.1 p. 148 (PDF pp. 15, 13, 14).
The printed population has unique finite logistic fits with the stated coefficient bounds,
exactly unbiased ATE and variance estimators, the corrected moment intervals and ten rounded
column entries, and failure of all six erroneous printed entries. -/
theorem SAP.P026b.T14 : SAP.P026b.T14Statement := by sorry

/-- P026-T15, staged package documentation man/estate.Rd lines 8, 30 and R/estate.R lines 15, 31–36.
This refutes the reading of the package help that estate() with HT=TRUE remains unbiased when
covariates X are supplied.
The specified three-unit OLS adjustment has fitted values and estimates as displayed, expectation
one half and bias minus one half although the ATE and unadjusted HT estimates are one. -/
theorem SAP.P026b.T15 : SAP.P026b.T15Statement := by sorry

/-- P026-T16, repaired package help, man/estate.Rd lines 8, 30 and R/estate.R lines 4–6, 15, 29, 31–36.
The fixed-prediction residual estimator is unbiased, while the all-unit intercept-inclusive OLS
residual estimator has the covariance bias formula, a biased example, and zero-covariance and
sharp-null sufficient conditions for unbiasedness. -/
theorem SAP.P026b.T16 : SAP.P026b.T16Statement := by sorry

/-- The printed claim is false: P026-T17, pp. 145–147, footnote 9 p. 147, introduction p. 137,
abstract p. 135 (PDF pp. 11–13, 3, 1).
The universal support and variance-conservativeness assertion fails, and a sharp-null example
with positive same-arm joints separately violates footnote 9's unbiasedness assertion. -/
theorem SAP.P026b.T17 : SAP.P026b.T17Statement := by sorry

/-- The printed claim is false: P026-T18, Section 5.1 and footnote 5, p. 142 (PDF p. 8).
The XOR design supplies individually independent fitting inputs whose deterministic fit has
nonzero covariance with the focal treatment indicator, refuting the printed general rule. -/
theorem SAP.P026b.T18 : SAP.P026b.T18Statement := by sorry

/-- The printed claim is false: P026-T19, Table 2 p. 149 and Section 7.2 p. 148 (PDF pp. 15, 14).
The stated FE (Cov.), G (Linear) and G (Logit) moment assertions for the printed population
cannot all be correct. -/
theorem SAP.P026b.T19 : SAP.P026b.T19Statement := by sorry

/-- P026-T20, equations [5]–[8], pp. 138–139 (PDF pp. 4–5).
The observed/potential HT masking identity holds and both totals and the ATE estimator are
unbiased under every finite binary assignment law with positive treatment and control marginals. -/
theorem SAP.P026b.T20 : SAP.P026b.T20Statement := by sorry

/-- P026-T21, Section 4.1, equations [11]–[12], pp. 139–140 (PDF pp. 5–6).
With exactly n of N units treated and equal inclusion probabilities, HT equals
the actual difference in unit means on support, and both the displayed contrast
and that difference are unbiased. For any partition into M nonempty clusters
whose distinct treatment indicators disagree with positive probability, with
treatment and control marginals m/M and (M-m)/M, 0 < m < M, HT equals
M/N times the difference of observed unit arm totals divided by m and M-m,
at every allocation; this contrast is unbiased, without a fixed cluster count.
There is a real-valued four-unit example with clusters {1}, {2}, {3,4}, one
uniformly treated cluster, distinct cluster indicators, and both unit arms
nonempty on support: for sharp-null outcomes (1,1,0,0), the actual difference
in means has expectation 1/9, whereas the ATE and expected HT are zero. -/
theorem SAP.P026b.T21 : SAP.P026b.T21WholeStatement := by sorry

/-- P026-T22, Appendix B p. 150 and equations [13]–[16], pp. 140–141 (PDF pp. 16, 6–7).
Zero prediction covariance makes both generalized totals and the ATE unbiased, including fixed
predictions, and the assignmentwise generalized adjustment identity holds. -/
theorem SAP.P026b.T22 : SAP.P026b.T22Statement := by sorry

/-- P026-T23, p. 139, Appendix A pp. 149–150 and Appendix C p. 151 (PDF pp. 5, 15–17).
HT obeys the affine formula and exact balance characterization with a supported failure example,
while identically transforming outcomes and predictions scales the generalized estimator. -/
theorem SAP.P026b.T23 : SAP.P026b.T23Statement := by sorry

/-- P026-T24, equations [25]–[30], pp. 144–145 (PDF pp. 10–11).
The generalized estimator is residual HT, its fixed-prediction variance has the displayed formula,
and actual cluster totals obey both arm-variance formulas and the full, split and off-diagonal
cross-covariance formulas without a directed cross-support assumption. -/
theorem SAP.P026b.T24 : SAP.P026b.T24Statement := by sorry
