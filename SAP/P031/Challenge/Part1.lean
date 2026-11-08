import SAP.P031.Defs.WholeW1
import SAP.P031.Defs.WholeW2
import SAP.P031.Defs.WholeW3
import SAP.P031.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P031

/-- P031-T1; Theorem 1, p. 367 (PDF p. 3), proof p. 368 (PDF p. 4).
For every admissible assignment and observed outcome vector, HC2 equals Neyman's estimator. -/
theorem SAP.P031.T1 : T1Statement := by sorry

/-- P031-T2; Corollary 1, p. 368 (PDF p. 4), displays p. 367 (PDF p. 3).
Over uniform fixed-size assignments, expected HC2 is at least the actual randomization variance. -/
theorem SAP.P031.T2 : T2Statement := by sorry

/-- P031-T3; Theorem 2, p. 369 (PDF p. 5).
Multiplying OLS variance by (N-2)/(N-1) gives the constant-effects imputation variance. -/
theorem SAP.P031.T3 : T3Statement := by sorry

/-- P031-T4; Theorem 3, p. 369 (PDF p. 5), proof p. 370 (PDF p. 6).
In a balanced design the scaled constant-effects, OLS, Neyman, and HC2 estimators agree. -/
theorem SAP.P031.T4 : T4Statement := by sorry

/-- P031-T5; pp. 367-368 (PDF pp. 3-4), including footnote 2.
The cited regular finite-population regime gives the nonnegative finite
Neyman bias, exact HC2 equality, asymptotic robust equivalences, and
conservative normal-interval coverage. Restriction: this candidate assumes
strictly positive limiting N-times-true-variance contrast D; it does not
formalize the D=0 coverage case. Allocation and moment conditions come from
the cited regime, not from routine measure-theoretic defaults. The W1
normality-only counterexample is retained as related auxiliary evidence. -/
theorem SAP.P031.T5 : SAP.P031.T5CitedRegimeStatement := by sorry

/-- P031-T6; Section 4, p. 369 (PDF p. 5).
Within the cited regular finite-population regime, unbalanced OLS and CE
variance estimates can have either sign of asymptotic error and can yield
undercoverage. Neyman and HC2 retain conservative normal-interval
coverage. Restriction: the positive contrast assumes strictly positive
limiting N-times-true-variance D and does not formalize the D=0 case.
The W1 normality-only counterexample is retained as related auxiliary
evidence. The once-unhatted CE quantity is the imputation estimator. -/
theorem SAP.P031.T6 : SAP.P031.T6CitedRegimeStatement := by sorry

/-- P031-T7; first sentence of the proof of Theorem 2, p. 369 (PDF p. 5).
The specified four-unit assignment has both imputed variances 5/2 and original
potential-outcome covariance 23/2, refuting the printed covariance equality. -/
theorem SAP.P031.T7 : T7Statement := by sorry

/-- P031-T8; corrected proof of Theorem 2, p. 369 (PDF p. 5).
Every link of the corrected imputed-moment, residual-sum, and scaled-OLS proof chain holds. -/
theorem SAP.P031.T8 : T8Statement := by sorry

/-- P031-T9; corrected proof of Theorem 3, p. 370 (PDF p. 6).
Every link of the balanced-design chain holds, with the CE hat and sample-variance notation restored. -/
theorem SAP.P031.T9 : T9Statement := by sorry

/-- P031-T10; counterexample to footnote 3, p. 369 (PDF p. 5), parts (a)–(c).
Shifting all control outcomes by c and all treatment outcomes by c+d shifts the
control mean and population effect by c and d. Assignment by assignment, it
adds c+dX to the observed vector, shifts the intercept and treatment estimate
by c and d, and preserves every residual, OLS variance estimate, and actual
randomization variance. For N=4k, M=k, k≥2, the balanced sign schedules
y0=z, y1=a z+2, a=1,2,1/2, share allocation 1/4, control mean 0 and effect 2.
Their moments and exact N-times-variance and OLS formulas hold, with the treated
sign mean r satisfying E[r²]=3/(N-1). Their true leading limits are 16/3,49/3,25/12,
their OLS probability and expectation limits are 16/3,28/3,13/3, and their
OLS/actual-variance probability-limit ratios are 1,4/7,52/25. At k=2 the printed
outcome vectors give 28 assignments, actual variances 16/21,7/3,25/84, expected
OLS estimates 16/21,8/7,2/3 and expectation/variance ratios 1,24/49,56/25.
Thus allocation and the two first moments do not determine the variance relation.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P031.T10 : SAP.P031.T10WholeStatement := by sorry

/-- P031-T11; corrected footnote 3, p. 369 (PDF p. 5).
Interior allocation and convergent population second moments give the corrected
variance, expected-OLS, bias, treatment-effect-variance, conditional probability,
and positive-denominator ratio limits, with bounded-outcome sufficiency and exact shifts.
Sample second-moment convergence means consistency of both centered arm sample variances.
Restriction: Excludes only the bibliographic assertion that Freedman (2008b, p. 190)
gives this relation; every mathematical clause of the corrected footnote is stated. -/
theorem SAP.P031.T11 : T11Statement := by sorry

