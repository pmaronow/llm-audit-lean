import SAP.P002a.Defs
import SAP.P002a.Defs.WholeW1
import SAP.P002a.Defs.WholeW2
import SAP.P002a.Defs.WholeW3
import SAP.P002a.Defs.WholeW4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P002-T1; Supplement pp. 23-24 (PDF pp. 3-4) and pp. 34-35 (PDF pp. 14-15).
The printed claim is false: the twelve-unit population satisfies both parameter spaces,
with all the stated moments, OLS coefficients, contrast variances, assignment probabilities
and oracle formula. Its variance bounds have right sides 65/4752 and 39/55, exceeding
the actual variances 5/396 and 36/55. The repeated-block family preserves both failures
with factor 13/12; the displayed negative-delta arithmetic step fails. -/
theorem SAP.P002a.T1 : SAP.P002a.T1WholeStatement := by sorry

/-- P002-T2; Supplement pp. 23-24 (PDF pp. 3-4) and pp. 34-35 (PDF pp. 14-15).
Replacing delta by max(delta,0) gives the two corrected variance lower bounds for every
admissible model, hence at every subsequence term. The entire corrected complier chain
(C.3)-(C.6), full-population bound (C.8), and residual-square bound preceding (E.10) hold.
Negative-delta classes are contained in the corresponding zero-delta classes; nonnegative
delta recovers the printed bounds. Singleton compliers and zero variances are included. -/
theorem SAP.P002a.T2 : SAP.P002a.T2WholeStatement := by sorry

/-- The printed claim is false: Both universally quantified printed variance lower bounds are false.
P002-T3; Supplement pp. 23-24 (Supplement PDF pp. 3-4) and pp. 34-35 (Supplement PDF pp. 14-15). -/
theorem SAP.P002a.T3 : SAP.P002a.T3Statement := by sorry

/-- P002-T4; main p. 8 (Theorem 1 and Remark 3), main p. 11 (Theorem 2),
Supplement p. 31 (PDF p. 11), and Assumptions 3(ii), 5(ii).
The printed claim is false: the half-moment bound forces collapse. The stated nonempty
raw class has all observed and reassigned statistics and quantiles zero, and coverage one.
The adjusted class has zero population residuals, exact full-rank fits, the individual
258 and 774 rank-loss bounds and the 1548 coverage bound for every singular-fit completion.
The grid moments give every beta fiber; both worst-case coverages tend to one. The
six-unit heterogeneous example has 20 accepting assignments and 312 nonzero reassigned
squared statistics among its 400 assignment pairs. -/
theorem SAP.P002a.T4 : SAP.P002a.T4WholeStatement := by sorry

/-- P002-T5; main pp. 8, 11; Supplement Sections C and E, pp. 23-42 (PDF pp. 3-22).
Both corrected uniform liminf lower bounds hold along nonempty sizes, including degenerate
models, without a cofinality hypothesis. Nominal worst-case liminf in a fixed class
requires a nondegenerate constant-additive-effect sequence in that very class whose
coverage tends to nominal. Raw nondegeneracy is baseline variance; adjusted nondegeneracy
is population OLS residual variance. Admissible nondegenerate raw constant-effect
sequences give nominal coverage and worst-case liminf. The specified degenerate raw
and adjusted classes instead have worst-case coverage tending to one. -/
theorem SAP.P002a.T5 : SAP.P002a.T5WholeStatement := by sorry

/-- The printed claim is false: P002-T6; Supplement p. 42 (Supplement PDF p. 22),
Lemma 20, claim 4, display (E.61), with the feasible statistic in the denominator.
With k = 1, delta = 0, epsilon = 1/4, A = 16, B = 5 and r = 1/3, the explicit
even near-singular family and odd equally spaced extension satisfy the standing
assumptions at every size n >= 8. All units comply and the LATE is zero. The even
family has the stated centered moments, covariate and residual bounds, common
population OLS fit, and distinct covariates, so every arm fit has full rank.
The two pure-block reassignments have slopes 1/eta and statistics -2/eta and 2/eta.
Arm complementation gives zero expectation. The feasible reassignment variance
is at least 8/(choose(n,n/2) eta^2), at least 8*2^(2n^2)/2^n, whereas every variance
estimate is between zero and sum(y_i^2)/(n/2)^2 <= 121/(25n) < 5/n. Their ratio is
at most 5*2^n/(8n*2^(2n^2)) < 1/2 for every original and reassigned assignment.
Consequently the conditional error probability at kappa = 1/2 is identically one
along the even subsequence and tends to one, contradicting the printed zero limit.
The odd extension has distinct equally spaced covariates in [-1,1] and the same
constants. Statements (E.58)-(E.60) are context, not assertions of this counterexample. -/
theorem SAP.P002a.T6 : SAP.P002a.T6WholeStatement := by sorry

/-- P002-T7; Supplement p. 42 (Supplement PDF p. 22), Lemma 20, (E.58)-(E.61),
with the canonical correction of 2026-11-04.
Fix a positive covariate dimension and admissible constants. For any deterministic
strictly increasing sequence of models in Xi whose population OLS residual variance
is strictly positive in each arm at every size, and any fixed deterministic strict
subsequence, the following hold on one event of probability one, simultaneously for
all positive thresholds: the feasible and pooled-coefficient oracle reassignment
statistics merge relative to the oracle standard deviation (E.58); the oracle and
feasible statistics have standard normal absolute tails on that scale (E.59)-(E.60);
and the feasible variance estimator is ratio-consistent for the oracle reassignment
variance (corrected E.61).
The usual measure-theoretic conditions are assumed. Observed assignments have exact
measurable complete-randomization marginals with any coupling across sizes; the
conditional reassignment law holds the observed response fixed. Xi includes valid
designs with at least two units, monotone receipt, a nonempty complier set, centered
covariates and Assumption 5. OLS uses a fixed least-squares minimizer on singular
arms. Residual positivity is pointwise in size, with no uniform lower bound. No
finite-size positivity of the conditional oracle variance is assumed; the variance
quotient is zero at denominator zero, as with real division in Lean. -/
theorem SAP.P002a.T7 : SAP.P002a.T7WholeStatement_W4 := by sorry

/-- P002-T8; Supplement p. 42 (Supplement PDF p. 22), first display;
Assumption 5(v), main p. 11.
For every positive even size 2m, the covariate x_i=2(-1)^i is centered, has fourth
moment 16, and has covariate Gram [4] with smallest eigenvalue 4, at least 2.
Its augmented Gram is diag(1,4) with smallest eigenvalue 1. The unit intercept
vector has quadratic form 1<2, refuting the covariate-to-augmented-Gram implication.
This is a counterexample to that implication, as asserted by the canonical target. -/
theorem SAP.P002a.T8 : SAP.P002a.T8WholeStatement := by sorry

/-- P002-T9; Supplement p. 42 (Supplement PDF p. 22), first display, corrected.
Centered covariates give population augmented Gram diag(1,C), smallest eigenvalue
min(1,lambda_min(C)) at least min(1,e), and the corresponding quadratic bound for
every vector. For Xi sequences with fixed positive dimension and constants, every
measurable coupling of the exact complete-randomization marginals satisfies, almost
surely along each fixed strictly increasing subsequence, the corrected coefficient-error
bound with one vanishing error for both arms. In particular this covers the paper's
independent coupling. -/
theorem SAP.P002a.T9 : SAP.P002a.T9WholeStatement := by sorry

/-- P002-T10; Supplement p. 26 (Supplement PDF p. 6).
The four-unit model contradicts both printed centering equalities and gives the corrected finite evaluations. -/
theorem SAP.P002a.T10 : SAP.P002a.T10Statement := by sorry

/-- P002-T11; Supplement p. 26 (Supplement PDF p. 6), identity before (C.17)
and corrected (C.17).
For every valid design and every beta, the treated sample-centering identity has
+beta times the population receipt mean, and its squared bracket has exact expectation
n0*sum(v_i^2)/(n1*n*(n-1)). When S_1 squared is positive, division gives the printed
normalized equality, sum(v_i^2)/S_1 squared=(n-1)/(pi^2*(1-pi)^2), and the simplified
expectation n0/(n1*n*pi^2*(1-pi)^2). Along increasing Theta sequences under fixed
balance and the stated denominator guard this expectation is O(n0/(n1*n)) and tends
to zero. The unnormalized finite identities need no variance positivity. -/
theorem SAP.P002a.T11 : SAP.P002a.T11WholeStatement := by sorry

/-- P002-T12; Supplement p. 29 (Supplement PDF p. 9).
The eight-unit sign population has variance 1/28 while printed (C.31) demands 1/14, and the corrected bound is attained. -/
theorem SAP.P002a.T12 : SAP.P002a.T12Statement := by sorry

/-- P002-T13; Supplement p. 29 (Supplement PDF p. 9).
The corrected finite reassignment-variance bound holds with the explicit balance constant. -/
theorem SAP.P002a.T13 : SAP.P002a.T13Statement := by sorry

/-- P002-T14; Supplement p. 30 (Supplement PDF p. 10).
The printed claim is false: the admissible balanced-sign family has the stated
hypergeometric law, moments, exact variance and ratio formulas, and zero-or-at-least-three
support. The printed error probability is one for every original assignment; its ratio
divided by the square root of sample size tends to two in probability and diverges.
The variance ratio lies in [0,1], has mean deficit 2/n and has the stated vanishing tails. -/
theorem SAP.P002a.T14 : SAP.P002a.T14WholeStatement := by sorry

/-- P002-T15; Supplement p. 30 (Supplement PDF p. 10), corrected Lemma 12.
For Theta sequences under the supplied Supplement p. 23 standing assumption that both
adjusted potential-outcome variances are positive, the corrected variance/variance
error probabilities tend to zero almost surely along every fixed strictly increasing
subsequence, simultaneously for all positive tolerances. Assignments may have any
measurable coupling of their exact complete-randomization marginals. No positivity
of every finite-size conditional variance is assumed; the proof obtains eventual
positivity almost surely, so any totalization at earlier zero denominators is immaterial. -/
theorem SAP.P002a.T15 : SAP.P002a.T15WholeStatement := by sorry

