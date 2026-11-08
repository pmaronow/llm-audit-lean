import SAP.P002b.Defs.WholeW2
import SAP.P002b.Defs.WholeW1
import SAP.P002b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P002-T16; Supplement p. 35 (Supplement PDF p. 15).
The centered four-unit covariate array has Gram matrix one-half times the identity, coordinate fourth moments one-half, augmented squared-norm maximum two, and sum-of-coordinate-maxima expression three. -/
theorem SAP.P002b.T16 : SAP.P002b.T16Statement := by sorry

/-- P002-T17; Supplement p. 35 (Supplement PDF p. 15).
Coordinate fourth-moment bounds imply the corrected finite maximum inequalities and an order bound proportional to the square root of sample size for fixed covariate dimension. -/
theorem SAP.P002b.T17 : SAP.P002b.T17Statement := by sorry

/-- P002-T18; Supplement p. 36 (Supplement PDF p. 16).
The feasible-minus-oracle adjusted contrast has the corrected signs in both its slope-error and inverse-Gram representations. -/
theorem SAP.P002b.T18 : SAP.P002b.T18Statement := by sorry

/-- P002-T19; Supplement p. 39 (Supplement PDF p. 19): (E.41); Supplement p. 40 (Supplement PDF p. 20): the display after (E.46).
Population-minus-fitted coefficients have the negative inverse-Gram representation, and the residual cross term has coefficient minus two. -/
theorem SAP.P002b.T19 : SAP.P002b.T19Statement := by sorry

/-- P002-T20; Supplement p. 37 (Supplement PDF p. 17).
The corrected control remainder tends to zero in design probability along every
admissible fixed-dimension model sequence. At the LATE, the oracle contrast equals
the arm-specific potential-response contrast, its intercept-centered version, and
the difference of arm residual means. Population intercepts are population means,
and the mean response contrast is the complier fraction times LATE minus beta.
The remainder uses the existing totalized inverse and zero-division convention;
on the domain of the displayed ordinary inverse and normalization it is (E.29). -/
theorem SAP.P002b.T20 : SAP.P002b.T20WholeStatement := by sorry

/-- P002-T21; Supplement p. 39 (Supplement PDF p. 19), corrected display (E.36).
Fix positive covariate dimension, delta less than one, positive epsilon, A and B,
and a balance constant in (0, 1/2]. For every significance level alpha in (0, 1),
the ordinary right-hand limit at zero of the sample-size limit superior of the
nested suprema over LATE and Xi of adjusted-statistic rejection probabilities
exists in [0, 1] and is at most alpha. The cutoff is the standard-normal
(1-alpha/2)-quantile minus kappa. All positive population sizes are included;
empty model suprema are zero. Absolute studentization is zero for zero over zero
and infinity for a nonzero numerator over zero scale, and singular regression
arms use the fixed least-squares minimizer. The usual measure-theoretic
conditions are assumed. No positive population residual variance is required.
The corrected claim uses Xi and an inner limit superior; it asserts an ordinary
outer right-hand limit. -/
theorem SAP.P002b.T21 : SAP.P002b.T21WholeStatement := by sorry

/-- P002-T22; Main p. 16 (PDF p. 16), Algorithm 2; Supplement pp. 44-45
(Supplement PDF pp. 24-25), Algorithm 4 and Section H.2.
Every admissible history-dependent choice policy terminates in at most |J|+1
iterations when J is nonempty. Every completed corrected run has ordered crossing
endpoints, covers the real line, selects a quantile curve throughout each closed
interval, and returns exactly the empirical confidence set. This holds for every
regular nonnegative quadratic-ratio family, hence for both paper data settings
where the displayed ordinary regression inverses exist. -/
theorem SAP.P002b.T22 : SAP.P002b.T22WholeStatement := by sorry

/-- P002-T23; Supplement p. 45 (Supplement PDF p. 25).
On each closed Algorithm 1 or 3 gap, the selected simulated curve attains the squared critical value and the returned piece is the confidence set intersected with the gap. -/
theorem SAP.P002b.T23 : SAP.P002b.T23Statement := by sorry

/-- P002-T24; Supplement p. 45 (Supplement PDF p. 25): (I.1); Supplement p. 46 (Supplement PDF p. 26): (I.2) and the display after it.
Full-rank arm OLS coefficients and the adjusted statistic are affine in the hypothesized effect, and the Wald ratio zeroes the statistic when its denominator is nonzero. -/
theorem SAP.P002b.T24 : SAP.P002b.T24Statement := by sorry

/-- P002-T25; Main p. 6 (PDF p. 6), Section 3.3, first sentence; main p. 10 (PDF p. 10), Section 4.4, first sentence; also main pp. 4-5 (Section 3.1), p. 7 (Remark 2) and Supplement p. 23 (Supplement PDF p. 3).
A constant additive effect recovers baseline outcomes and gives finite-sample coverage at least one minus the significance level for both confidence sets. -/
theorem SAP.P002b.T25 : SAP.P002b.T25Statement := by sorry

/-- P002-T26; Main p. 10 (PDF p. 10), Remark 4 and (12); Supplement
Section I, pp. 45-47 (Supplement PDF pp. 25-27).
The adjusted full-randomization confidence set is a finite union of intervals
where its ordinary regression inverses exist; it can be nonempty without being
a single interval. The adjusted contrast is affine, and its outcome and receipt
contrasts are the treatment coefficients of the corresponding interacted fits.
The well-defined adjusted Wald ratio has zero contrast and statistic and belongs
to the confidence set at every interior level. Under the stated IV invertibility
conditions, the IV product identity holds, and a nonzero receipt contrast gives
equality of the IV coefficient and the Wald ratio. No positive-variance condition
is imposed: zero-over-zero is zero and absolute nonzero-over-zero is infinity. -/
theorem SAP.P002b.T26 : SAP.P002b.T26WholeStatement := by sorry

/-- P002-T27; Main p. 14 (PDF p. 14); proof in Supplement Section H.1, p. 45 (Supplement PDF p. 25).
Between crossings the empirical quantile index set is constant, and every interior quantile index persists at each finite endpoint. -/
theorem SAP.P002b.T27 : SAP.P002b.T27Statement := by sorry

/-- P002-T28; Main p. 17 (PDF p. 17), Theorem 3; Algorithms 1-2, main pp. 15-16;
Algorithms 3-4, Supplement p. 44; proof in Supplement Section H.2, p. 45.
For both covariate settings, finite crossing lists and completed runs exist, every
completed run using the corrected interval-index pairs returns the empirical
confidence set, and with no intersections any selected quantile curve does so.
Restriction: For both covariate settings, includes finite complete crossing-list existence, Algorithm 1/3 run existence and correctness, existence and correctness of completed corrected Algorithm 2/4 runs, and arbitrary quantile selections in the no-intersection branch. In the regression-adjusted branch, assumes positive covariate dimension, population-centered covariates, and full-rank augmented design matrices in both arms for the observed assignment and every simulated assignment; no assertion is made for rank-deficient adjusted datasets. Does not assert termination for every prescribed sequence of admissible Algorithm 2/4 index choices. -/
theorem SAP.P002b.T28 : SAP.P002b.T28Statement := by sorry

/-- The printed claim is false: the universal exact nominal-coverage limit of Theorem 1 fails.
P002-T29; Main p. 8 (PDF p. 8); proof in Supplement Section C, pp. 23-31 (Supplement PDF pp. 3-11). -/
theorem SAP.P002b.T29 : SAP.P002b.T29Statement := by sorry

/-- The printed claim is false: the universal exact nominal-coverage limit of Theorem 2 fails.
P002-T30; Main p. 11 (PDF p. 11); proof in Supplement Sections D-E, pp. 31-42 (Supplement PDF pp. 11-22). -/
theorem SAP.P002b.T30 : SAP.P002b.T30Statement := by sorry
