import SAP.P041.Defs
import SAP.P041.Defs.WholeW2
import SAP.P041.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P041

/-- P041-T1; p. 5/8 (PDF p. 5); the claim recurs in the Abstract, p. 1/8 (PDF p. 1).
The stipulated exponential countermodel has common non-null hazard ratios, exact unequal 12-hour contrasts, and positive binomial expressions at all four observed counts.
-/
theorem SAP.P041.T1 : T1Statement := by sorry

/-- P041-T2; p. 5/8 (PDF p. 5); the tables used are S6 Table A (rendered p. 1) and S6 Table C (rendered p. 2).
The supplied rounded table entries give imprecise former-senator relative effects, smaller pooled early contrasts, and a countermodel to absence of relative bias.
Restriction: States the rounding-rectangle Wald bounds, interval membership and endpoint enclosures, central p-value approximation bounds, pooled early contrasts, and existence of a common-bias countermodel. Omits cited-only comparisons; causal identification of political inactivity and cultural or policy-enforcement mechanisms; the finer central z-statistic and central confidence-endpoint approximations; and the specified exact contrasts 16/125 and 9801/1000000 of the countermodel.
-/
theorem SAP.P041.T2 : T2Statement := by sorry

/-- P041-T3; Abstract, p. 1/8 (PDF p. 1); ‘Effects of Citations on Survival’, sentence running from p. 4/8 to p. 5/8 (PDF pp. 4–5).
The three printed directional percentages fail individually, while the symmetric percentages round as printed and strictly understate directional increases.
-/
theorem SAP.P041.T3 : T3Statement := by sorry

/-- P041-T4; Abstract, p. 1/8 (PDF p. 1); ‘Effects of Citations on Survival’, pp. 4/8–5/8 (PDF pp. 4–5).
The supplied counts give the corrected directional percentages, the conditional 76-removal variant, and the symmetric alternative repair.
-/
theorem SAP.P041.T4 : T4Statement := by sorry

/-- P041-T5; S1 File, last paragraph (rendered p. 2); S5 File, last paragraph (rendered p. 2); the main article points to S5 on p. 3/8 (PDF p. 3).
A uniformly balanced order with scrutiny gives zero direct effects and slow contrast but a positive accelerated expectation, with the full six-order table, general formula, size-50 instance, zero expected contrast for every fixed treatment-independent outcome pattern at every m >= 1, its four-rank example, and the independent-assignment boundary.
-/
theorem SAP.P041.T5 : T5Statement := by sorry

/-- P041-T6; S1 File, last paragraph (rendered p. 2); S5 File, last paragraph (rendered p. 2).
Rank-and-own-treatment outcomes give the average direct effect, whereas the scrutiny protocol separates the direct, planned, and implemented effects.
-/
theorem SAP.P041.T6 : T6Statement := by sorry

/-- P041-T7; S11 File, Table A (rendered p. 1); main text p. 4/8 (PDF p. 4).
The four binary-outcome cells give the stated OLS fit and HC1 variance. The
standard error is 0.06446... and rounds to 0.064. The erroneous printed
statistic has a two-sided p value rounding to 0.62 and is not significant at
10%, under either the normal or Student t(197) reference. The corrected
statistic exceeds both genuine 1% critical points, retaining three stars.
The usual measure-theoretic conditions are assumed. These are reference
calculations, not an assertion of an exact sampling law for robust OLS.
-/
theorem SAP.P041.T7 : SAP.P041.T7WholeStatement := by sorry

/-- P041-T8; S6 File, Tables B and E (rendered pp. 2–3), and S9 File,
Table A (rendered p. 1); main text p. 4/8 (PDF p. 4).
All four rounding rectangles have the stated Wald and Gaussian p enclosures,
central approximations, and strongest tiers 3, 2, 2, 2. The genuine normal
critical points have the stated approximations and give exactly the same
tier rule. Under nested cutoffs the first three printed weaker levels hold;
the fourth printed 1% assertion fails. The usual measure-theoretic conditions
are assumed. Decimal ellipses are approximations with explicit errors.
-/
theorem SAP.P041.T8 : SAP.P041.T8WholeStatement := by sorry

/-- P041-T9; S11 File, first paragraph and Tables A and B (rendered p. 1);
main text p. 4/8 (PDF p. 4).
Complementing an outcome reverses all slopes and residuals and preserves the
robust meat. HC1 covariances and standard errors agree whenever their divisor
exists. The stated balanced designs imply full rank and the difference-of-arm
survival slopes, reproducing all twelve entries and excluding their removal
interpretation. The six-hour full vectors and the initialization/replacement
rules give the stated coding correction. The usual measure-theoretic
conditions are assumed; the sample-size guard applies only to HC1.
-/
theorem SAP.P041.T9 : SAP.P041.T9WholeStatement := by sorry

/-- P041-T10; S9 File, Table A (rendered p. 1) and Table B (rendered p. 2);
S10 File (rendered p. 1); the same covariate label occurs in the notes to S6,
S9 and S11 and on p. 4/8 (PDF p. 4).
The fitted covariate is first-election year. Replacing it by tenure preserves
the predictor and fitted hazards after transforming the year, treatment and
interaction coefficients and baseline. The complete coefficient covariance
transforms by congruence, with every other coefficient retained. The five
printed ratios reverse direction through reciprocals, with the stated uniform
enclosures; the two 1.056 reciprocals round to 0.947. Reciprocal delta-method
standard errors obey s/r^2 even at zero variance. Where a Wald test is defined,
its squared statistic, two-sided normal p value and cutoff decisions are
preserved; both S9 Table B rounding rectangles retain three stars under this
Wald reading. The exact 132/125 illustration has the stated hazards and tenure
values. The usual measure-theoretic conditions are assumed; finite second
moments are explicit for covariance, and positive variance is required only
for the Wald test. Hazard ratios formed by division require a nonzero baseline.
-/
theorem SAP.P041.T10 : SAP.P041.T10WholeStatement := by sorry

/-- P041-T11; p. 5/8 (PDF p. 5); Abstract, p. 1/8 (PDF p. 1).
The three former-senator table pairs have the displayed Gaussian p-value enclosures and central approximations, with absolute Wald statistics below one.
Restriction: States the following subset of P1: three uniform Gaussian p-value enclosures, central absolute-z and p approximation bounds, and uniform absolute z below 1. Omits P1's explicit compatibility assertion for the printed living-subgroup p = 0.70: existence of h and s in the (0.775,0.503) rounding rectangle with 0.695 ≤ normalTwoSided (hazardWald h s) < 0.705. Omits all P2 confinement and mechanism inferences, their counterexample/refutation and the comparison with active-senator relative effects. Does not assert that the central living-subgroup p value rounds to 0.70.
-/
theorem SAP.P041.T11 : T11Statement := by sorry

/-- P041-T12; Abstract p. 1/8 (PDF p. 1); Effects of Citations on Survival,
pp. 4/8–5/8 (PDF pp. 4–5).
The printed claim is false: under the stated directional reading of “more
likely than”, each of 36%, 29% and 64% fails separately. The exact directional
increases are 575/13, 100/3 and 375/4, rounding to 44%, 33% and 94%. The
symmetric percentages do round to the printed numbers and all three removal
comparisons have the stated direction. The usual measure-theoretic conditions
are assumed. This refutation concerns the three directional percentages.
-/
theorem SAP.P041.T12 : SAP.P041.T12WholeStatement := by sorry

