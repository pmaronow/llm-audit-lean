import SAP.P039.Defs.WholeW1
import SAP.P039.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P039

/-- P039-T1; pp. 128, 136--137 and note 5, p. 141.
The sixteen-quarter description and the implemented Q2--16 income predictor differ,
as shown by quarter-one independence, the missing terms, and both exact witnesses. -/
theorem SAP.P039.T1 : T1Statement := by sorry

/-- P039-T2; pp. 128, 136--137 and note 5, p. 141.
The corrected Q2--16 predictor has positive normalization, ignores quarter one,
and satisfies the exact difference, equality characterization and endpoint formulas. -/
theorem SAP.P039.T2 : T2Statement := by sorry

/-- P039-T3; Figure 4 and p. 138, compared with Table 2, p. 137 and Table 3, p. 139.
The six-observation OLS witnesses give different tests at 5%, different slopes for
the correlated regressor, and the stated Gaussian-null scaled-t3 law and moments.
For every nonnegative threshold the two analytic formulas are the actual t4 and
t3 two-sided probability tails. The intermediate square and arctangent comparisons
and four-decimal p-value enclosures hold. The usual measure-theoretic conditions
are assumed; statistics are totalized on the Gaussian null set of zero SSE. -/
theorem SAP.P039.T3 : SAP.P039.T3WholeStatement := by sorry

/-- P039-T4; p. 138, final sentence, with the exact linear-OLS interpretation.
For every full-rank control design containing an intercept and every additional
regressor outside its span, clauses (a)--(e) give the projection, attenuation,
SE and t identities. Under positive isotropic noise the residual covariance has
rank n-k. Under the Gaussian null the full statistic has the central t(n-k-1)
law; an orthogonal centered regressor gives the stated scaled residual-line law,
which differs from t(n-2) when k is at least two, including residual df one or two.
The usual measure-theoretic conditions are assumed. The empirical nonlinear
application in (g) is expressly outside the formal claim. -/
theorem SAP.P039.T4 : SAP.P039.T4WholeStatement := by sorry

/-- P039-T5; p. 139 and note 15, p. 142.
Both voter-centered score comparisons refute the 1980 selection, and all five
signed maxima are positive, with the worked signed-maximum product negative. -/
theorem SAP.P039.T5 : T5Statement := by sorry

/-- P039-T6; p. 139 and corrected note 15, p. 142.
The corrected magnitude rule uniquely selects the stated elections with positive
attained margins in both samples, gives the signed fitted contribution and its
maximum magnitude, and preserves the rounded worked example. -/
theorem SAP.P039.T6 : T6Statement := by sorry

/-- P039-T7; Table 2, p. 137, and the specifications on p. 136.
Nested OLS gives the inverse-Gram and SE inequalities, the exact printed-cell
bound and positive gap, and incompatibility of all four printed rounding bins.
The alternative RMSQ convention sqrt(SSE/17) multiplies the ratio bound by
sqrt(13/14), strictly reducing it. The exact deposited inputs give the unique
corrected fits, income coefficients and SE displays .94, .96 and 1.0 (or 1.01).
All three corrected income coefficients retain their stars: their actual
two-sided Student reference probabilities, on 14, 13 and 12 df, are below .01.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P039.T7 : SAP.P039.T7WholeStatement := by sorry
