import SAP.P013b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P013-T15; Propositions 5.3–5.6, pp. 1923–1924 (PDF pp. 12–13).
When every off-diagonal cross-exposure joint probability is positive, the first
covariance estimator has expectation at most the true covariance, with equality
when each unit's two selected potential outcomes agree. For arbitrary joint
probabilities, the adjusted covariance estimator has expectation at most the true
covariance, and the effect variance estimator has expectation at least the true variance. -/
theorem SAP.P013b.T15 : SAP.P013b.T15Statement := by sorry

/-- P013-T16; Section 7, expressions (12)–(15), pp. 1927–1929 (PDF pp. 16–18).
Fixed predictions give an unbiased difference total and its residual form, the
inverse-probability count is unbiased, and the zero-convention Hajek ratio has the stated bias bound. -/
theorem SAP.P013b.T16 : SAP.P013b.T16Statement := by sorry

/-- P013-T17; Proposition 8.1 and Corollary 8.1, pp. 1929–1930 (PDF pp. 18–19).
With misspecified exposures the HT total and contrast have the stated weighted
randomization-potential-outcome expectations. -/
theorem SAP.P013b.T17 : SAP.P013b.T17Statement := by sorry

/-- The printed claim is false: Conditions 3, printed 5 and 6 do not guarantee
the asserted limiting Wald coverage for every nested population sequence.
P013-T18; Proposition 6.2, p. 1926 (PDF p. 15), Appendix A.7, p. 1943 (PDF p. 32).
Coverage counts a negative variance estimate as noncoverage. In the source paired
witness, its probability along the even-size subsequence showing undercoverage is
at most 1/N and tends to zero; the refutation does not rely on undefined intervals. -/
theorem SAP.P013b.T18 : SAP.P013b.T18Statement := by sorry

/-- P013-T19; Proposition 6.1, p. 1925 (PDF p. 14), Appendix A.6, p. 1942 (PDF p. 31).
Under uniform Condition 3 and Condition 4 the HT effect estimation error converges in probability to zero. -/
theorem SAP.P013b.T19 : SAP.P013b.T19Statement := by sorry

/-- P013-T21; Section 7.1, p. 1927 (PDF p. 16), fixed-numerical-prediction reading.
The specified three-unit design gives all baseline, shifted, error, moment and
joint-repair facts refuting the asserted location property when predictions are held fixed. -/
theorem SAP.P013b.T21 : SAP.P013b.T21Statement := by sorry

/-- P013-T22; corrected Section 7.1, p. 1927 (PDF p. 16).
Exact translation formulas give equivariance, invariance and their characterizations,
zero mean translation errors, and calibration with fixed predictions, including a two-unit example. -/
theorem SAP.P013b.T22 : SAP.P013b.T22Statement := by sorry

/-- P013-T23; Section 10 and Table 2, p. 1936 (PDF p. 25), pp. 1934–1935 (PDF pp. 23–24).
The specified three-world two-unit example has identical records, different wearing
effects, the asserted estimator and loss tables, nonidentification, and the respondent comparison.
The refutation concerns wearing interpretation combined with the additional zero-scoring rule. -/
theorem SAP.P013b.T23 : SAP.P013b.T23Statement := by sorry

/-- P013-T24; corrected Section 10 and Table 2, pp. 1934–1936 (PDF pp. 23–25).
Recorded-outcome HT estimation has the stated loss decomposition, identification
conditions, sufficient condition, exclusion formulas, unequal Hajek factors and conditional numeric scaling.
Restricted: the scaling clause assumes item and survey are subsets of S, with
|S| = 2050, |item| = 1708 and |survey| = 1899, positive weights on S, and retention
of every nonzero recorded score in both sets. It does not assume or establish
item ⊆ survey: containment of survey nonrespondents among item nonrespondents is omitted.
The reconstruction's actual counts and zero coding, its link to the released
orange-wristband indicator, and reproduction of the twelve rounded Table 2 estimates are not verified.
The strictness of the comparison between the sufficient and necessary conditions is not separately asserted. -/
theorem SAP.P013b.T24 : SAP.P013b.T24Statement := by sorry

/-- P013-T25; Section 10, p. 1934 (PDF p. 23), expression (7), p. 1921 (PDF p. 10).
The specified school designs differ in support and give the stated moment formulas,
wrong-joint variance biases and correct-joint equality for a 56-school population
in which exactly two schools have nonzero hosted potential outcomes.
This is the canonical counterexample to identifying the two specified lotteries. -/
theorem SAP.P013b.T25 : SAP.P013b.T25Statement := by sorry

/-- P013-T26; corrected Section 10, p. 1934 (PDF p. 23), released scripts 1 and 7.
The two specified school laws have the stated counts, strict support inclusion,
marginals, joint laws, differences and student exposure preservation and nonhosting formulas. -/
theorem SAP.P013b.T26 : SAP.P013b.T26Statement := by sorry

/-- P013-T27; Section 10 and Table 2, pp. 1934–1936 (PDF pp. 23–25), formal reading.
For binary wearing outcomes observed consistently, the four exposure contrasts
are differences of wearing proportions and the HT estimators are unbiased for them. -/
theorem SAP.P013b.T27 : SAP.P013b.T27Statement := by sorry
