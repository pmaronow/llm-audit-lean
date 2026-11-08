import SAP.P018a.Defs.WholeW2
import SAP.P018a.Defs.WholeW1
import SAP.P018a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P018-T8; p. 567 (PDF p. 4), after Proposition 1; p. 565 (PDF p. 2);
p. 573 (PDF p. 10), Appendix A.
Under the standing bounded symmetric unit-kernel model, the projection CLT (allowing
singular limits), target limit, and sandwich consistency hold. Every contrast of positive
limiting variance has a standard normal zero-extended pivot, vanishing probability of
nonpositive estimated variance, and nominal confidence coverage. The shared-endpoint
moment equals the projection covariance. The specified zero-variance slope supplies a
failure of normal inference. -/
theorem SAP.P018a.T8 : SAP.P018a.T8WholeStatement := by sorry

/-- P018-T9; p. 575 (PDF p. 12), Appendix D and Corollary 2;
pp. 567–568 (PDF pp. 4–5), fixed finite repetitions and Corollary 1.
The bounded fair-sign intercept model with fixed weights 2^(-i-j) has the stated geometric
sums, linear fit, variance bounded below by 9/16 and tending to 36/35, inconsistent
coefficients and divergent scaled variance. Its first-eight-positive event has probability
1/256 and forces the stated sandwich separation, ruling out a common deterministic
target. The normalized weighted design vanishes and the first coefficient tends to 3/4.
Identical repetitions 2^(i+j) transfer the joint law by label reversal and have no uniform
count bound. Duplicating both directions preserves the weighted fit and sandwich.
The all-N linear-fit and variance identities include the zero completion when N<2. -/
theorem SAP.P018a.T9 : SAP.P018a.T9WholeStatement := by sorry

/-- P018-T10; pp. 567–568 (PDF pp. 4–5), Corollary 1;
p. 575 (PDF p. 12), Appendix D and Corollary 2.
Uniformly bounded common record kernels and counts, a positive limiting normalized design,
and vanishing scaled overlap products of block means imply repeated sandwich consistency.
The stacked normal equations alone need not give overlap control or consistency. A common ordered
kernel, at most one record per direction, bounded positive normalized weights, and a
positive limiting normalized weighted design imply weighted consistency, permitting empty
blocks. Positive common weight rescaling leaves all three weighted quantities unchanged
where the ordinary inverses exist. Bounded positive fixed weights and unweighted rank
alone are insufficient. -/
theorem SAP.P018a.T10 : SAP.P018a.T10WholeStatement := by sorry

/-- P018-T11; p. 568 (PDF p. 5), display for the repeated target;
p. 576 (PDF p. 13), display for the weighted target.
In the fair-sign intercept model the exact fit has scaled variance 4, while each literal
unsummed target equals 4/D and tends to zero. The exact sample and expectation sandwich
formulas, their probability limit and both discrepancy limits hold. Restoring the dyad
sum gives the actual score variance and target 4. With T identical records the printed
block bread has the wrong dimension (and is singular for T=2); its unnormalized coefficient
bread gives 4/T^2, whereas the normalized bread gives 4. In the independent uniform/sign
two-regressor model the stated Gram, cross-Gram, scalar norm and dyad covariance yield
the distinct coefficient-bread and scalar-left-bread matrices. -/
theorem SAP.P018a.T11 : SAP.P018a.T11WholeStatement := by sorry

/-- P018-T12; p. 568 (PDF p. 5), V_r; p. 576 (PDF p. 13), V_w.
The corrected repeated and weighted targets use normalized expected Gram
matrices and the unconditional variance of the total score. They are exact
covariances, with centred total scores, expected normalized Grams and exact
linearization on every nonsingular sample. Block covariances have the sparse
form; raw moments may replace them if every block has mean zero. Singleton
records and unit weights reduce to equation (1), either normalization gives
the same repeated target, and the scalar and two-regressor model checks have
the stated values. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P018a.T12 : SAP.P018a.T12WholeStatement := by sorry

/-- P018-T13; p. 576 (PDF p. 13), Appendix E, display for the logistic variance estimator.
The six specified binary dyads have a globally strictly concave log-likelihood uniquely
maximized at zero, and the stated exact bread, meats, distinct positive definite
covariances, difference, and unit-incidence identity. -/
theorem SAP.P018a.T13 : SAP.P018a.T13WholeStatement := by sorry

/-- P018-T14; p. 576 (PDF p. 13), Appendix E.
The corrected logistic score-product estimator has the unit-incidence identity and symmetry and generally differs from the printed expression. -/
theorem SAP.P018a.T14 : SAP.P018a.T14Statement := by sorry

