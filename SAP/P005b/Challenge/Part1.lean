import SAP.P005b.Defs.WholeW1
import SAP.P005b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P005-T15; Appendix B.2, p. 1516 (PDF p. 15), using (11)–(12) on p. 1515.
The corrected control covariance and the treatment covariance have coefficients
1/(n-2) and -1/(n-2), including the printed intermediate fraction and their combined expression. -/
theorem SAP.P005b.T15 : SAP.P005b.T15Statement := by sorry

/-- P005-T16; proof of Lemma A.2, pp. 1511–1512 (PDF pp. 10–11).
The corrected finite indicator calculations, coefficient simplification, and complement relation
give both the treated third moment and the mixed treated-control third moment. -/
theorem SAP.P005b.T16 : SAP.P005b.T16Statement := by sorry

/-- P005-T17; Appendix B.1.1, p. 1514 (PDF p. 13), corrected matching summation index.
The variance of the actual common-residual term (*) is bounded by the centered
double sum, then by the raw contraction. The exact Gram contraction and leverage
bound give deterministic order O(kappa/n), with bounded residual-difference second
moments, and (*) is O_p(sqrt(kappa*d/n)), including dimension zero. -/
theorem SAP.P005b.T17 : SAP.P005b.T17WholeStatement := by sorry

/-- P005-T18; Appendix B.1.1, top of p. 1514 (PDF p. 13), corrected brackets.
The weighted normal equation gives all three bracketed vectors and identifies their first
expression with the actual common-residual term (*). -/
theorem SAP.P005b.T18 : SAP.P005b.T18Statement := by sorry

/-- The printed claim is false: the universal conjunction of the printed expectation identity
and the uncentered covariance variance bound fails under complete randomization.
P005-T19; Lemma A.1, pp. 1510–1511 (PDF pp. 9–10). -/
theorem SAP.P005b.T19 : SAP.P005b.T19Statement := by sorry

/-- The printed claim is false: both the universal third-component sign identity and the
stochastic expansion under the literal logarithm condition fail; the stated exact slope
decompositions, bias expression, and first-component moments hold.
P005-T20; Theorem 4.1, pp. 1509–1510 (PDF pp. 8–9). -/
theorem SAP.P005b.T20 : SAP.P005b.T20Statement := by sorry

/-- P005-T21; Theorem 3.2, pp. 1508–1509 (PDF pp. 7–8); proof in Appendix B.2.
The printed noninteracted bias estimator is exactly unbiased for the bias, and
its correction is exactly unbiased for the ATE. The closed-form coefficients
are the unique OLS minimizer. The inverse-free formula, bias decomposition,
inverse-component identity and both population component expectations hold for
all nonempty arms. Expressions (11) and (12), their expectations and their
collection into (7) require only their presupposed nonzero arm-size denominators. -/
theorem SAP.P005b.T21 : SAP.P005b.T21WholeStatement := by sorry

/-- P005-T22; Theorem 4.2, p. 1510 (PDF p. 9).
The interacted bias correction and corrected ATE are exactly unbiased, with the inverse-free
identity and both armwise expectations, including the stated weaker centered-covariate hypotheses. -/
theorem SAP.P005b.T22 : SAP.P005b.T22Statement := by sorry

/-- P005-T23; Theorem 3.1 and Remark 1, p. 1507 (PDF p. 6).
The exact noninteracted slope and bias decompositions give (5), (6), the covariance
interpretation, and the two stated vanishing consequences of Remark 1. -/
theorem SAP.P005b.T23 : SAP.P005b.T23Statement := by sorry

/-- P005-T24; Theorem 4.1, p. 1509 (PDF p. 8), its valid exact part.
Both interacted slopes decompose as printed, and the bias expression and separate
first-component expectations give their stated difference. -/
theorem SAP.P005b.T24 : SAP.P005b.T24Statement := by sorry

/-- P005-T25; last part of Theorem 3.1, p. 1507 (PDF p. 6).
The noninteracted regression remainder is O_p(sqrt(kappa*d/n)) when d/n tends to zero.
The dimension convention 1 <= d_n <= n agrees with the canonical order-symbol definitions.
No conclusion is omitted. -/
theorem SAP.P005b.T25 : SAP.P005b.T25Statement := by sorry

/-- P005-T26; Theorem 3.2, p. 1509 (PDF p. 8); Appendix B.2, pp. 1516–1517.
The debiased noninteracted remainder equals the p. 1516 term (*) exactly and is
O_p(sqrt(kappa/n)) under Assumptions 1–3, without leverage decay. If kappa tends
to zero, this gives the printed common-slope expansion with o_p(n^(-1/2)) error. -/
theorem SAP.P005b.T26 : SAP.P005b.T26WholeStatement := by sorry

/-- P005-T27; Theorem 4.2, p. 1510 (PDF p. 9); Appendix B.4, pp. 1518–1519.
The debiased interacted remainder is O_p(sqrt(kappa/n)) under Assumptions 1–3,
without leverage decay. If kappa tends to zero, the printed arm-specific linear
expansion has o_p(n^(-1/2)) error. -/
theorem SAP.P005b.T27 : SAP.P005b.T27WholeStatement := by sorry
