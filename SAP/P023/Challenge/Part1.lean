import SAP.P023.Defs.WholeW2
import SAP.P023.Defs.WholeW1
import SAP.P023.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P023

/-- P023-T1; p. 3 (PDF p. 3) and p. 7 (PDF p. 7).
The six-election linear design has the stated rank, exact model, weights and estimator values, and changing a distant outcome changes polynomial OLS while preserving the close-window and coarsened estimates. -/
theorem SAP.P023.T1 : T1Statement := by sorry

/-- P023-T2; p. 3 (PDF p. 3) and p. 7 (PDF p. 7).
The sixteen-election degree-seven design has the stated rank, exact model, nonzero weights and estimator values, and its distant perturbation changes polynomial OLS while preserving both close-window estimates. -/
theorem SAP.P023.T2 : T2Statement := by sorry

/-- P023-T3; p. 3 (PDF p. 3) and p. 7 (PDF p. 7); Section 5, p. 8 (PDF p. 8).
Coarsened OLS has exactly the localized RD weights and a unique party coefficient.
Full-rank polynomial OLS has the residual weights, root-count nonlocality and
conditional moments stated in clauses (b)–(d). The uniform degree-one and
degree-seven examples share the cutoff target while retaining distant influence.
For every positive tolerance the difference-event probability is bounded by the
two half-tolerance error probabilities; shared consistency implies convergence
of the estimator difference without an independence or sample-admissibility premise. -/
theorem SAP.P023.T3 : SAP.P023.T3WholeStatement := by sorry

/-- P023-T4; p. 7 (PDF p. 7) and p. 10 (PDF p. 10).
For every positive amplitude and positive width at most one, the uniform-margin
clipped linear family has a continuous Lipschitz conditional mean whose centered
part is odd, and zero cutoff jump. Its RD
means, residuals, degree-one and degree-seven coefficients and numerical outcome
bounds are as displayed. At every degree the fitted risk lies between the noise
risk and that risk plus a squared amplitude times width divided by three; no
measurable predictor, including one with infinite risk, improves it by more.
For fixed degree the coefficient tends to twice the amplitude as width vanishes,
while the risk bound vanishes. Every family member has the stated fixed-degree
sampling limit; the numerical degree-one and degree-seven limits remain separated
from shrinking-window RD under IID sampling and the stated bandwidth limits alone. -/
theorem SAP.P023.T4 : SAP.P023.T4WholeStatement := by sorry

/-- P023-T5; p. 10 (PDF p. 10); Proposition 2 and its Remark, p. 7 (PDF p. 7).
The clustered continuous positive-density family has continuous Lipschitz
conditional means with odd centered parts and zero cutoff jumps, all the displayed
moments and RD values, and a coefficient tending to minus one while the uniform
zero-polynomial error tends to zero.
At the numerical witness the coefficient, outcome bounds and error bound are
as displayed. The constant and fitted predictors can be improved by at most
the squared half-width by any measurable predictor, even one with infinite risk.
Consequently no coefficient-error constant can be uniform over the stated laws. -/
theorem SAP.P023.T5 : SAP.P023.T5WholeStatement := by sorry

/-- P023-T6; p. 7 (PDF p. 7) and p. 10 (PDF p. 10).
For one fixed uniform margin law, logarithmic amplification yields one bounded continuous mean with diverging polynomial coefficients along increasing degrees and a vanishing RD limit; every continuous function satisfying the zero-at-cutoff, size-bound and growing-bias-subsequence conditions has no Lipschitz bound. -/
theorem SAP.P023.T6 : T6Statement := by sorry

/-- P023-T7; p. 10 (PDF p. 10) and p. 7 (PDF p. 7).
Population and finite-sample residual formulas give the bias identities, approximation bounds, exact-specification and fixed-degree criteria, and the displayed uniform-law constants. -/
theorem SAP.P023.T7 : T7Statement := by sorry

/-- P023-T8; p. 7 (PDF p. 7); Appendix B, p. 10 (PDF p. 10).
Under the stated finite-second-moment IID, local density domination, Lipschitz
mean, bounded local conditional variance and shrinking-bandwidth assumptions,
all the positive-definite moment, residual-variance, zero-constant polynomial
approximation, population bias, fixed-degree, RD and growing-degree conclusions
(a)–(g) hold, including existence of a slow degree schedule. The smallest moment
eigenvalues and residual normalizations are positive. No separate singular-design
or empty-window probability assumptions are required. -/
theorem SAP.P023.T8 : SAP.P023.T8WholeStatement := by sorry

/-- P023-T9; p. 9 (PDF p. 9).
The corrected pair-indexed Appendix A formula partitions the observed pairs into bins, annihilates the demeaned party indicator outside the central bin, and gives the positive-denominator localized OLS ratio. -/
theorem SAP.P023.T9 : T9Statement := by sorry

/-- The printed claim is false: P023-T10; p. 3 (PDF p. 3); p. 7 (PDF p. 7); p. 8 (PDF p. 8).
The universal localization assertion for positive-degree polynomial vote-share controls fails, while coarsened OLS coefficients agree for outcomes agreeing on the close elections when both close-window counts are positive. -/
theorem SAP.P023.T10 : T10Statement := by sorry

/-- P023-T11; Proposition 1, p. 6 (PDF p. 6); Conditions 1–3, p. 5
(PDF p. 5); Appendix A, p. 9 (PDF p. 9).
For finite two-party election data with margins in [-1,1], binary win indicators
agreeing with the signs of nonzero margins, bandwidth 0 < k < 1, and the two
strictly interior observations required by Condition 1, both party counts in
U_b = (-k,k] are positive. Every least-squares solution of the all-election
regression with an intercept, the win indicator, and the printed width-2k bin
indicators of Condition 2 has win coefficient equal to the degree-zero,
rectangular-kernel RD difference in means of Condition 3. Ties may have either
binary indicator and nuisance bins may be empty. All sums here are finite.
Restriction: States the estimator-equality result under Conditions 1–3; omits the printed remark that Condition 1 is necessary for an RD estimate to exist. -/
theorem SAP.P023.T11 : SAP.P023.T11WholeStatement_W2 := by sorry

/-- P023-T12; p. 7 (PDF p. 7); equation (2) on p. 6 (PDF p. 6); Appendix B, p. 10 (PDF p. 10).
The adopted fixed-law reading of Proposition 2, formalized in PrintedPropositionTwo, fails: RD consistency together with the assertion that, for each positive tolerance, every sufficiently large fixed polynomial degree gives an estimator difference converging to a population bias below that tolerance.
The formal hypotheses include IID sampling, finite second moments, nondegenerate population moments, local support, and explicit usual-RD regularity; the moment guards are additional formal assumptions. -/
theorem SAP.P023.T12 : T12Statement := by sorry

