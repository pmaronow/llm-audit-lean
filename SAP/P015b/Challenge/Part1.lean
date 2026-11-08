import SAP.P015b.Defs.WholeW3
import SAP.P015b.Defs
import SAP.P015b.Defs.WholeW2
import SAP.P015b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P015b
universe u v

/-- P015-T9; p. 257 (PDF p. 8), Random Coefficient Models and expression (10).
The two full-rank binary-treatment groups have zero within-group slopes but pooled GLS slope -10/61, with the exact inverse certificates, raw-data GLS value, and arbitrary-vector coordinate formula.
This is a counterexample to interpreting the pooled treatment coefficient as a scalar precision-weighted average of the group-specific OLS treatment coefficients. -/
theorem SAP.P015b.T9 : T9Statement := by sorry

/-- P015-T10; p. 257 (PDF p. 8), corrected random-coefficient aggregation
description; expression (7), p. 254 (PDF p. 5), under its assumptions within
each group. Usual measure-theoretic conditions are assumed.
For nonempty finite groups and coordinates, full-rank group designs, positive
error variances and a symmetric positive semidefinite coefficient covariance,
all covariance inverses exist. Precision pooling uniquely minimizes the GLS
loss, equals raw-observation GLS and the sum of the matrix-weighted group OLS
vectors, and its matrix weights sum to the identity. Its treatment coordinate
can include other coefficients. For prescribed scalar weights, pooling all
coefficient vectors is equivalent to the full treatment-row identity, hence
to off-treatment zeros AND the prescribed diagonal entries. Treatment-block
diagonal precisions suffice, with weights p_g/sum_h p_h. Along any sequence
with fixed finite dimensions, vanishing off-treatment entries give a vanishing
error for uniformly bounded coefficient inputs, using the treatment diagonal
entries as weights. Expression (7) applies separately in each group satisfying
its causal and regularity assumptions. This qualification is compatible with
consistency under correctly specified random-coefficient and exogeneity
assumptions; it makes no additional consistency assertion. -/
theorem SAP.P015b.T10 : SAP.P015b.T10WholeStatement_W3 := by sorry

/-- P015-T20; pp. 263-264 (PDF pp. 14-15), Appendix B.
The specified population has the exact regression weights and scaled leverages, their conditional averages, and all printed decimal and percentage roundings, with opposite profile comparisons. -/
theorem SAP.P015b.T20 : T20Statement := by sorry

/-- P015-T14; p. 257 (PDF p. 8), logistic display; Appendix C, p. 265 (PDF p. 16).
The binary logistic model specifies common real intercept, treatment and control
coefficients for which the conditional success probability given treatment and
controls is 1/(1+exp(-predictor)). Model membership supplies those parameters.
The printed unconditional probability cannot equal both predictions at distinct
treatments with fixed controls and a nonzero treatment coefficient.
The usual measure-theoretic conditions are assumed; the conditional-probability
equalities hold almost surely. -/
theorem SAP.P015b.T14 : SAP.P015b.T14WholeStatement := by sorry

/-- P015-T21; p. 265 (PDF p. 16), Appendix C; main text p. 257 (PDF p. 8).
For every binary sample the logistic log likelihood is Frechet differentiable
with score sum W_i'(Y_i - sigmoid(W_i theta)), without a rank assumption.
Affine coefficients give identical observation predictors and residual equations.
If W'W is nonsingular and the affine scale is nonzero, the surrogate equations
have a unique root whose affine transform is OLS; its treatment coefficient
multiplied by the scale equals the OLS treatment coefficient. -/
theorem SAP.P015b.T21 : SAP.P015b.T21WholeStatement := by sorry

/-- P015-T11; p. 257 (PDF p. 8); expansion point also on p. 265 (PDF p. 16).
The full-rank 200-observation binary example has the unique logistic fit at predictors plus or minus log 99, outside the exact Taylor radius pi, and every degree has probability error at least 49/100 and treatment-equation error at least 49. -/
theorem SAP.P015b.T11 : T11Statement := by sorry

/-- P015-T15; p. 254 (PDF p. 5), corrected expression (7); Appendix A,
p. 262 (PDF p. 13).
Under unconfoundedness, affine potential outcomes, the linear conditional
treatment mean, and the stated eight-family regularity, the actual OLS
treatment coefficient converges in probability to E[w tau]/E[w], with
w=(D-E[D|X])^2, on any ambient probability space. The two conditional
factorizations and their zero-moment consequences hold; the corrected OLS
coefficient column has K+2 coordinates. A fair-bit confounding example shows
that conditions (1) and (3) alone do not imply the factorizations. -/
theorem SAP.P015b.T15 : SAP.P015b.T15WholeStatement := by sorry

/-- P015-T22; p. 262 (PDF p. 13), Theorem A.1; proof pp. 262-263
(PDF pp. 13-14); expression (7), p. 254 (PDF p. 5).
For measurable iid unit data on any probability space, unconfoundedness,
affine potential outcomes, a linear conditional treatment mean, and the
stated eight-family regularity imply convergence in probability of the actual
OLS treatment coefficient to E[w tau]/E[w], where w=(D-E[D|X])^2. The
numerator is integrable and the denominator has positive finite expectation.
The inverse formula completes the estimator on singular finite samples. -/
theorem SAP.P015b.T22 : SAP.P015b.T22WholeStatement := by sorry

/-- P015-T23; pp. 255–256 (PDF pp. 6–7), expression (9).
For iid measurable observations with a linear conditional treatment mean, the
seven integrable moment families and nonsingular population control Gram in the
claim's sufficient regularity reading, and positive mean population weight, the
mean formed with fitted squared treatment residuals converges in probability to
E[w Z]/E[w], the effective population mean. Finite singular samples and zero
fitted denominators use the package's totalized conventions. -/
theorem SAP.P015b.T23 : SAP.P015b.T23WholeStatement := by sorry

/-- P015-T24; p. 263 (PDF p. 14), Corollary A.1; p. 256 (PDF p. 7).
Common random assignment makes the population treatment mean conditional on
controls constant and the squared residual weight independent of the effect.
Its mean is the positive treatment variance; the product expectation factors
and the weighted-effect ratio cancels to the average effect. Under iid sampling
and the eight-family regularity reading, both the actual OLS treatment estimate
and the intermediate fitted-weight effect ratio converge in probability to
that average effect, on every measurable sampling space. -/
theorem SAP.P015b.T24 : SAP.P015b.T24WholeStatement := by sorry

/-- The printed claim is false: P015-T18; pp. 264-265 (PDF pp. 15-16), Appendix C; pp. 256-257 (PDF pp. 7-8).
Finite logistic ML fits solve their residual equations, but a genuine square-link ML branch in the stated causal model refutes universal mean-only first-order OLS scaling.
Scope: Retains clause (A) and an explicit counterexample to universal clause (C); omits an assessment of score substitution for every specifically listed nonlogistic family in (B), and does not assert a separate counterexample for each named family. -/
theorem SAP.P015b.T18 : T18Statement := by sorry

/-- The printed claim is false: P015-T17; p. 261 (PDF p. 12), positivity passage.
Positive endpoint probabilities imply positive variance on the exported domain, while small effective mass, zero fitted sample weights, and a literal effective-law example refute the printed weight and pair-positivity implications.
Scope: The positive implication (A) requires countable covariates with measurable singletons and a global finite treatment second moment; omits its remaining meaningful cases. Clauses (B) and (C) are refuted by explicit examples, without a universal characterization of identification or an applied country-specific conclusion. -/
theorem SAP.P015b.T17 : T17Statement.{u,v} := by sorry
