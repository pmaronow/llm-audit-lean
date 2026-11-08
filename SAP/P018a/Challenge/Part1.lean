import SAP.P018a.Defs.WholeW3
import SAP.P018a.Defs.WholeW2
import SAP.P018a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P018-T1; p. 566 (PDF p. 3), equation (2); p. 573 (PDF p. 10), equation (6)
and Sigma; pp. 568, 576, V_r and V_w.
For iid uniform units, X=(1,2+Z_i+Z_j) and Y=(Z_i+Z_j)^2 satisfy the bounded
dyadic projection assumptions and almost-sure sample rank. The conditional
mean is quadratic and not affine. All printed conditional covariance meats,
including the singleton repeated and unit-weight extensions, are zero.
The centred scores have the displayed H, overlapping Gamma, exact nonzero
finite variance and positive leading limit. The true target tends to
4 Q^{-1} Gamma Q^{-1}=V_*, the scaled estimator has that Gaussian limit,
and the sandwich converges in probability to V_*. The usual
measure-theoretic conditions are assumed. -/
theorem SAP.P018a.T1 : SAP.P018a.T1WholeStatement := by sorry

/-- p. 566 (PDF p. 3), equation (2); p. 573 (PDF p. 10), equation (6) and
Appendix B; p. 568 and p. 576, repeated and weighted covariance targets.
Under the usual measure-theoretic conditions, the symmetric iid single-record
model has centered scores, zero disjoint raw moments, the corrected sparse
second-moment meat, the full law of total covariance and its omitted positive
semidefinite term, the disjoint conditional remainder, the overlap representation
of Gamma, and the exact finite-N and limiting sandwiches. Projection orthogonality
alone need not remove the omitted term. For bounded finite repeated records and
fixed real weights with nonsingular population Gram, the total score is centered;
its covariance equals the full raw double sum and the sparse unconditional
covariance sum. The sparse raw sum is valid exactly when the sparse block-mean
products cancel, in particular if every block is centered. Global centering alone
is insufficient. The repeated and weighted targets use N/L^2 and N/D^2,
respectively. No fitted-residual consistency is asserted here. -/
theorem SAP.P018a.T2 : SAP.P018a.T2WholeStatement_W3 := by sorry

/-- P018-T3; pp. 573-574 (PDF pp. 10-11), Appendix B.
In the intercept fair-sign model the fit, residual bound, ordered-overlap
identity, exact meat, target, means, fourth moments and scaled variance have
the displayed formulas. The raw mean error diverges while its normalized
version vanishes, and the sandwich remains consistent. Products of fitted
residuals on disjoint endpoint unions have the stated positive covariance,
while another covariance is negative; these are actual OLS residuals and
the disjoint configuration lies outside the six printed cases. The
deterministic missing-N and spike examples invalidate the printed moment
inferences. The bounded inverse-design example has determinant twice
Var(exp(-T))>0, almost-sure rank for every N>=3, inverse convergence in
probability and the displayed infinite extended inverse-norm expectation
for every N>=3. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P018a.T3 : SAP.P018a.T3WholeStatement := by sorry

/-- P018-T4; p. 567 (PDF p. 4), Proposition 1; pp. 573–574 (PDF pp. 10–11), Appendix B.
The dyadic sandwich is absolutely consistent for the unconditional target, and the correctly scaled finite-moment Chebyshev conditions are sufficient. -/
theorem SAP.P018a.T4 : SAP.P018a.T4Statement := by sorry

/-- P018-T5; pp. 569–570 (PDF pp. 6–7), paragraph beginning ‘In the supplementary information’; Supporting Information p. 2; p. 572 (PDF p. 9), Conclusion; replication scripts 1 (line 86) and 2 (line 78).
The three-unit two-role covariance family misses the shared-unit covariance and understates the displayed GLS variance.
Restriction: Retains the N = 3 covariance matrices and universal parameter mismatch, the fixed-component GLS calculation and variance ratio, and the translation-equivariant intercept variance bound. For that bound, independence of the centered response from the Gaussian unit average, measurability, and both finite second moments are explicit hypotheses; their derivation for design (4) is not asserted. Drops the general-N random-effect covariance derivations, general-N mismatch and binomial(N,3) count, Gaussian average/centered-effect independence, the four displayed numeric lower bounds, and the repeated-observation extension. -/
theorem SAP.P018a.T5 : SAP.P018a.T5Statement := by sorry

/-- P018-T6; pp. 569–570 (PDF pp. 6–7); Supporting Information p. 2; p. 572 (PDF p. 9).
Shared-unit incidence yields the covariance expansion and role mismatch, and using the correct covariance yields the exact GLS covariance. -/
theorem SAP.P018a.T6 : SAP.P018a.T6Statement := by sorry

/-- P018-T7; pp. 565-567 (PDF pp. 2-4), Lemma 1 and Proposition 1.
The bounded iid sign-pair model has Q=[[1,1],[1,2]], beta=0, the stated
residual and score moments, and rank failure probability 2^(1-N). Its exact
target tends to diag(4,0). The specified eight-unit sample has positive
probability, the displayed Gram, OLS coefficient, meat and negative slope
variance. Jointly (N beta_hat_slope,N^2 V_hat_22) tends to
(2AB,4(A^2+B^2-1)) for independent standard normals A,B. The negative
variance probability tends to 1-exp(-1/2)>0; on such samples no real square
root exists. The pivot completed by zero when V_hat_22<=0 has no standard
normal limit. Nevertheless N V_hat tends in probability to diag(4,0) and
N V_hat-V_N tends to zero. The usual measure-theoretic conditions are
assumed; the ordinary inverse is used on full-rank samples and the matrix
inverse supplies the zero completion on singular samples. -/
theorem SAP.P018a.T7 : SAP.P018a.T7WholeStatement := by sorry

