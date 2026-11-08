import SAP.P018b.Defs.WholeW3
import SAP.P018b.Defs.WholeW1
import SAP.P018b.Defs.WholeW2
import SAP.P018b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P018-T15; p. 568 (PDF p. 5), Proposition 2, definition of $\hat\Sigma_{C,i}$; p. 575 (PDF p. 12), Appendix
C, definition of $E_i$.
The ordered nonincident reading doubles its contribution, adds the extra sandwich term, and gives the exact
six-dyad mismatch. -/
theorem SAP.P018b.T15 : SAP.P018b.T15Statement := by sorry

/-- P018-T16; p. 568 (PDF p. 5), Proposition 2; pp. 574–575 (PDF pp. 11–12), Appendix C.
Counting each nonincident dyad once gives both corrected decomposition identities and all five Appendix C
steps. -/
theorem SAP.P018b.T16 : SAP.P018b.T16Statement := by sorry

/-- P018-T17; p. 567 (PDF p. 4), equation (3) and the following sentence;
p. 570 (PDF p. 7), Fig. 1 caption.
All five negative-variance witnesses are asserted: the six-edge spectrum and cycle,
the intercept fit and every zero-padded extension, the full-rank two-coefficient
fit and negative definiteness, its bounded iid-unit population and labelled event,
and the N=20 normal-design witness with positive probability. The usual
measure-theoretic conditions are assumed. The covariance in (d) is also identified as the
Gaussian limit covariance and the limit of the linear-approximation targets;
ordinary finite-sample coefficient moments are not asserted. -/
theorem SAP.P018b.T17 : SAP.P018b.T17WholeStatement := by sorry

/-- P018-T18; p. 567 (PDF p. 4), sentence after Proposition 1.
The incidence and score formulas express the symmetric estimator as a difference
of two positive semidefinite matrices. It can have negative fitted-OLS diagonals.
Truncation is contractive and preserves the stated probability limit; negative
diagonals become rare for a target bounded away from zero. A real standard error
exists precisely on the nonnegative domain. The optional truncated convention
changes finite-sample values and entails no universal coverage guarantee.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P018b.T18 : SAP.P018b.T18WholeStatement := by sorry

/-- P018-T19; p. 567 (PDF p. 4), Corollary 1; pp. 573--574 (PDF pp. 10--11),
Appendix B; p. 575 (PDF p. 12), Corollary 2.
The explicit rare-category iid model satisfies (a)--(g): bounded records,
conditional mean zero and population rank, full sample rank, the exact OLS and
residual formulas and uniform residual bound, exact rare-event probabilities and
conditional second moments with their exponential lower bounds, infinite slope
moments and infinite positive but finite negative sandwich mean, the nondegenerate
Gaussian and sandwich limits, and the independent-uniform directed unit-weight
version with the same estimators and failures. The usual measure-theoretic
conditions are assumed for the finite quantities; divergent moments are asserted
as extended nonnegative integrals. Event index m below represents printed M=m+1. -/
theorem SAP.P018b.T19 : SAP.P018b.T19WholeStatement := by sorry

/-- P018-T20; p. 567 (PDF p. 4), Corollary 1; p. 575 (PDF p. 12), Corollary 2.
Restricted version of P018-T20(ii), under the C1 and C2 premises stated below;
the finite covariance identities, the UI-based actual-covariance implication,
the moment-failure examples and the deterministic-limit equivalence are included.
The retained covariance targets and explicit consistency premises are stated here;
no equivalence to an unsupplied canonical T10 contract is claimed.
Write L_N = sum_d T(N,d), D_N = N(N-1)/2, G_N = sum_dt X_dt X_dt', and
G_w,N = sum_dt w_dt X_dt X_dt'. Each population coefficient is the inverse
expected Gram times its corresponding expected XY sum. Define the population
residuals using those coefficients, the block scores b_d = sum_t X_dt epsilon_dt
and b_w,d = sum_t w_dt X_dt epsilon_w,dt, and their sums S_r and S_w.
Set H_r,N = E[G_N]/L_N and H_w,N = E[G_w,N]/D_N. The targets are
V_r,N = (N/L_N^2) H_r,N^-1 Var(S_r) H_r,N^-1 and
V_w,N = (N/D_N^2) H_w,N^-1 Var(S_w) H_w,N^-1.
The finite identities assume iid units, bounded measurable records with positive
record counts, N >= 2 and nonsingular H_r,N or H_w,N; fixed real weights suffice.
They identify these targets with the covariances of H_r,N^-1 (sqrt(N)/L_N) S_r
and H_w,N^-1 (sqrt(N)/D_N) S_w respectively.
Weak convergence with uniformly integrable squared scaled errors gives mean and
actual covariance convergence; subtraction of a convergent target is valid.
Bounded data and sample and population rank alone do not give those moments or
uniform integrability. The directed unit-weight witness satisfies the common-
kernel and positive limiting-design conditions. Deterministic covariance convergence
is exactly convergence in probability of constant random matrices. The usual
measure-theoretic conditions are assumed.
Restriction: For canonical clause (ii), retain only consistency under the following explicit C1 and C2
premises; equivalence with the unsupplied canonical P018-T10 hypotheses is not asserted. C1 assumes iid
units, measurable uniformly bounded common record-index pair kernels with an intercept, 1 <= T(N,d) <= T0
for one fixed T0, H_r,N tending to a positive definite H, and (N/L_N^2) times the sum over ordered
overlapping dyads d,f of E[b_d] E[b_f] transpose tending to zero, including diagonal pairs. C2 assumes iid
units, measurable uniformly bounded records with an intercept, at most two records per dyad, one common
ordered-pair kernel used in original or reversed endpoint order with injective Boolean record orientations,
deterministic weights with positive scales a_N and a uniform finite bound 0 < w_Ndt/a_N <= C, and H_(w/a),N
tending to a positive definite limit. These are substantive model and limit premises, not usual
measure-theoretic existence conditions. The finite covariance identities, UI-based actual-covariance
implication, moment-failure examples and deterministic-limit equivalence are retained. -/
theorem SAP.P018b.T20 : SAP.P018b.T20WholeStatement := by sorry

/-- P018-T21; p. 566 (PDF p. 3), equation (2), term B.
The expectation belongs before the braces in each neighbour summand. There are
2(N-2) neighbours per dyad, N(N-1)(N-2) ordered distinct-neighbour pairs and
D(2N-3) ordered overlapping pairs including the diagonal. The diagonal-plus-
neighbour conditional-covariance expression equals the sparse conditional sum
term by term. It is not the score variance in general: that variance is the
unconditional sparse score second moment. The bounded uniform nonlinear model
has zero conditional-covariance sum but the displayed nonzero score variance at
N=3. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P018b.T21 : SAP.P018b.T21WholeStatement := by sorry

/-- P018-T22; p. 569 (PDF p. 6), sentence after equation (4).
With the corrected symbol ν, mutually independent standard-normal covariates, unit effects and
observation errors give jointly Gaussian mean-zero compound errors, independent of all covariates.
Their covariance is the number of shared units plus the same-observation indicator (hence 3, 2,
1 or 0). Their conditional means given all covariates vanish. For equation (4), the conditional
response mean given the endpoint covariates, and given the regressors (1, |Xᵢ-Xⱼ|), is
β₀ + β₁|Xᵢ-Xⱼ|. Thus this regression is correctly specified, in particular for β₀ = 0, β₁ = 1
and T = 1 or 2. The usual measure-theoretic conditions are assumed; the finite moments used
below follow from the Gaussian input laws. -/
theorem SAP.P018b.T22 : SAP.P018b.T22WholeStatement := by sorry

/-- P018-T23; p. 576 (PDF p. 13), Appendix E.
The corrected logistic predictor, score derivatives, Jacobian, score products and their sums have the stated
formulas and dimensions, and the expected same-data score product is positive semidefinite.
The usual measure-theoretic conditions are assumed; in the generic expected-score-product
assertion the law is a probability measure and every score coordinate is square-integrable. -/
theorem SAP.P018b.T23 : SAP.P018b.T23Statement := by sorry

/-- P018-T24; p. 571 (PDF p. 8), Section 5, second paragraph; Table 1, p. 572 (PDF p. 9).
The nine exact dyadic/heteroskedastic standard-error ratios have the displayed values, minimum
24749/10734 and maximum 172/39, and are all below 5 and 10. Rounding to three decimals cannot
conceal a tenfold ratio: the exact row bounds are as displayed and at most 17/3. Each row has
D > C > H, with D/C ranging from 185/181 to 86/47. The international-organizations ratio is
11/8 < 1.64. On the full one-sided domains, |b| ≤ 23/2000 and se ≥ 15/2000 imply
|b|/se ≤ 23/15 < 1.64; independently, |b| ≥ 21/2000 and 0 < se ≤ 5/2000 imply
|b|/se ≥ 21/5 > 1.64. -/
theorem SAP.P018b.T24 : SAP.P018b.T24WholeStatement := by sorry

/-- The printed claim is false: the shared-unit covariance is outside the fitted two-independent-role family for
at least one N >= 3.
P018-T25; pp. 569–570 (PDF pp. 6–7); Supporting Information p. 2; p. 572 (PDF p. 9); replication scripts 1
(line 86) and 2 (line 78). -/
theorem SAP.P018b.T25 : SAP.P018b.T25Statement := by sorry

/-- The printed claim is false: the conditional-covariance identity and asymptotic-law conjunction fails even in
the class with eventual almost-sure sample rank.
P018-T26; p. 566 (PDF p. 3), Lemma 1; p. 573 (PDF p. 10), Appendix A. -/
theorem SAP.P018b.T26 : SAP.P018b.T26Statement := by sorry

/-- P018-T27; p. 567 (PDF p. 4), Proposition 1, equation (3);
pp. 573–574 (PDF pp. 10–11), Appendix B.
For iid units and a fixed bounded symmetric measurable dyad regression kernel
with an intercept and nonsingular population Gram matrix Q, the sandwich
estimator (3), formed using fitted residuals, satisfies N Vhat_N - V_N ->p 0.
Here beta = Q^(-1) E[XY], epsilon = Y - X' beta, and
V_N = (N/D^2) Q^(-1) Var(sum_d X_d epsilon_d) Q^(-1), with unconditional variance.
The usual measure-theoretic conditions are assumed. Population rank suffices;
the estimator uses the existing totalized inverse convention on singular samples.
The additional printed fitted-residual and moment conditions may be imposed,
but are unnecessary for this conclusion. -/
theorem SAP.P018b.T27 : SAP.P018b.T27WholeStatement_W3 := by sorry

/-- The printed claim is false: the fair-sign scalar specialization refutes the conjunction of the two limits
with the literal target 4/D.
P018-T28; pp. 567–568 (PDF pp. 4–5). -/
theorem SAP.P018b.T28 : SAP.P018b.T28Statement := by sorry

