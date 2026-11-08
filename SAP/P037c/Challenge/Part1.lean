import SAP.P037c.Defs.WholeW1
import SAP.P037c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P037-T35; SI Appendix pp. 29 and 32, Fig. S5 (pp. 30–32).
Own-seed outcomes alone give the stated one-block distribution, p-values and rejection
probability 8/63. With four disjoint copies the uniform support has size 252^4,
the copied observation has statistic -1, exactly two assignments have absolute statistic
1, and its exact two-sided p-value is 2/252^4. The usual measure-theoretic conditions
are assumed (all spaces and sums here are finite). -/
theorem SAP.P037c.T35 : SAP.P037c.T35WholeStatement := by sorry

/-- P037-T36; SI Appendix pp. 29 and 32, Fig. S5 (pp. 30–32).
The nomination statistic gives a valid exact test of the global sharp null, admits the stated
direct-effect decomposition, and can reject the reciprocal-pair schedule without social influence.
Both recipient denominators are positive whenever the general statistic is used as a mean. -/
theorem SAP.P037c.T36 {Ω I : Type*} [Fintype Ω] [Fintype I] :
    SAP.P037c.T36Statement Ω I := by sorry

/-- P037-T27; SI Appendix pp. 18–19; main p. 568 (PDF p. 3).
The specified twelve-unit potential outcomes give different separate and pooled WLS
means and contrasts under both weight vectors. E1 consists of independent uniform
four-category exposures, with every joint cylinder probability (1/4)^its size,
marginals 1/4, weights 4 and observed realization probability (1/4)^12 > 0.
E2 is the six-school seed design with focal probabilities (1/2,1/8,1/8,1/4),
realization probability 1/640 and weights (2,8,8,4). All stated coefficients,
residuals, means and contrast differences hold. The usual measure-theoretic
conditions are assumed (all spaces and sums here are finite). -/
theorem SAP.P037c.T27 : SAP.P037c.T27WholeStatement := by sorry

/-- P037-T28; SI Appendix pp. 18–19; main p. 568 (PDF p. 3).
On the same finite analysis set, joint and separate WLS give the stated zero residual sums,
standardized means, one-covariate coefficient formulas, and exact equality characterization. -/
theorem SAP.P037c.T28 {I : Type*} [Fintype I] : SAP.P037c.T28Statement I := by sorry

/-- P037-T33; SI Appendix pp. 19–20, also pp. 14–15.
The specified normalized 96-state abstract exposure design has the stated marginals,
ranks, point coefficients, standardized means and eight residuals. At every assignment
and every exposure the full-control imputed refit mean is the residual refit mean plus
the fixed point mean. The two full-control contrast variances equal Vfull; the collapsed
residual contrast variance equals Vcol, with 2 < Vcol < 5/2 < 9 < Vfull < 37/4.
Their standard deviations round to 1.53 and 3.03. The usual measure-theoretic
conditions are assumed (all spaces and sums here are finite). -/
theorem SAP.P037c.T33 : SAP.P037c.T33WholeStatement := by sorry

/-- P037-T34; SI Appendix pp. 19–20, also pp. 14–15.
For fixed units and controls, positive weights and full column rank, the printed
constant-effect imputation equals r + H_z theta, its WLS coefficients shift by theta,
and every standardized mean and contrast shifts by its fixed point value and has the
same variance as the residual refit. Fewer controls retain only the projection of the
omitted control contribution; this equals that contribution exactly when it belongs
to the reduced design space. The T33 design has a strictly smaller collapsed control
space, an omitted contribution outside the reduced design, and unequal variances.
Aliased presentations have the same unique fitted values after passing to a full-rank
basis, and the shift and variance identities hold for estimable means and contrasts.
The usual measure-theoretic conditions are assumed; finite normalized laws describe
distributions on the finitely many exposure assignments. -/
theorem SAP.P037c.T34 : SAP.P037c.T34WholeStatement := by sorry

/-- P037-T43; accepted 19 October review of E001; SI Eq. (2), p. 13,
repeated pp. 15–16; main p. 568 (PDF p. 3).
On any finite normalized design and complete four-school blocks, the stated raw first
moments and mean-spanning controls imply E[r]=0, E[r't]=0, E[r'V]=0 and E[r'z]=E[r'r].
If E[t't] is nonzero and K=E[r'r]>0, every actual expected-normal-equation solution
obeys b-beta=E[sum r_i T_i eta_i]/K; eta=0 implies b=beta for arbitrary fixed untreated
levels. A four-state binary complementary two-of-four certificate has compositions
1/4 or 3/4, nonconstant untreated levels, E[t't]=1, K=1/16 and an actual solution.
The usual measure-theoretic conditions are assumed (all spaces and sums here are finite). -/
theorem SAP.P037c.T43 : SAP.P037c.T43WholeStatement := by sorry
