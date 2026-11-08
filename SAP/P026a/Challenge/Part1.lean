import SAP.P026a.Defs.WholeW2
import SAP.P026a.Defs.WholeW1
import SAP.P026a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a

/-- P026-T1; pp. 145-147 (PDF pp. 11-13).
The printed claim is false: the uniform sharp-null designs on 00,01,11 and on the
fourteen six-bit allocations with three treated and T1 ≤ T2 satisfy positive
marginals, positive same-arm joints and distinct cluster indicators, but have
Pr(T1=1,T2=0)=0. Literal equation [34] contains 0/0 and is outside its domain.
For the two-cluster design the marginals are (1/3,2/3) and (2/3,1/3), both
same-arm joints and disagreement are 1/3, HT=(-9/4,0,9/4), and [35]=
(57/16,3/2,57/16). Its true variance is 27/8, the expected [35] is 23/8
and the bias is -1/2; [34] with the unavailable term omitted is always -9/4,
exceeding the true covariance -13/4 by 1. For the six-cluster design the treatment
marginals are (2/7,5/7,1/2,1/2,1/2,1/2), the same-arm minimum is 1/14 and the
disagreement minimum is 3/7 at {1,2}. The 00,01,11 groups have sizes 4,6,4,
HT values -3/20,0,3/20 and [35] values -619/3600,7/54,-619/3600. The true
variance is 9/700, the expected [35] is -269/6300 and the bias is -1/18;
the covariance is 27/175 and the zero-omitted [34] has expectation 202/175.
Both covariance biases are +1. These facts refute the support deduction,
conservativeness and the stated sharp-null equalities. Usual measure-theoretic
conditions are assumed and hold automatically for these finite laws. -/
theorem T1 : SAP.P026a.T1WholeStatement := by sorry

/-- P026-T2; p. 145 (PDF p. 11); pp. 146-147 (PDF pp. 12-13); Appendix E, p. 152 (PDF p. 18).
Adding the unavailable directed-pair bounds gives the exact covariance and variance biases, conservativeness, sharp-null equality characterization, and fixed-prediction residual versions, with the strict six-cluster witness. -/
theorem T2 : T2Statement := by sorry

/-- P026-T3; p. 147 (PDF p. 13); p. 137 (PDF p. 3); eq. [34], p. 146 (PDF p. 12).
Directed cross-arm support is not implied by the standing assumptions, and under that support the printed estimators have the stated biases, conservativeness and sharp-null equalities, also for fixed residuals, with the numerical design's stated attained support minima. -/
theorem T3 : T3Statement := by sorry

/-- P026-T4; p. 142 (PDF p. 8).
The printed claim is false: pairwise assignment independence does not pass through
an arbitrary nonlinear fit of several outcomes. In the six-unit complementary-XOR
design, independence holds exactly between different complementary pairs; the full
fitting sets are {3,4,5,6}, {1,2,5,6}, {1,2,3,4} for the three pairs. Each stated
fit uses two outcomes in its permitted set and equals its own treatment indicator.
The joint event that treatment and the fit are both one has probability 1/2,
while the product of their probabilities is 1/4, and their covariance is 1/4.
The generalized totals are both 3, the generalized ATE is always zero, and
HT=Delta=1. Its bias -1 agrees with [19]. In the three-unit XOR design all
distinct coordinates are independent with marginals 1/2; fitting the XOR of
the other outcomes again gives generalized ATE zero and bias -1. The alternative
product fit has covariance -1/8, expectation 7/6 and bias +1/6. All potential
outcomes and covariates are fixed as specified in the witness definitions.
Usual measure-theoretic conditions are assumed and automatic on these finite laws. -/
theorem T4 : SAP.P026a.T4WholeStatement := by sorry

/-- P026-T5; p. 142 (PDF p. 8).
Under the usual measure-theoretic conditions, independence of each focal treatment
from the whole assignment vector used by its fit, or more weakly from the whole
observed-outcome vector, passes through deterministic fitting and prediction and
gives zero covariance. If either premise holds for each unit, allowing a different
choice for each unit, both generalized totals and the ATE are unbiased. The fitting
prediction factors explicitly through the fitting assignment vector; the scalar
footnote follows for one outcome. A three-unit nonlinear fitting witness shows
that the scalar argument cannot replace vector independence in general. Pairwise independence suffices for additive
predictions with fixed coefficients, with the stated covariance expansion.
Mutually independent units justify leave-one-out fits, and independent block
vectors justify fitting on other blocks. The nonempty unit type is the guard for
the ATE denominator; finite assignment spaces make all measurability and moment
conditions automatic. Parameter fitting and fixed covariates can be absorbed in
the arbitrary deterministic real-valued map G in the unbiasedness clause. -/
theorem T5 : SAP.P026a.T5WholeStatement := by sorry

/-- P026-T6; Table 2, p. 149 (PDF p. 15); Table 1, p. 147 (PDF p. 13);
Section 7.1, p. 148 (PDF p. 14).
The printed claim is false: for the printed sixteen-unit population and its ninety
uniform allocations, the unique real OLS fits within blocks 2 and 1 are respectively
1/4+X/8 and 70/93+X/31. Opposite-block predictions have residual cluster totals
(1,7/8,1/4,-1/2,-15/31,19/93,1/3,-76/93,-76/93,-79/93).
The actual generalized estimator G has mean and bias zero, variance and expected
residual variance estimate 38307/634880 (approximately .0603374), and SE=RMSE
approximately .2456367. The residual variance estimate is unbiased and has variance
2400328658503/15687787688755200 and SE=RMSE approximately .0123696. The strict
rounding refutations for .026, .162 and .007 follow. For every allocation the OLS
regression on (1,T,block2,X) has a unique real minimizer; its treatment coefficient
is the specified residualized FE formula and both projection denominators are
positive. Its mean is approximately -.0139874, its variance .0777347, and its SE
.2788094, with the stated broad intervals and rounding refutations of -.012,
.036 and .191. Every approximation has error less than .00000005. Usual
measure-theoretic conditions are assumed and automatic for this finite law. -/
theorem T6 : SAP.P026a.T6WholeStatement := by sorry

/-- P026-T7; Table 2, p. 149 (PDF p. 15); Table 1, p. 147 (PDF p. 13);
Section 7.1, p. 148 (PDF p. 14).
For the printed population and ninety equiprobable assignments, the opposite-block
lines are the unique OLS fits, and FE (Cov.) is the unique OLS regression on
(1,T,block2,X). G (Linear) has mean zero, variance and expected equation [35]
variance estimate 38307/634880, and variance-estimator variance
2400328658503/15687787688755200. Its complete corrected column is
(0,0,0,.246,.246,.060,.060,0,.012,.012). FE (Cov.) has corrected ATE mean and
bias -.014, SE and RMSE .279, and variance .078, with the stated strict mean
and variance intervals; G (Linear) has the smaller RMSE.
All columns without X are unchanged: HT
(0,0,0,.429,.429,.184,.184,0,.037,.037), G (Prior)
(0,0,0,.302,.302,.091,.091,0,.020,.020), IPW
(0,-.014,-.014,.276,.277,.076,.071,-.005,.017,.018), and FE
(0,-.016,-.016,.283,.283,.080,.074,-.006,.019,.020).
HT and prior are unbiased, with variance equal to expected equation [35]
variance estimate 353/1920 and 233/2560, respectively. Their variance-estimator
variances are 10147/7372800 and 20083/52428800. IPW is WLS with inverse
observed-arm inclusion weights, and FE is OLS on (1,T,block2); both fits are
unique. Their clustered variance estimates use the explicit HC1 convention
(10/9)*15/(16-k), k=2,3. All inverses and arm denominators exist on every
assignment. The usual measure-theoretic conditions are assumed; here every
quantity is a moment of a function on a fixed finite probability space. -/
theorem T7 : SAP.P026a.T7WholeStatement := by sorry

/-- P026-T8; Appendix E, p. 152 (PDF p. 18); eq. [34], p. 146 (PDF p. 12).
The corrected Appendix E display estimates the covariance lower bound under directed support, with the exact gap and equality characterization. -/
theorem T8 : T8Statement := by sorry

/-- P026-T9; Appendix E, p. 152 (PDF p. 18).
The printed claim is false: for four singleton clusters with two treated uniformly,
and sharp-null outcomes (1,2,4,7), the literal Appendix E display has the six values
(-68,-52,2,-62,-20,-52) and expectation -42. Equation [34] has values
(-37,-25,-22,-22,-25,-37) and expectation -28, equal to the true covariance and
its population bound; the true treatment-total variance and its population bound
are both 28. Every marginal is 1/2 and all distinct-cluster joint probabilities
are positive (TT=CC=1/6, TC=1/3). Thus the printed display is unbiased for neither
of the quantities named in the text and on its left side. Usual measure-theoretic
conditions are assumed and hold automatically on this finite probability space. -/
theorem T9 : SAP.P026a.T9WholeStatement := by sorry

/-- P026-T10; p. 144 (PDF p. 10); p. 145 (PDF p. 11).
Grouping by the fixed cluster partition preserves each displayed HT total identity and the resulting ATE contrast. -/
theorem T10 : T10Statement := by sorry

/-- P026-T11; p. 146 (PDF p. 12); Appendix D, pp. 151-152 (PDF pp. 17-18).
The restored cluster-indicator formulas give the exact arm variance and conservative bounds, unbiased estimation of those bounds, and unbiased equation [31] under same-arm support. -/
theorem T11 : T11Statement := by sorry

/-- P026-T12; p. 143 (PDF p. 9).
Equations [20]-[24] hold with both intermediate arm-covariance expansions and the unavailable directed-pair terms retained. -/
theorem T12 : T12Statement := by sorry

end SAP.P026a
