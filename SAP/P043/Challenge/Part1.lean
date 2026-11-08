import SAP.P043.Defs.WholeW1
import SAP.P043.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P043

/-- P043-T1; p. 474 (PDF p. 12), below Table 4, referring to p. 473 (PDF p. 11).
The two specified validator constructions are exact randomized counterexamples
to an unconditional mediation comparison. In the linear construction all eight
states have mass 1/8, knowledge increases by 6/5, support increases by h/20 with
knowledge, M=3/50 and D=-3/50, and observed support cancels assignment pointwise.
Both arm laws, all covariances, population regression slopes, and structural
coefficient identities are as specified. In the integer construction all 1000
states have mass 1/1000; K(0)=8 and K(1)=9 for W<=4 or 10 for W=5, with W stored
as i.1.val+1. Knowledge, support and constant general knowledge respect the 2007
index ranges. All stated arm means, nested means and one-unit effects hold;
both support arm means are 59/25 and both support laws put mass 9/25 at 3.
In each construction D<0, M>0 and tau=0<M, so the design alone gives neither
tau>=M nor the null inference M<=0. The contextual comparison assuming D>=0
is not refuted. The usual measure-theoretic conditions are assumed; the
specified probability spaces are finite and all expectations exist. -/
theorem SAP.P043.T1 : SAP.P043.T1WholeStatement := by sorry

/-- P043-T2; p. 474 (PDF p. 12), below Table 4, and p. 473 (PDF p. 11).
For arbitrary probability laws with the five specified finite expectations,
independent nondegenerate assignment identifies the mediation decomposition,
its weak and strict sign comparisons and null inferences, the linear and
positive-first-stage ratio formulas, and the sufficient but unnecessary
channelwise sign condition; the fixed witness records failure without the net sign premise. -/
theorem SAP.P043.T2.{u} : T2Statement.{u} := by sorry

/-- P043-T4; p. 472 (PDF p. 10) and pp. 474-475 (PDF pp. 12-13).
The specified two-type and two five-type validator constructions satisfy fair
independent assignment, exclusion, consistency and a strictly positive first
stage. The two-type witness has the stated arm means and covariances, zero IV
and covariance ratios, increaser mass 2/3 and increaser effect one. Every increaser
crosses only margin 9 with increment one; every normalized nonnegative average
of these increments is one, different from the zero IV ratio. This includes
arbitrary probability averages, whose integrability is certified. Cancellation
explains the zero reduced form, and responses are nondecreasing with the stated
2008 index bounds. The five-type models have the specified complete conditional
and joint observable laws, common positive first stage 1/5 and zero reduced
form and IV ratio, but increaser probabilities 2/5 and 3/5 and effects one and
4/3 respectively. Every increase is one unit, so these are also the average
per-unit effects. No functional of the observable law recovers the increaser
effect in both admissible models, hence none works on the entire claimed class.
These are validator witnesses, not empirical claims about the curriculum.
The usual measure-theoretic conditions are assumed; all finite expectations
exist and every conditioning or ratio denominator used here is positive. -/
theorem SAP.P043.T4 : SAP.P043.T4WholeStatement := by sorry

/-- P043-T5; p. 472 (PDF p. 10) and pp. 474–475 (PDF pp. 12–13).
Individual knowledge monotonicity and a positive first stage yield the normalized
crossed-margin IV formula and its finite-population identities.
Restriction: the population has finitely many types with arbitrary nonnegative
weights summing to one; arbitrary probability laws, including nonatomic laws,
are not covered. Identification and covariance conclusions retain the aggregate's
monotonicity and positive-first-stage hypotheses. Omits signed-crossing value-set
membership for arbitrary nonmonotone models, the particular T4 down-type value
R(9) = -1, and the separate nonidentification assertion without monotonicity;
retains general bounded signed telescoping and the downward-crossing implication. -/
theorem SAP.P043.T5.{u} : T5Statement.{u} := by sorry

/-- P043-T6; equation (1), p. 471 (PDF p. 9), right column.
Correctly indexed stratum indicators select the nonreference offset, encode
the omitted reference indicator, and give the equivalent stratum-intercept equation. -/
theorem SAP.P043.T6 : T6Statement := by sorry
