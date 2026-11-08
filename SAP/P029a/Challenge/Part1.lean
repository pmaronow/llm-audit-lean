import SAP.P029a.Defs.WholeW1
import SAP.P029a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P029a

universe u v

/-- P029-T1; Section 3.4, p. 499 (PDF p. 8), paragraph after Assumption 1.
The six-atom law satisfies the IV and received-treatment ignorability conditions, including
potential-pair independence, but fails latent ignorability and has the stated ATE and Wald values. -/
theorem SAP.P029a.T1 : T1Statement := by sorry

/-- P029-T2; Section 3.4, p. 499 (PDF p. 8), comparison following Assumption 1.
The two ignorability conditions are incomparable, as witnessed by the stated six-atom laws
with type masses (1/2, 1/4, 1/4). The baseline-selection law has constant effect one and
received-treatment means (1/2, 0) and (3/2, 1). Under randomized one-sided noncompliance,
received-treatment ignorability implies latent ignorability at every positive-mass profile
with positive compliance. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P029a.T2 : SAP.P029a.T2WholeStatement := by sorry

/-- P029-T3; Section 3.4, p. 499 (PDF p. 8), last sentence of the sufficiency paragraph.
The explicit binary-covariate laws refute the marginal and conditional independence readings,
with the stated nested probabilities, arm differences, ATEs, LATEs and population Wald ratios. -/
theorem SAP.P029a.T3 : T3Statement := by sorry

/-- P029-T4; Section 3.4, p. 499 (PDF p. 8), corrected heterogeneous-effect sufficiency
statement; Appendix equations (10) and (13), p. 504 (PDF p. 13).
For finite positive-mass covariate support, the weighted Wald identities, LATE and true-score
ICSW formulas, covariance gap, separate ATE sufficiency implications, both separation laws,
and both joint-independence sufficient conditions hold. For iid sampling and measurable
profile-based consistent score estimates, ordinary IV and estimated-score ICSW converge in
probability to the respective population ratios. The respective mean-equality premises give
ATE consistency; imposing both gives consistency of both estimators. The usual
measure-theoretic conditions are assumed. -/
theorem SAP.P029a.T4 : SAP.P029a.T4WholeStatement := by sorry

/-- P029-T5; supplement pp. A2, A5 and A7, homogeneous-noise design, Table A3 and Figure A3.
Two admissible 500-record homogeneous-effect inputs have the stated nonsingular design,
cross-products and recovered coefficients, and scoring about six instead of five reverses
the squared-error discrepancy even though positive weights preserve exact recovery. -/
theorem SAP.P029a.T5 : T5Statement := by sorry

/-- P029-T6; supplement pp. A2, A5 and A7, corrected homogeneous-noise scoring rule.
The effect is five, the corrected RMSE uses five for every positive replicate count, the coded
benchmark has the stated uniform moments, and the finite and population error-discrepancy
identities permit both signs on the admissible inputs. -/
theorem SAP.P029a.T6 : T6Statement.{u} := by sorry

/-- P029-T7; package icsw 1.0.0, compliance.score.R lines 43–48 and 81–92,
icsw.tsls.R lines 28–37 and package help; article Section 3.3, p. 498 (PDF p. 7).
Positive weights inside the logarithm leave all minimizers unchanged; a zero weight gives
infinite extended objective. In the sixteen-record one-sided witness, the actual unweighted
and weighted probit fits have scores (1/4,3/4) and (3/4,27/28), giving Wald estimates 3/2 and
17/10. Every ordered raw two-sided receipt array has finite nested-probit coefficients;
the stated two-sided arrays are the actual clipped package and corrected fits, with the
stated score differences and likelihood ratio. Under the positive weight perturbation,
actual refitting yields scores (1/(3+t),3/4) and the stated Wald curve with derivative
-1/16 at one, while the fixed-score estimate has derivative zero. These facts refute the
package help's interpretation that the supplied weights refit the compliance model.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P029a.T7 : SAP.P029a.T7WholeStatement := by sorry

/-- P029-T8; package icsw 1.0.0 and deposited icsw.R helper, corrected observation weights;
article Section 3.1, pp. 496–497 (PDF pp. 5–6).
Observation weights outside the logarithm satisfy the zero/unit and replication rules, give
unique free-cell fits, and preserve the stated constant-weight and numerical witness conclusions.
Restriction: Fitting certificates use free interior Bernoulli cell probabilities, including the
three concrete corrected fits, without identifying them with finite-coefficient one-sided or
nested two-sided probit fits. Drops the nonconstant-weight claim about distinct package and
corrected probit minimizers; the numerical Wald conclusions concern the specified score arrays. -/
theorem SAP.P029a.T8 : T8Statement.{u,v} := by sorry

/-- P029-T9; Section 4.1, p. 501 (PDF p. 10), and supplement Table A7.
The two 18,933-record completions preserve the specified recorded labels, compatible raw codes
and arbitrary outcomes, yet give opposite strict compliance/race associations in both directions.
Restriction: Omits the standalone general binary-count sign identity and independent assertions
about the staged-data summaries: the 4,660 Raleigh records, 8,721 assignments, 1,685 Raleigh
assignments, the 602/1370 and 160/315 Raleigh rates, and the 21 unknown-code records and their
breakdown. The nine-cell construction, its exported pooled counts and the assignment-support
certificate are retained; no raw data file is validated. -/
theorem SAP.P029a.T9 : T9Statement := by sorry

/-- P029-T10; Section 4.1, p. 501 (PDF p. 10), corrected interpretation of supplement Table A7.
Finite binary counts determine both association directions, the two Raleigh rational rate
comparisons are negative, compatible completions have opposite signs, and covariance decomposes
into the stated within-group and between-group terms.
Restriction: Drops the corrected prose's empirical claims about prior voting, fitted compliance
scores, the size of between-city contributions, party/race availability and zero coding, and
other covariate missingness and imputation. The completions here preserve binary race labels and
outcomes, without a raw-string-code assertion. The distinguished-group conditional covariance
formula additionally requires that group's probability to be positive. In part (b), only the
two displayed rational rate calculations are retained; the empirical identification of seven
treatment-assigned unknown-code records, five of them contacted, and the exclusion producing
155/308 are not certified. -/
theorem SAP.P029a.T10 : T10Statement.{u} := by sorry

/-- P029-T11; Section 2.2, p. 495 (PDF p. 4), comparison with the Section 2.1 SEM framework.
Both explicit constant-effect SEM laws have the stated exogeneity, relevance and endogeneity
moments, while one has defiers and the other lacks instrument/potential-outcome independence. -/
theorem SAP.P029a.T11 : T11Statement := by sorry

/-- P029-T12; Section 2.2, p. 495 (PDF p. 4), corrected comparison with Section 2.1.
The SEM witnesses and the heterogeneous all-complier IV law establish non-nesting, while the
SEM potential-outcome equations force a constant effect and the IV witness has ATE and LATE 3/2. -/
theorem SAP.P029a.T12 : T12Statement.{u,v} := by sorry

/-- P029-T13; Assumption 2, p. 500 (PDF p. 9), with the estimator on pp. 496–497.
The one-observation-per-arm closed-domain likelihood maxima give a biased compliance score,
with the stated certificates, raw-difference expectation and five-per-arm positive-part example;
boundary probabilities and the natural-power convention are part of the claim. -/
theorem SAP.P029a.T13 : T13Statement := by sorry
