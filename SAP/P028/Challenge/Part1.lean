import SAP.P028.Defs
import SAP.P028.Defs.WholeW1
import SAP.P028.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P028-T1; Section 4, p. 679, with the Section 2 assumptions, p. 678.
The two explicit seventeen-atom laws have the stated integer completions, positive
completed counts, Bernoulli parameters, conditional product construction, stratum
probabilities, source table, full and respondent moments, and different complier
means. They satisfy random assignment including response potentials and have the same
recorded-data law; neither complier mean is a real-valued function of that law in all
admissible models. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P028.T1 : SAP.P028.T1WholeStatement := by sorry

/-- P028-T2; Section 4, p. 679, repaired using Corollary 1, p. 678.
Joint moments identify complier means without positive treatment cells. The stated
mean equalities justify mixed respondent formulas; conditional response independence
suffices. Cellwise mean ignorability justifies reweighting but need not justify the
mixed formulas. With unrestricted response the stated bounds depend only on the
recorded-data law. All source-table values and approximations hold; both endpoints
of each source interval are attained, so no valid interval can be narrower. The usual
measure-theoretic conditions are assumed. -/
theorem SAP.P028.T2 : SAP.P028.T2WholeStatement := by sorry

/-- P028-T4; proof of Proposition 1, p. 678 (PDF p. 2), corrected intermediate system.
For 0 < p < 1 the corrected system is equivalent to the mixture equations and the
printed intervals, with the stated substitutions, endpoint translations, unique
noncomplier mean, and strict weakening caused by the printed residual constraint. -/
theorem SAP.P028.T4 : SAP.P028.T4Statement := by sorry

/-- P028-T5; proof of Proposition 1 after Eq. (3), p. 678.
The exact candidate (1/2,3/4,3/4,0,0) satisfies the printed system and fails
the constrained mixture equations: its forced noncomplier mean is 3/2. The two
printed feasible coordinate sets are [0,1], while the corrected mixture sets and
Proposition 1 intervals are [1/2,1]. The input triple has the specified realization
with half compliers of outcome one, half never-takers of outcome one half, and
independent fair assignment. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P028.T5 : SAP.P028.T5WholeStatement := by sorry

/-- P028-T6; Proposition 1 proof, p. 678, and Corollary 1 proof, p. 679.
A bounded causal model has positive complier probability at most one, and full
compliance is allowed. The noncomplier contribution gives the mixture identities,
the partial- and full-compliance branches, cell-compatible observable formulas,
both bounds, and singleton boundary intervals. Positive pure cells give the printed
probability-times-mean expression; empty cells have zero product moment. The usual
measure-theoretic conditions are assumed. -/
theorem SAP.P028.T6 : SAP.P028.T6WholeStatement := by sorry

/-- P028-T7; proof of Proposition 1, p. 678 (PDF p. 2), and Corollary 1 proof, p. 679.
An explicit two-atom randomized full-compliance law has the stated outcome means,
null noncomplier and pure-cell events, zero proof denominators and numerators,
undetermined noncomplier mean, and valid singleton Proposition 1 intervals. -/
theorem SAP.P028.T7 : SAP.P028.T7Statement := by sorry

/-- P028-T8; Proposition 1, Section 3, p. 678 (PDF p. 2).
Both complier means lie in the printed intervals, which are nonempty for every
compatible triple and attain every value through bounded randomized models,
including full compliance. -/
theorem SAP.P028.T8 {Ω : Type*} [MeasurableSpace Ω] : SAP.P028.T8Statement Ω := by sorry

/-- P028-T9; Corollary 1, Section 3, p. 678 (PDF p. 2), and its proof,
p. 679 (PDF p. 3), under the Section 2 assumptions.
The four ordinary finite treatment-assignment cell means and probabilities
determine both complier average potential outcomes. They reconstruct the arm
means and positive complier probability, the pure-stratum means and masses,
the printed noncomplier ratio, both mixture equations, and both displayed
complier formulas. Any two models with the same eight cell summaries have the
same complier means. The usual measure-theoretic conditions are assumed;
only observed cell moments are required, with no moment condition on unused
counterfactual outcomes. Positive conditioning events express existence of the
ordinary means in the premise. -/
theorem SAP.P028.T9 : SAP.P028.T9WholeStatement := by sorry

/-- P028-T10; Section 2 LATE display, p. 678, and Section 1, p. 677.
The population and observed treatment first stages equal the positive complier
probability. With the usual measure-theoretic conditions (in particular finite
observed arm means), the complier moments exist, the reduced form and both LATE
ratios hold, and measurable sample analogues give the Wald IV statistic. Two bounded
randomized models share the three reported figures and CACE but have different
complier levels. No moments on unused potential outcomes are assumed. -/
theorem SAP.P028.T10 : SAP.P028.T10WholeStatement := by sorry
