import SAP.P010.Defs.WholeW1
import SAP.P010.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

/-- The printed claim is false: the unweighted preference interval for 90–90 is disjoint from each other arm.
P010-T1; pp. 578–579 (PDF pp. 7–8); Figure 1, p. 577 (PDF p. 6); Figure 2, p. 585 (PDF p. 14). -/
theorem SAP.P010.T1 : SAP.P010.T1Statement := by sorry

/-- P010-T2; pp. 578–579 (PDF pp. 7–8); Figure 2, Panels D–E, p. 585 (PDF p. 14).
Exact trimming counts and endpoints give approval overlap and positive preference separations under both trimming rules. -/
theorem SAP.P010.T2 : SAP.P010.T2Statement := by sorry

/-- The printed claim is false: both continuous witnesses have the same observables and violate the printed bounds that omit passing from conditioning.
P010-T3; p. 575 (PDF p. 4). -/
theorem SAP.P010.T3 : SAP.P010.T3Statement := by sorry

/-- P010-T4; p. 575 (PDF p. 4).
The corrected finite-branch trimmed means bound all compatible always-passer means, attain both endpoints, and have the stated quantile-integral forms. -/
theorem SAP.P010.T4 : SAP.P010.T4Statement := by sorry

/-- The printed claim is false: the specified full-support observed law has finite sharp passer-mean endpoints zero and one.
P010-T5; p. 575 (PDF p. 4); matching clauses of the proof, p. 580 (PDF p. 9). -/
theorem SAP.P010.T5 : SAP.P010.T5Statement := by sorry

/-- P010-T6; p. 575 (PDF p. 4); matching clauses of the proof, p. 580 (PDF p. 9).
The corrected else-branch bounds are the passer essential endpoints, sharp as extrema and unattained when finite. -/
theorem SAP.P010.T6 : SAP.P010.T6Statement := by sorry

/-- P010-T7; pp. 579–580 (PDF pp. 8–9).
The canonical four-state counterexample has common checks and per-arm ignorability,
fails joint-vector independence by the displayed 1/4 versus 1/8 factorization,
and satisfies the Corollary 1 mean identity, refuting the printed joint-independence step. -/
theorem SAP.P010.T7 : SAP.P010.T7Statement := by sorry

/-- P010-T8; pp. 579–580 (PDF pp. 8–9).
Common check status gives the arm-by-arm independence, positive passing probabilities and conditional-mean identities used in Corollary 1. -/
theorem SAP.P010.T8 : SAP.P010.T8Statement := by sorry

/-- P010-T9; p. 581 (PDF p. 10); Table 1, p. 582 (PDF p. 11).
The canonical two simulation designs have different observable passer laws and rigorously
separated population bound widths, establishing the counterexample to the printed comparison of rows 1 and 4. -/
theorem SAP.P010.T9 : SAP.P010.T9Statement := by sorry

/-- P010-T10; p. 581 (PDF p. 10); Table 1, p. 582 (PDF p. 11).
Bounds are invariant at a fixed observable law; when λ ≠ 0, changing a feasible correlation
changes the simulation's passer laws and means, and the two specified designs have different bound widths. -/
theorem SAP.P010.T10 : SAP.P010.T10Statement := by sorry

/-- P010-T11; p. 578 (PDF p. 7).
Counterexample to the exact-distribution-matching reading of the printed weighting guidance:
with replication membership coded 1, the attained two-cell logistic fit and printed odds
give weighted share 27/28 instead of the original 1/4; reciprocal odds recover the original distribution. -/
theorem SAP.P010.T11 : SAP.P010.T11Statement := by sorry

/-- P010-T12; p. 578 (PDF p. 7), corrected footnote 7.
With true study propensities and positive common-support probability densities,
Bayes' odds identities hold. The odds of original-study membership transport
the replication density to the original density, and a positive constant in
the weights cancels. Coding original membership one gives these same odds.
Printed odds instead give the normalized squared-density ratio when its
extended mass is finite and positive; this equals the original density exactly
when the two densities agree almost everywhere. If that mass is infinite,
the printed weighted mass is infinite and no finite nonnegative constant
normalizes it to a probability measure. Counting measure includes discrete
covariates. These identities concern true propensities, without a claim of
exact balance for a fitted logistic propensity. -/
theorem SAP.P010.T12 : SAP.P010.T12WholeStatement := by sorry

/-- The printed claim is false: the normal witness has zero always-passer mean and a strictly negative printed upper bound.
P010-T13; p. 580 (PDF p. 9). -/
theorem SAP.P010.T13 : SAP.P010.T13Statement := by sorry

/-- P010-T14; p. 580 (PDF p. 9).
Upper-tail selection attains the maximum at fixed mass, is monotone in the discarded share, and gives the corrected potential upper bound. -/
theorem SAP.P010.T14 : SAP.P010.T14Statement := by sorry

/-- P010-T15; p. 580 (PDF p. 9).
The potential and observed passer laws and trimming shares agree; for a trimming ratio below one their upper-tail means agree and give the corrected observable upper bound. -/
theorem SAP.P010.T15 : SAP.P010.T15Statement := by sorry

/-- P010-T16; p. 580 (PDF p. 9).
The explicit three-stratum witness has zero unit effects and a positive selected contrast of one half for every interior assignment probability. -/
theorem SAP.P010.T16 : SAP.P010.T16Statement := by sorry

/-- P010-T17; p. 574 (PDF p. 3), corrected Assumption 3.
Admissible populations are required to have positive probability of passing
the manipulation check in every treatment arm: Pr(S=1 | Z=z)>0.
Under the standing probability-law and ignorability assumptions, this is
exactly the additional requirement in the population assumptions, and all
conditioning denominators are positive. The requirement is determined by
the observed joint law of (S,Z); populations with the same observed law agree
on whether it holds. This is an imposed assumption, with no additional premise
about potential passing and no assertion of certainty from a finite sample. -/
theorem SAP.P010.T17 : SAP.P010.T17WholeStatement := by sorry

/-- P010-T18; p. 574 (PDF p. 3); proof in Appendix A, pp. 579–580 (PDF pp. 8–9).
Common potential check status identifies the always-passer effect by the selected observed contrast. -/
theorem SAP.P010.T18 : SAP.P010.T18Statement := by sorry

/-- P010-T19; p. 574 (PDF p. 3).
Arm means identify potential means and their difference identifies the intent-to-treat effect. -/
theorem SAP.P010.T19 : SAP.P010.T19Statement := by sorry

/-- P010-T20; p. 574 (PDF p. 3); the proof remark is on p. 575 (PDF p. 4).
Common potential check status implies independence of observed check status and assignment. -/
theorem SAP.P010.T20 : SAP.P010.T20Statement := by sorry

/-- P010-T21; p. 575 (PDF p. 4); proof in Appendix A, p. 580 (PDF p. 9).
A population with check status independent of assignment has positive conditioning masses, finite ordinary conditional means, and unequal selected and always-passer contrasts. -/
theorem SAP.P010.T21 : SAP.P010.T21Statement := by sorry

/-- P010-T22; p. 576 (PDF p. 5).
Common potential check status implies covariate balance conditional on observed check status. -/
theorem SAP.P010.T22 : SAP.P010.T22Statement := by sorry

/-- P010-T23; p. 576 (PDF p. 5).
A covariate-balanced population has positive conditioning masses, finite ordinary conditional means, and unequal selected and always-passer contrasts at zero covariates. -/
theorem SAP.P010.T23 : SAP.P010.T23Statement := by sorry
