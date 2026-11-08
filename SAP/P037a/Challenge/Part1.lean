import SAP.P037a.Defs
import SAP.P037a.Defs.WholeW1
import SAP.P037a.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P037-T1; SI Appendix pp. 13–14, repeated pp. 15–16 and Table S7
(p. 42); main p. 568. The exact four-school hierarchical design has the
stated treatment and conditional seed moments, feasible supports and 454
positive-mass collapsed states. Composition has zero causal slope, yet the
expected regression has the displayed matrices and unique slope -16/31;
the general response schedule gives (15 b1 + 16 b2)/31. Under independent
block repetition, every selection of actual least-squares minimizers has
composition coefficient converging in probability to -16/31. Minimizers
exist, and singular pooled Gram matrices have probability tending to zero.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P037a.T1 : SAP.P037a.T1WholeStatement := by sorry

/-- P037-T2; SI Appendix pp. 13–14 and 15–16 (supplement PDF pp. 13–16); main p. 568 (PDF p. 3).
Finite seed-law moments and explicitly imposed response and randomization conditions yield the stated population regression identification and witness comparisons.
Restriction: Replaces DM's treated-school conditional mean and variance by the exported unconditional moments under the uniform product seed law. Omits the joint school-assignment/seed-sampling construction and its conclusion E[D_i(C_i-mu_i) | D]=0. Condition (R) remains an explicit premise of the identification statements, as in the canonical claim; it is not derived from the unconditional moments. Retains the equal-fraction implication, unequal-strata example, response identification, decomposition, centered and uncentered orthogonality, zero-variation moment equality, positive-variation identification, augmentation equivalence and slope corollary, eligible-composition identities, and all witness regression comparisons. -/
theorem SAP.P037a.T2 : SAP.P037a.T2Statement := by sorry

/-- P037-T3; main p. 569; 2018 Correction p. E3598; SI Table S6 p. 41.
The two significance descriptions are incompatible. The strict rounding
bins give the same displayed estimate and standard error for two witnesses
with opposite actual two-sided normal Wald decisions. The exact ratio
envelope is (11/7,13/5), containing the unique normal 0.975 quantile, which
lies strictly between 1.95996 and 1.95997. The normal-tail comparisons at
1.9 and 2 and the six stated five-decimal approximations are certified;
rounding alone therefore does not determine significance. Decimal tail
approximations mean error less than 0.000005. The usual measure-theoretic
conditions are assumed. -/
theorem SAP.P037a.T3 : SAP.P037a.T3WholeStatement := by sorry

/-- P037-T4; SI Appendix Table S6 note p. 41 and Table S7 note p. 42.
For every number of schools at least two, normalized independent uniforms
give ratio-event probability 1/6. Normalized independent standard
exponentials have the constant-density Dirichlet(1,...,1) simplex law and
give probability 1/4, also the probability E1 < E2/3 and the integral of
exp(-v)(1-exp(-v/3)) on the positive half-line. These are different weight
laws, with probability difference -1/12. All normalization and ratio
denominators are positive almost surely. Positive common rescaling,
including normalization, preserves the unique WLS coefficients for positive
weights and full column rank. The usual measure-theoretic conditions are
assumed. -/
theorem SAP.P037a.T4 : SAP.P037a.T4WholeStatement := by sorry

/-- P037-T5; SI Appendix, Table S6, p. 41, and Table S7, p. 42
(supplement PDF pp. 41–42).
The Bayesian bootstrap uses the probability law with constant density (n-1)!
in the first n-1 open-simplex coordinates, supported on positive unit-sum weights.
For every n≥2, independent Exp(1) multipliers normalized by their sum have this
law; independent U(0,1) draws transformed by minus-log give independent Exp(1)
inputs and the same construction. The forward normalization map in coordinate
order (p₁,…,pₙ₋₁,t) and its inverse have absolute Jacobian determinants
t^{-(n-1)} and t^{n-1}, respectively. The joint density is t^{n-1} exp(-t)
on the open simplex times t>0 and zero elsewhere; its t-integral is (n-1)!.
The n spacings of n-1 ordered independent uniforms, including both endpoint
gaps, have the same simplex law. Direct independent uniform multipliers,
even after normalization, have a different law (ratio-event probabilities
1/6 versus 1/4). Positive common scaling preserves the unique full-rank WLS
coefficient, so raw and normalized uniform replicates agree. The usual
measure-theoretic conditions are assumed. These facts justify the conditional
relabel/recompute correction, without identifying the rule actually used or
supplying replacement standard errors. -/
theorem SAP.P037a.T5 : SAP.P037a.T5WholeStatement_W2 := by sorry

/-- P037-T6; main p. 566 (PDF p. 1), p. 569 (PDF p. 4) and p. 571 (PDF p. 6); 2018 Correction, p. E3598 (correction PDF p. 1).
The printed totals and rounding bins give the exact corrected percentage arithmetic and exclude deriving 25 percent from the two rounded mixed-basis numbers. -/
theorem SAP.P037a.T6 : SAP.P037a.T6Statement := by sorry

/-- P037-T7; SI Appendix p. 17 (supplement PDF p. 17).
Both feasible witness configurations satisfy two distinct printed exposure cases, and the overlap rules preclude a single-valued mapping. -/
theorem SAP.P037a.T7 : SAP.P037a.T7Statement := by sorry

/-- P037-T8; SI Appendix p. 17 (supplement PDF p. 17).
The five corrected exposure predicates partition every feasible configuration and give school and direct exposure on the two witnesses. -/
theorem SAP.P037a.T8 : SAP.P037a.T8Statement := by sorry

/-- P037-T9; SI Appendix p. 18 and p. 14 (supplement PDF pp. 18 and 14).
Independent finite-design exposure draws give unbiased frequency estimates with exact variance, a Chebyshev error bound and consistency, whereas the printed formula uses the last draw. -/
theorem SAP.P037a.T9 : SAP.P037a.T9Statement := by sorry

/-- P037-T10; SI Appendix p. 19 (supplement PDF p. 19); the design is on SI p. 5 and in Fig. S1, SI p. 24.
Two-of-four school assignment creates negative within-block treatment and control-exposure covariance, while independently randomized blocks have the stated product law. -/
theorem SAP.P037a.T10 : SAP.P037a.T10Statement := by sorry

/-- P037-T11; SI Appendix p. 19 (supplement PDF p. 19).
Independent retained-block totals give the finite unbiasedness and variance identities, bounds, consistency, Gaussian limits, contrast results, and fitted-estimator limits under the stated regularity conditions. -/
theorem SAP.P037a.T11 : SAP.P037a.T11Statement := by sorry

/-- P037-T12; SI Appendix p. 6 (supplement PDF p. 6); the related sentence is on main p. 567 (PDF p. 2).
The corrected integer interpolation rule has no ties, is monotone with the stated bounds and cap threshold, and gives the listed counts and eligible shares.
The listed examples refute the reading that the upper-cap parenthesis assigns exactly 64 seed-eligible students to every school with fewer than 550 students. The literal upper bound of no more than 64 for those schools remains true under this rule. -/
theorem SAP.P037a.T12 : SAP.P037a.T12Statement := by sorry

/-- P037-T13; main p. 569 (PDF p. 4), with Fig. 2D on the same page; SI Table S7, p. 42 (supplement PDF p. 42).
The printed coefficients and explicit coefficient and control-level intervals imply the stated treatment prediction and relative-reduction intervals. -/
theorem SAP.P037a.T13 : SAP.P037a.T13Statement := by sorry

