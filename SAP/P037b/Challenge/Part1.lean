import SAP.P037b.Defs.WholeW2
import SAP.P037b.Defs.WholeW1
import SAP.P037b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P037-T18; main p. 568 (PDF p. 3); main p. 569 (PDF p. 4), Results and Fig. 2 caption; SI p. 13 (supplement PDF p. 13); SI Tables S6 and S7, pp. 41–42 (supplement PDF pp. 41–42).
Residual multiplier refits have HC0 covariance, and homoskedastic HC0 has the stated positive semidefinite leverage shortfall.
Restriction: Retains the residual-multiplier covariance, leverage facts, homoskedastic HC0 shortfall, and positive-norm weighted-row algebra. Omits identification with the released R procedure, the second expanded Gram-inverse sandwich expression and coefficient standard-error/normal-Wald formulas in (a), and identification of the abstract row factor with the expected-to-true coefficient variance ratio.
-/
theorem SAP.P037b.T18 : SAP.P037b.T18Statement := by sorry

/-- P037-T23; main p. 569 (PDF p. 4), Fig. 2; SI Appendix p. 33 (supplement PDF p. 33), Fig. S6.
The exact 56-school fit has level variances 1/2800, contrast variance 1/1400 and the residual-control construction 1/5400.
Restriction: Retains the six-group inverse, normal-equation, residual-magnitude and HC0 certificates; both predicted means; all named variances and their comparisons; and the centered-fit certificates. Omits an explicit rank-3 assertion, the predicted-difference and variance-decomposition equations, the separate control-residual mean and sample-variance certificates, and the square-root interval-width conclusion or identification of released plotting code.
-/
theorem SAP.P037b.T23 : SAP.P037b.T23Statement := by sorry

/-- P037-T24; main p. 569 (PDF p. 4), Fig. 2; SI Appendix p. 33 (supplement PDF p. 33), Fig. S6.
A same-sample centered interaction refit estimates the contrast, whose variance differs algebraically from a treatment predicted-mean variance.
Restriction: Retains the algebraic prediction rows and mean difference, the symmetric-covariance decomposition/equality criterion, and same-sample full-rank recentering of coefficients, predictions, residuals and HC0 variance. Omits the normal-reference interval endpoints in (b), examples realizing both variance orderings in (c), the residual-control-band failure and concrete certificate in (e),(f), the explicit identification of the centered variance with a prediction quadratic form, and verification of the released plotting routines.
-/
theorem SAP.P037b.T24 : SAP.P037b.T24Statement := by sorry

/-- P037-T19; main p. 567 (PDF p. 2); Fig. 1 caption, main p. 568 (PDF p. 3); SI Appendix p. 10 (supplement PDF p. 10); the regressions are SI Eqs. (1)–(6), pp. 13–16.
Outcome-threshold selection changes the kept contrast expectation and the weighted-block probability limit despite constant effects.
Restriction: Retains constant effects pointwise and averaged over every nonempty subset, assignment-dependent kept sets, the complete six-assignment table, finite expectations, profiling crossproducts, and the probability limit of the explicitly defined weighted block ratio. Omits identification of that ratio as the OLS treatment coefficient in a general regression on block indicators.
-/
theorem SAP.P037b.T19 : SAP.P037b.T19Statement := by sorry

/-- P037-T20; main p. 567 (PDF p. 2); Fig. 1 caption, main p. 568 (PDF p. 3); SI Appendix p. 10 (supplement PDF p. 10).
Fixed inclusion identifies the kept-population mean by inverse-probability weighting, whereas varying inclusion introduces conditional inclusion factors.
Restriction: States only the finite inverse-probability identities (a),(b) and the same-side threshold sufficient condition in (c). Omits the sharp-null specialization, the referenced T19 counterexample and conditional inclusion probabilities in (d), and verification of the released scripts, data counts and reporting descriptions.
-/
theorem SAP.P037b.T20 : SAP.P037b.T20Statement := by sorry

/-- P037-T21; main p. 568 (PDF p. 3); SI Appendix pp. 14, 18 and 19 (supplement PDF pp. 14, 18, 19); Table S5 note, SI p. 40.
Two seed designs separate positivity from the 0.01 screen and give distinct seed/nonseed labels, with a supported simulated-frequency witness.
Restriction: Retains both exact local probability vectors, their raw exposure histograms, probability sums and positivity/cutoff comparisons, two supported seed/nonseed realizations, and the supported 10000-draw frequency witness. Omits the separate conditional mass 1/924 assertions for those two selections and the complete analysis-set membership-change assertion in W2(vii), including its outcome, baseline, school and simulated-frequency masks.
-/
theorem SAP.P037b.T21 : SAP.P037b.T21Statement := by sorry

/-- P037-T22; main p. 568 (PDF p. 3); SI Appendix pp. 14, 18 and 19;
Table S5 note, SI p. 40. Corrected canonical claim, 2026-11-04.
The positive-probability population equals the all-four-positive population;
the exact and simulated .01 screens have all stated inclusions, with strictness
in a legal design. Five-label probabilities sum to one, and the four indirect
probabilities sum to at most one. Zero exact probability forces zero supported
simulation frequency. Under 10000 independent design draws, exposure counts have
the binomial law, the scalar cutoff is count at least 101, and both scalar and
joint four-cutoff membership have probability strictly between zero and one for
students of the positive-probability population. A balanced supported sequence
passes, a constant sequence fails, and retained inverse frequencies are at most
10000/101 < 100. For each fixed supported simulation, the outcome-specific analysis
set excludes realized seeds, with exclusion probability at least the direct
probability. Positive seed probability alone permits a constant nonempty analysis
set; positive seed and positive inclusion probabilities together imply inclusion
probability at most one minus the direct probability and strictly between zero
and one, so the set is not almost surely constant. Predictions are averaged over
this same outcome-specific set with its own cardinality whenever it is nonempty;
the printed comparison averages over the fixed all-four-positive population.
The usual measure-theoretic conditions are assumed; here all laws are finite.
No historical or public-rerun sample size is asserted.
-/
theorem SAP.P037b.T22 : SAP.P037b.T22WholeStatement_W2 := by sorry

/-- P037-T29; SI Appendix p. 14; the general simulation statement and J are
on SI p. 18.
In the stated synthetic four-block, forty-eligible school, exactly one of 63504
uniform first-two-block selections avoids all ten peers; 31752 contain referent 0,
and 31751 hit only nonreferent peers. The exposure vector is
(1/2, 1/127008, 31751/127008, 1/4), sums to one, and is strictly positive and below one.
Every supported 10000-draw frequency misses the school-exposure probability by at
least that probability, with the stated sharper zero/positive-count alternatives,
regardless of dependence. For independent design draws, the count has the full
binomial law, expected count 625/7938, and zero-hit probability strictly between .9
and .95. The school-exposure frequency (count divided by 10000) has variance
127007/161310320640000, relative variance 127007/10000, and relative standard error
above 3.5. The control frequency has variance 1/40000 and standard
error 1/200. The usual measure-theoretic conditions are assumed; all quantities
here are finite sums under explicit finite product laws. This is a synthetic
witness and asserts no occurrence in the study.
-/
theorem SAP.P037b.T29 : SAP.P037b.T29WholeStatement := by sorry

/-- P037-T30; SI Appendix p. 14 and p. 18 (supplement PDF pp. 14 and 18).
Independent finite-design simulations have the stated binomial law, moments, precision bounds and blocked school-exposure formula.
-/
theorem SAP.P037b.T30 : SAP.P037b.T30Statement := by sorry

/-- P037-T31; SI Appendix pp. 14, 18 and 19–20 (supplement PDF pp. 14, 18, 19, 20); the design is on SI p. 5 and in Fig. S1, SI p. 24.
The school samplers have different support counts and pair probabilities, with exact eight-school second-moment changes in both directions.
Restriction: Retains actual 56-school support cardinalities and one pair probability for uniform 28-of-56 and 2-of-4 laws, the eight-school support witness and exact uncentered second-moment examples in both directions, and the general zero-mean/second-moment formula conditional on half school marginals. Omits the 56-school support inclusion and block-respecting probability, their exact ratio, universal school marginals/pairs/covariances, the complete eight-school pair-law family and explicit 34-state count, explicit zero means identifying the eight-school second moments as variances, and identification of the two 56-school outcome examples with their actual design variances.
-/
theorem SAP.P037b.T31 : SAP.P037b.T31Statement := by sorry

/-- P037-T32; SI Appendix pp. 14, 18 and 19–20 (supplement PDF pp. 14, 18, 19, 20); the design is on SI p. 5.
The blocked school mass normalizes, uniform selection gives the stated marginals and pairs, and local exposure probabilities have a half-treatment mixture form.
Restriction: Retains the blocked mass definition and its normalization/support count, general uniform-selection marginal/pair formulas, and the school-local mixture identity for normalized nonnegative school and seed masses. Omits explicit independence of the blocked components, the numerical specializations in (b), the control-versus-other-exposure specializations and explicit equality of exposure probabilities/populations/estimands under the two school laws in (c), the joint control-exposure/variance comparisons in (d), and certification of the released-sampler repair.
-/
theorem SAP.P037b.T32 : SAP.P037b.T32Statement := by sorry

/-- P037-T25; SI Appendix p. 17 (supplement PDF p. 17); main p. 567 (PDF p. 2) and p. 568 (PDF p. 3).
The two explicitly specified nomination networks give different exposures and positive exposure probabilities under the nomination and either-direction rows.
-/
theorem SAP.P037b.T25 : SAP.P037b.T25Statement := by sorry

/-- P037-T26; SI Appendix p. 17 (supplement PDF p. 17); main p. 567 (PDF p. 2) and p. 568 (PDF p. 3).
Either-direction peers decompose into outgoing and incoming-only nominations and obey the stated label and probability comparisons.
Restriction: Retains Boolean union-graph properties and the two count decompositions, the scalar equal-label criterion and pointwise implications, and normalized positive-weight scalar probability inequalities with strictness. Omits the graph-instantiated subset-count inequalities, the all-supported-assignments reciprocal-possible-seed sufficient condition in (d), referenced concrete examples in (f), and verification of the released-script and Fig. S5 descriptions; probability comparisons are stated for scalar counts satisfying r ≤ c and q ≤ b.
-/
theorem SAP.P037b.T26 : SAP.P037b.T26Statement := by sorry
