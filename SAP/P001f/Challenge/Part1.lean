import SAP.P001f.Defs.WholeW1
import SAP.P001f.Defs.WholeW2
import SAP.P001f.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P001f
universe u v

/-- P001-T96, Section 7.2.6, p. 266 (PDF p. 284), with Sections 7.2.1 and
7.2.5, pp. 256 and 264: the canonical eighteen-unit counterexample to the
printed IPW/post-stratification equality has unique logit ML fit
(0, log 2), IPW estimate 59/36 and post-stratified estimate 1, with the displayed
fitted probabilities, observed fractions, score arithmetic and nonzero gap. -/
theorem SAP.P001f.T96 : T96Statement := by sorry

/-- P001-T97, corrected Section 7.2.6, p. 266 (PDF p. 284), Section 7.2.1, p. 256, and Example 7.2.1, p. 257: for every positive-size binary sample with both arms in each observed cell, the individual IPW and empirical plug-in estimators have the displayed cell formulas; saturated fitted propensities make them equal, and equality for every individual outcome vector holds if and only if the fitted propensity is the observed treated fraction in each cell. The specified six-unit plug-in estimate is 4/9. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001f.T97 : SAP.P001f.T97WholeStatement := by sorry

/-- P001-T98, Definition 7.2.7 and its following paragraph, p. 267 (PDF p. 285):
true-score arm weights have conditional mean one, their positive-size sample
averages have mean one, and both all-unit reciprocal weights have mean above one.
Restricted: retains those expectation assertions only; omits the displayed full
stabilized outcome-estimator formula, fitted-score denominator convergence and
efficiency assertions, and requires binarity and uniform overlap pointwise for
every observation in the infinite sequence. -/
theorem SAP.P001f.T98 : T98Statement.{u, v} := by sorry

/-- P001-T99, Section 7.3.1, p. 273 (PDF p. 291): the canonical two-point
counterexample with constant potential outcomes 0 and 1, covariate 0 and treated probability 1/4
satisfies conditional ignorability and both stated positivity bounds, while its
unnormalized weighted effect is 1/4, its ATT is 1, and normalization restores 1. -/
theorem SAP.P001f.T99 : T99Statement := by sorry

/-- P001-T100, corrected Section 7.3.1 sentence, p. 273 (PDF p. 291): under
conditional ignorability and an integrable treatment effect, the propensity mean
is the positive treatment probability, the weighted-effect identities hold, and
the normalized estimand equals ATT; the unnormalized equality holds exactly
when the treatment probability is one or ATT is zero. -/
theorem SAP.P001f.T100 : T100Statement.{u, v} := by sorry

/-- P001-T101, corrected set-subtraction row, p. 283 (PDF p. 301): relative complement is membership in A outside B and intersection with U minus B. The printed union identity holds exactly when A and B cover U and are disjoint, equivalently when A is U minus B. For U={1,2,3}, A={1,2}, B={2}, the difference and intersection are {1}, and the union is {1,2,3}. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001f.T101 : SAP.P001f.T101WholeStatement := by sorry

/-- P001-T102, Definition 4.3.7, p. 167 (PDF p. 185), footnote 13 on p. 166,
the remark on p. 168, and the standing footnote-14 condition on p. 70.
Restricted: the joint law does not determine one
PDA at the covariate mean, even with a joint density, two globally
differentiable versions of the same CEF, and the literal footnote-14 condition
that the sample range equals the chosen PDF's positive set, as Definition
1.2.20 defines support. The proposed counterexample has its mean in a gap
of that positive set; it is
not a null-set modification at an interior support point. The second conjunct merely unfolds the chosen
fitted CEF's plug-in formula. Its positive-sample-size and differentiability
premises describe the printed domain, but the Lean equality is definitional
and uses neither premise. This does not refute the derivative of a fixed
chosen extension or address the recommendation of discrete partial slopes. -/
theorem SAP.P001f.T102 : T102Statement.{u} := by sorry

/-- The printed claim is false: P001-T103, Section 5.2.5 and Example 5.2.11,
pp. 198–200 (PDF pp. 216–218), do not ensure a likelihood maximizer for every
positive sample in the stated normal/lognormal/exponential mixture.
Scope: refutes only maximizer-existence assertion (A) in that mixture;
omits both assertion (B)'s full-parameter consistency and its asymptotic
efficiency assertion, and makes no claim about the quality of the plotted fit. -/
theorem SAP.P001f.T103 : T103Statement := by sorry

/-- The printed claim is false: P001-T104, pp. 271–272 (PDF pp. 289–290),
cannot identify complete population overlap with uniform two-sided positivity
for every countable joint-mass distribution.
Scope: states only the negation of the unrestricted countable-mass
equivalence; does not prove assertion (A), separately isolate the directed
failure in (B), settle (C) under unspecified extra support conditions, or state
the regional propensity values in Example 7.3.3. -/
theorem SAP.P001f.T104 : T104Statement := by sorry

/-- P001-T106, Theorems 2.1.9, 2.1.13–14, 2.1.16 and 2.1.18, pp. 49,
52–53 and 55 (PDF pp. 67, 70–71 and 73): expectation is linear, variance and
standard deviation obey the printed affine rules, and standardized Chebyshev
holds with finite second moment and positive variance. -/
theorem SAP.P001f.T106 : T106Statement.{u} := by sorry

/-- P001-T107, Theorems 2.2.17–18 and 2.2.20, pp. 72–73 and 75–76 (PDF pp. 90–91 and 93–94): iterated expectation holds; with a finite second moment, total variance is expected conditional variance plus variance of the CEF. For every measurable predictor with finite prediction MSE, the exact MSE decomposition has a nonnegative remainder, the CEF minimizes MSE, and its residual risk equals expected conditional variance. The prediction assertion needs finite squared residuals, not a second moment of Y. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001f.T107 : SAP.P001f.T107WholeStatement := by sorry

/-- P001-T108, Theorems 3.2.3–5, pp. 97–99 (PDF pp. 115–117): every positive-size finite measurable iid family has an integrable sample mean with the common population expectation under a first moment. Under a second moment its variance is the population variance divided by n, and with positive population variance it obeys the displayed Chebyshev bound. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001f.T108 : SAP.P001f.T108WholeStatement := by sorry

/-- P001-T109, Theorems 4.3.2–3, pp. 158–159 (PDF pp. 176–177): Weierstrass
approximation holds, and on the paper's PMF/PDF full interval-support domain,
population polynomial least-squares minimizers exist at every degree and every
minimizing family eventually approximates the continuous CEF in mean square,
with finite prediction risks ensured by a square-integrable outcome. -/
theorem SAP.P001f.T109 : T109Statement.{u} := by sorry

/-- P001-T110, Example 5.2.3, pp. 187–189 (PDF pp. 205–207), footnote 9:
every nonempty binary sample has the unique Bernoulli likelihood maximizer equal
to its sample mean, including the endpoint samples, and the (1,0,1) example has
unique maximizer 2/3. -/
theorem SAP.P001f.T110 : T110Statement := by sorry

/-- P001-T111, Theorems 6.1.6, 6.1.9–10, pp. 213 and 216–217 (PDF pp. 231 and 234–235), with Examples 6.1.7 and 6.2.1, pp. 214 and 220: MCAR identifies the mean by respondents; MAR and uniform response overlap identify the vector CEF and the discrete positive-support mean, with population integrability derived rather than assumed. The empirical respondent and observed-profile formulas hold whenever their denominators are positive, and the six-unit estimates are 3/4 and 7/9. The usual measure-theoretic conditions are assumed. -/
theorem SAP.P001f.T111 : SAP.P001f.T111WholeStatement := by sorry

/-- P001-T112, Theorem 6.1.12, pp. 217–218 (PDF pp. 235–236): conditioning
on the true response propensity balances response and covariates, preserves MAR,
and gives a conditional response-probability version with a positive uniform
lower bound, without imposing an outcome moment assumption. -/
theorem SAP.P001f.T112 : T112Statement.{u} := by sorry

/-- P001-T113, Theorem 6.2.9, pp. 229–230 (PDF pp. 247–248): under MAR,
the augmented missing-data score has the outcome mean if either the respondent
regression is correct and the candidate propensity is bounded away from zero
and one, or the propensity is correct. The outcome and the complete displayed
score have finite expectations. No separate population integrability of the
nuisance regression is assumed. Conditional means, correctness, binarity and
overlap are interpreted as versions up to null sets; both response values have
positive probability. -/
theorem SAP.P001f.T113 : SAP.P001f.T113WholeStatement := by sorry

/-- P001-T114, Theorem 7.1.7 and its width and sharpness discussion,
pp. 241–244 (PDF pp. 259–262), and Example 7.1.6, p. 240 (PDF p. 258):
bounded potential outcomes and binary treatment with both arms of positive
probability give the printed conditional-arm ATE interval, of width b-a.
Every value in it is attained by bounded potential outcomes with the same
observable joint law. Individual endpoint imputations retain observed values
and bound the missing potential outcomes. For the six specified units, the
upper treated, lower control, lower treated and upper control mean estimates
are respectively 5/6, 1/6, 3/6 and 5/6, giving ATE endpoints -2/6 and 4/6. -/
theorem SAP.P001f.T114 : SAP.P001f.T114WholeStatement := by sorry
