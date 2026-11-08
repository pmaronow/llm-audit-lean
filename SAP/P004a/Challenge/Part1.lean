import SAP.P004a.Defs
import SAP.P004a.Defs.WholeW1
import SAP.P004a.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

/-- P004-T1; Supplement A pp. 13-17, Proposition 4, eqs. (36), (42)-(43).
The printed claim is false: the balanced three-type spatial design satisfies every stated
hypothesis, with the displayed exact information, coefficients, effects and variance
constants. Its independent blocks have the stated exact second and fourth moments and the
positive uniform tail bound. An actual constrained logistic MLE has the corrected order-N⁻¹
expansion, so the printed root-N remainder fails to converge to zero. The fitted estimator's
Gaussian variance is 3/625, its printed-variance standardization has limiting variance
3600/1753, and intervals consistent for the printed variance have the stated strict coverage
deficit for every 0<α<1. -/
theorem SAP.P004a.T1 : SAP.P004a.T1WholeStatement := by sorry

/-- P004-T2; Supplement A pp. 14-17 (Appendix A.6: 'C 2', Proposition 4, eqs. (36)-(43)); article Section 6.4,
p. 759 (PDF p. 16).
The corrected IPW estimator has the expansion, exact representations, unbiasedness, variance formula, oracle
bounds, normal limit and conservative intervals in clauses (a)-(e).
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P004a.T2 {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] : SAP.P004a.T2Statement (Space := Space) := by sorry

/-- P004-T3; Supplement A pp. 15-16, observational residual, SAH variance and Proposition 4(i).
The printed claim is false: the specified N=8r two-group disk field and actual clipped
logistic MLE satisfy the stated assumptions, with singleton neighborhoods and zero AME.
The exact fitted estimator, coefficients, residual sum and double-weighted variance have
the stated formulas. The N=32 and N=64 variances and expectations give the stated strict
finite underestimation. The root-N Gaussian variance and scaled actual variance tend to
1/4, the pooled treatment fraction N₁/N and normalized residual sum R/N tend in probability
to 1/5 and 1/8, and the printed scaled variance and variance ratio tend to 2/25 and 8/25.
Every 0<α<1/2 has the stated exact limiting coverage strictly below 1-α. -/
theorem SAP.P004a.T3 : SAP.P004a.T3WholeStatement := by sorry

/-- P004-T4; Supplement A p. 15, definitions of the observational residual and SAH variance.
Use raw fitted residuals with squared inverse propensities. With both arms nonempty this
has the stated equivalent arm-count form; the printed weighted residual instead produces
fourth powers. Under independent assignment, symmetric self-containing neighborhoods and
zero covariance outside them, the variance of the residual contrast mean is bounded by
the stated conditional second moments, exactly the expectation of the raw SAH estimator.
In the T3 design its N-scaled limit is 1/2, compared with actual variance limit 1/4, and its
N=32 expectation is exactly 493725989/38038425600, above 18239/1505280. General fitted-IPW
intervals use the residuals of the corrected linearization as specified in T2. -/
theorem SAP.P004a.T4 : SAP.P004a.T4WholeStatement := by sorry

/-- P004-T5; pp. 763-764 (PDF pp. 20-21), interpretation of the sum of point Hajek estimates;
eqs. (2), (8)-(9), (16).
These examples refute the reading that an unweighted sum of point Hajek contrasts over a
partition equals the change in the normalized deforested area share of the union. Three
specified binary area fields on the two radius-one disk nodes realize Cases A, B and C.
All six bin areas, positive finite averages, all-assignment
shares and whole-region weighted averages have the stated values. At assignment (1,0),
each bin Hajek contrast is its AME and each six-bin sum is -17/500; the actual whole-region
contrasts and AMEs are -17/3000, 121/18000 and -7/1800. Case B reverses the sign and Case C's
sum is below every bin effect. Refining the same Case A field into eleven bins changes the
sum to -187/3000 while preserving its whole-region effect -17/3000.
No corrected empirical area effect is asserted for the application. -/
theorem SAP.P004a.T5 : SAP.P004a.T5WholeStatement := by sorry

/-- P004-T6; p. 763 (PDF p. 20), last paragraph, continued on p. 764 (PDF p. 21).
Actual area averages and their marginalized effects aggregate with bin masses, lie within bin bounds, and
positive scaling preserves randomization p-values.
Restriction: Retain the actual integral union identity, marginal means, node effects, node-average area
effect, range bounds, equal-mass mean formula, and positive-scale comparison and exact p-value invariance.
Omit the two negative assertions in (b): an unweighted sum outside the bin-effect range, and non-
identifiability from bin AMEs when node masses differ. Do not assert the application numbers, reported Monte
Carlo p-value or substantive beneficial-effects conclusion. -/
theorem SAP.P004a.T6 : SAP.P004a.T6Statement.{u} := by sorry

/-- P004-T7; p. 761 (PDF p. 18), Section 7; p. 756 (PDF p. 13), eqs. (21)-(22) and footnotes 14-15; Supplement A
p. 17 (A.7, eqs. (44)-(45)).
The repeated-star construction gives a finite adjustment-order reversal and a guarded asymptotic coverage
upper bound strictly below 95 percent.
Restriction: Retain the full finite twenty-node adjusted-order reversal and spatial, homophily,
nondegeneracy, cutoff-kernel and exact linearized-variance guards for the repeated-star witness. Replace the
exact limiting coverage equality by an eventual upper bound with the same explicit value, strictly below
19/20, counting only realizations with positive treatment and control counts, positive adjustment trace and
positive trace-square parameter. Omit the separate W1 spectral eigenvalue/trace/diagonal certificates, W2
block moments, W3 raw-variance, trace, variance-ratio and degrees-of-freedom limits, and the fitted-
estimator Gaussian law. The guarded upper bound is not a conditional-on-validity coverage probability. -/
theorem SAP.P004a.T7 : SAP.P004a.T7Statement := by sorry

/-- P004-T8; p. 761 (PDF p. 18), Section 7; p. 756 (PDF p. 13),
eqs. (21)-(22), footnote 15; Supplement A p. 17 (A.7).
Capping the positive-semidefinite HAC adjustment preserves variance ordering and
interval inclusion for every symmetric kernel. Every positive-degree Student
upper quantile dominates the normal quantile. Under C1-C5 and the variance floor,
the capped intervals have asymptotic coverage at least one minus alpha, including
arbitrary assignment-dependent positive Student degrees of freedom. Coverage
counts only draws with both arms nonempty. The repeated-star design has
well-defined uncapped intervals with probability tending to one and shows
that the uncapped rule has no such universal guarantee. -/
theorem SAP.P004a.T8 : SAP.P004a.T8WholeStatement.{u} := by sorry

/-- P004-T9; Supplement A pp. 13-14, C 1(iv),(vi) and Lemma A.6.
The boundary-constrained one-dimensional logistic MLE over [0,1], with constant
confounder one and true coefficient zero, satisfies all stated premises. Its
likelihood has the stated derivatives and unique clipped-logit maximizer; its
information, score remainder, exact moments and explicit finite tail lower bounds have
the displayed values. The score remainder fails to be smaller than root-N.
The scaled MLE converges to twice the positive part of a standard normal, while
the leading score term converges to twice a standard normal. Consistency and
the root-N rate hold. Thus the printed universal score expansion is false. -/
theorem SAP.P004a.T9 : SAP.P004a.T9WholeStatement := by sorry

/-- P004-T10; Supplement A pp. 13-14 ('C 1' item (iv)); p. 14 (Lemma A.6).
Compact membership gives logistic-MLE consistency and its root-N rate, while interior truth gives the
order-N^-1 and smaller-than-root-N score remainders. -/
theorem SAP.P004a.T10 : SAP.P004a.T10Statement := by sorry

/-- P004-T11; p. 759 (PDF p. 16), display defining $\hat\tau^{\mathrm{obs}}_{\mathrm{HT}}(d)$; Supplement A p. 4
(A.1.3, last line of the display).
Corrected observational HT is unbiased, the printed estimator has the stated expectation and exact equality
criterion, and the constant-outcome example has printed expectation minus two. -/
theorem SAP.P004a.T11 : SAP.P004a.T11Statement := by sorry

/-- P004-T12; p. 758 (PDF p. 15), Section 6.3, second paragraph.
The eight-node sharp-null design witnesses the signed-comparison defect and excess size of the uncorrected
absolute-statistic Monte Carlo test.
Restriction: Retain the specific eight-node sharp-null Witness A and its exact positive-probability draw
array, printed proportion, absolute exceedance count and corrected p-value, and Witness B with its exact
rejection sum greater than 1/20. Omit the separate universal negative-observation rule, the signed-statistic
size s/2 and decimal size approximations, and all of the seventeen-node, P=10000 Witness C and its exact
lower bound. Witness B uses the permitted nonnegative statistic absolute HT; no failure for every finite P
or for all sufficiently large P on one fixed design is asserted. -/
theorem SAP.P004a.T12 : SAP.P004a.T12Statement := by sorry

/-- P004-T13; p. 758 (PDF p. 15), Section 6.3, second paragraph.
The plus-one absolute-statistic Monte Carlo test has finite-sample level, the raw rule has the stated bound,
and the correction changes its p-value by the stated amount. -/
theorem SAP.P004a.T13 : SAP.P004a.T13Statement := by sorry

/-- P004-T14; p. 757 (PDF p. 14), sentence after eq. (26); eq. (2),
p. 747 (PDF p. 4), and eqs. (4)-(9), pp. 749-750.
All three explicit Euclidean witnesses refute the printed uniform-radius
disk/donut identity. The one-node atomic witness has radius effects zero and
one, uniform-radius mean one half, and band effects two thirds, with shell
weights one third and two thirds. The two-node witness has zero circle AMEs,
band AMEs one sixth, the stated individual effects and unequal shell weights,
and defeats every common pair of weights. For area on the unit disk the
continuous conditional circle-effect version is radius itself; radial area
has density 2r/(b squared minus a squared). Disk averages are two thirds versus
one half, and annulus averages seven ninths versus three quarters. Every atomic
and positive-area band average exists; singleton area circles are conditional
means. -/
theorem SAP.P004a.T14 : SAP.P004a.T14WholeStatement := by sorry

/-- P004-T15; p. 757 (PDF p. 14), sentence after eq. (26); eqs. (2), (7)-(9).
Band effects average marginalized point effects using node-specific shell masses. Continuous
circle effects are signed pushforward densities, with the actual shell means at positive
atoms. Finite shell decompositions and their node mean hold without common weights; common
weights give a weighted sum of circle AMEs. A common kernel works for every bounded measurable
profile if and only if all normalized node measures equal it. Circle AMEs alone do not
determine the band AME. Full planar annuli have density 2r/(b²-a²), including disks at a=0,
and their radial measure differs from the uniform radial measure.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P004a.T15 : SAP.P004a.T15WholeStatement.{u,v} := by sorry

