import SAP.P008a.Defs
import SAP.P008a.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P008-T1; p. 153 (PDF p. 16); the design sentences on p. 151 (PDF p. 14), p. 145 (PDF p. 8) and p.
142 (PDF p. 5).
The fixed labelled 121-node example and two four-node examples refute the reading that an observed
assignment and its treated count identify the design reference law; unrestricted and blocked tails
differ in either direction.
Restricted: Retains the explicitly labelled 121-node observation and its within-count swap, both
normalized supports, and both directions of the four-node tail discrepancy. Does not quantify over
every initial 60-treated observed assignment or assert the existence of a relabelling that puts it
into the recorded observation form. -/
theorem SAP.P008a.T1 : SAP.P008a.T1Statement := by sorry

/-- P008-T2; p. 153 (PDF p. 16); with p. 151 (PDF p. 14), p. 145 (PDF p. 8), p. 144 (PDF p. 7) and p.
142 (PDF p. 5).
Inclusive tails are calibrated under the actual finite design and conditional laws, common Bernoulli
designs become uniform given their count, and the spatial sharp-null statistic is imputable under
the stated restrictions.
Restricted: The spatial cumulative-test component is confined to Euclidean circles in a measurable
whole field, with integrability for every assignment on every evaluated circle; positive finite
circle mass and nonempty arms on the positive-probability conditional support make its averages and
ratios meaningful. Imputability is asserted for the cumulative statistic on that support, rather
than separately for each circle mean. The documentary seven-lottery design, its identification with
a particular conditional reference law, and the empirical significance/withdrawal conclusions are
not formalized. General finite-law calibration, conditioning, Bernoulli-given-count uniformity and
both directions of the four-node law discrepancy are retained. -/
theorem SAP.P008a.T2 : SAP.P008a.T2Statement := by sorry

/-- P008-T3; p. 144 (PDF p. 7); p. 146 (PDF p. 9); footnote 5, p. 148 (PDF p. 11); pp. 149–150 (PDF pp.
12–13).
The canonical counterexample refutes the level assertion for the specified interpolated-percentile
reading: a true sharp null has single-radius and cumulative rejection probability 1/3 at nominal
level 1/20 despite full enumeration. -/
theorem SAP.P008a.T3 : SAP.P008a.T3Statement := by sorry

/-- P008-T4; p. 144 (PDF p. 7); p. 146 (PDF p. 9); footnote 5, p. 148 (PDF p. 11); pp. 149–150 (PDF pp.
12–13).
On the six two-of-four assignments every linear contrast functional has inclusive p-value at least
1/3, and exact design-law and IID sampled-permutation tails are calibrated.
Restricted: Retains complementation, the one-third inclusive-tail lower bound for every linear
contrast functional, the mass and level obstruction for every nonempty rejection set, general exact
calibration, the IID sampled-permutation bound, and the sum 7.996 of the displayed estimates. Omits
the reconstructed unrounded observed statistic 7.99649 and its asserted rounded value 8.00, the six
reconstructed cumulative statistics and their exact observed p-value 1/3. The
interpolated-percentile counterexample is not repeated in this theorem; it is stated in T3. -/
theorem SAP.P008a.T4 : SAP.P008a.T4Statement := by sorry

/-- P008-T5; p. 145 (PDF p. 8); toy cutoff on pp. 147–148 (PDF pp. 10–11) and the table on p. 149 (PDF
p. 12).
The outcome-effect-range sufficiency reading is false: a cutoff equal to the range of outcome
effects need not cover dependence between node-level linearization contributions; the two-node
example and all its replicated pairs omit half the linearization variance at that cutoff.
This refutes the outcome-range reading, not the printed instruction to cover contribution
dependence, and establishes no coverage failure for the particular printed toy intervals. The
asymptotic consequence explicitly marked optional in the canonical statement is not asserted. -/
theorem SAP.P008a.T5 : SAP.P008a.T5Statement := by sorry

/-- P008-T6; p. 145 (PDF p. 8); pp. 147–149 (PDF pp. 10–12).
A cutoff below all off-diagonal node distances gives HC0, while the additive-score covariance and
geometric support bound identify the dependence a cutoff must cover.
Restricted: The weighted-contrast, OLS weight/residual and sandwich-to-score-HAC identities hold for
every nonnegative cutoff and general distance array when both arm counts are at least one; no
off-diagonal separation premise restricts that representation. Only the HC0 specialization requires
a zero diagonal and every off-diagonal distance to exceed the cutoff. Retains the reconstructed
toy-node cutoff and interval equalities, the additive-score covariance formula, the
diagonal/off-diagonal variance decomposition and exact cutoff condition. The geometric sufficient
bound remains restricted to the Euclidean plane, a measurable whole field and coefficient integrands
vanishing beyond the effect range on the whole plane, with positive finite circle masses. Omits the
numerical smallest-distance approximation 1.4295... and reproduction of the ten printed interval
pairs to three decimals. Also omits the canonical warning that cutoff c = r need not suffice; the
counterexample referenced as P008-T5 is not asserted by this declaration. -/
theorem SAP.P008a.T6 : SAP.P008a.T6Statement := by sorry

/-- P008-T7; p. 153 (PDF p. 16).
The specified four centres, four radii and 40,000 distinct rational directions give
640,004 distinct planar field points and exactly 40,000 points on each counting circle.
Both complete binary outcome schedules vanish at the centres. Under independent
Bernoulli(1/2) assignment, their actual spatial circle means, effects and Hajek estimates
give the stated sums -0.0321 and -4. Uniform sampling from the 640,000 planar circle
points gives risk difference -0.008025, preserved by every normalized radius weighting;
adding the unweighted sum to baseline risk gives a negative number. The companion
sum -4 cannot be a difference of probabilities. This is the specified synthetic
counterexample to the probability interpretation, with no empirical reconstruction. -/
theorem SAP.P008a.T7 : SAP.P008a.T7WholeStatement := by sorry

/-- P008-T8; p. 153 (PDF p. 16).
Normalized radius mixtures yield probability differences and a common positive rescaling preserves
tail comparisons and divides finite type-7 percentiles by the same factor.
Restricted: The fixed-radius spatial-risk component requires Euclidean circles and a measurable
whole field; positive finite circle masses and integrability of exactly the positive-weight one-node
overrides make the averages meaningful. Retains the generic convex-mixture probability bounds and
identity, bounds against any common lower and upper effect bounds, equal-weight and constant-effect
algebra, the -4 binary example, sorted finite-sample rescaling, the three reported values divided
by four, and the comparisons -0.0321 < -0.0304 and -0.008025 < -0.0076. Does not explicitly state
finite minimum/maximum values or a separate order-statistic characterization beyond the type-7
formula on a sorted sample, and does not construct the joint node/radius/point sampling probability
space. The -4 example uses the labelled counting model of T7 and does not assert its planar
realization. The numbers -0.0304, -0.0321 and 0.0336 enter only as supplied rational constants:
omits the identification of -0.0321 as the actual observed sum and of -0.0304 and 0.0336 as the
actual 0.025 and 0.975 sharp-null permutation percentiles of the summed AMR statistic on the stated
1-2.5 km window and grid, and hence the empirical assertion that the observed sum lies below the
lower reference quantile (only the numerical comparison is stated). Also omits the specification of
the actual application grid and unit weights, the identification of the actual equal-radius mean
estimate with -321/40000 = -0.008025 (printed as approximately -0.0080, a 0.8 percentage-point
reduction) or with the normalized sampling target, and any certification that the divided values
are reconstructed permutation outputs; only exact division by four and comparison are established. -/
theorem SAP.P008a.T8 : SAP.P008a.T8Statement := by sorry

/-- P008-T9; article p. 145 (PDF p. 8); supplied archived computation;
toy call and table pp. 148–149 (PDF pp. 11–12).
The specified planar counterexample has the displayed OLS coefficient, residual,
contrast-weight and score vectors. The cutoff-plus-position rule uses the identity
kernel at position one and the adjacent-pair kernel at position two, giving variances
1 and 1/2 for the same radius and data. In every four-node configuration in [0,4]^2,
the sixth-position bandwidth covers all pairs; the normal equations force variance
and interval width zero, incompatible with the printed sixth-row width 3.476.
The assertion concerns the supplied computational model and its physical-cutoff reading. -/
theorem SAP.P008a.T9 : SAP.P008a.T9WholeStatement := by sorry

/-- P008-T10; article p. 145 (PDF p. 8); supplied archived computation.
Retaining cutoff as the final node-pair bandwidth makes the actual OLS sandwich
variance independent of grid position and gives variance 1 on both example grids.
The normal equations make every all-pairs regression variance zero. For the toy nodes,
cutoff 0.4 is the identity kernel and gives HC0, equal to cutoff zero and positive
exactly when some actual OLS residual is nonzero; the archived sixth-row variance is
zero. A proposed physical-radius enlargement requires its own dependence justification. -/
theorem SAP.P008a.T10 : SAP.P008a.T10WholeStatement := by sorry

/-- P008-T11; p. 149 (PDF p. 12), last two lines; table on the same page.
The five displayed estimates sum to 7.996 with certified rounding bounds, whereas the eight
displayed estimates sum to 12.376 and round to 12.38.
Restricted: Retains the exact sums of the displayed five and eight estimates, the full rounding
envelope for the five estimates, the exclusion of a displayed sum 12.38, and the strict comparison
with every number displayed as 7.97. Omits the identification of the actual unrounded cumulative
effect as 7.99649 and its corrected display as 8.00; the rounding envelope alone does not establish
that actual display. The kept empirical permutation percentiles -7.97 and 7.97 are not certified as
outputs. -/
theorem SAP.P008a.T11 : SAP.P008a.T11Statement := by sorry

/-- P008-T12; p. 153 (PDF p. 16).
The canonical grid/output incompatibility holds: the printed grid selects no radius in the test
window, so every observed and permutation sum and every finite type-7 percentile is zero, unlike the
three reported values. -/
theorem SAP.P008a.T12 : SAP.P008a.T12Statement := by sorry

/-- P008-T13; p. 153 (PDF p. 16); Figure 8, p. 154 (PDF p. 17).
The corrected 41-point grid selects exactly the four radii 1, 1.5, 2 and 2.5 km and sums exactly
their four estimates. -/
theorem SAP.P008a.T13 : SAP.P008a.T13Statement := by sorry

/-- P008-T14; p. 143 (PDF p. 6).
The corrected AMR display is the average of node-level differences, whereas its literal printed
product agrees with that average only at 0 or 1 and gives 16 instead of 4 in the recorded example. -/
theorem SAP.P008a.T14 : SAP.P008a.T14Statement := by sorry
