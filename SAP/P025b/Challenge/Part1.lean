import SAP.P025b.Defs
import SAP.P025b.Defs.WholeW1
import SAP.P025b.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P025-T12; pp. 239-240 (PDF pp. 5-6); Supplement p. 2.
The printed claim is false: the two-unit census with outcomes (0,1) and equal
probability bounds has threshold values 1/2 and different least stopping indices.
It refutes the Appendix implication and cut equivalence and both Supplement
equivalences. Its feasible box is a single
point; all sample and class endpoints and both means are 1/2. The first upper
cut is one and its physical optimizer and displayed value still give 1/2.
-/
theorem SAP.P025b.T12 : SAP.P025b.T12WholeStatement := by sorry

/-- P025-T13; p. 238 (PDF p. 4); proof in the Supplement, p. 2.
Under independent Brewer replication, both actual pooled extrema converge almost surely to the class optimization endpoints without separation, and hence also with the finite-index Assumption 2.
-/
theorem SAP.P025b.T13 : SAP.P025b.T13Statement := by sorry

/-- P025-T14; p. 238 (PDF p. 4).
The printed claim is false: the six-unit random pair design satisfies independent
Brewer replication and violates Assumption 2, yet every nonempty pooled sample
has endpoints 5/4 and 2 on every path. Both polynomial certificates and all three
optimizer evaluations hold. Pooled class sums lie in [2h,4h], give the displayed
ratio and its normalization by h, and map onto the entire class weight box.
-/
theorem SAP.P025b.T14 : SAP.P025b.T14WholeStatement := by sorry

/-- P025-T15; p. 237 (PDF p. 3), echoed on pp. 235 and 238;
Supplement pp. 1-2.
Conditional only on positive limiting shares and with population size unrestricted,
the class box endpoints are the sharp infimum and supremum of compatible finite
population means. The box maps onto the proportion region; its rational points
are precisely finite population proportions, with the stated endpoint attainment
criteria. Compatibility is automatic at ratio greater than one and is equivalent
to rational shares at ratio one. Positive scaling preserves the objectives and
endpoints. Bounded class marginals are realized by finite sampling designs.
Absolute totals and known size give the stated integer calibration and outer
bounds; sharpness can fail with totals retained or with shares and size retained.
-/
theorem SAP.P025b.T15 : SAP.P025b.T15WholeStatement := by sorry

/-- P025-T16; p. 237 (PDF p. 3); Supplement p. 2.
These examples refute the reading of the printed sharpness assertion that retains
absolute class totals, with population size also retained in the second example:
retained absolute totals can force the singleton mean
set {2/3} strictly within [4/7,3/4], even when Assumption 2 holds. With totals
(50,100) and size 1000 the exact means are k/1000 for 500 ≤ k ≤ 750, whose
maximum 3/4 is below the continuous upper endpoint 4/5. All four specified
weight vectors give the stated endpoints. Every such integer k is realized by
independent uniform quota sampling with the specified probabilities and totals;
the 500-zero, 500-one example has mean 1/2 and probabilities 1/10 and 1/5.
Independent replication holds, outer bounds remain valid, and shares alone
with unrestricted size have the corrected sharp endpoints.
-/
theorem SAP.P025b.T16 : SAP.P025b.T16WholeStatement := by sorry

/-- P025-T17; p. 238 (PDF p. 4).
The inferred counts determine all 42 corrected Table 1 cells, reproduce the printed cells from rounded inputs, and preserve all gallery/exchange grid comparisons.
-/
theorem SAP.P025b.T17 : SAP.P025b.T17Statement := by sorry

/-- P025-T18; p. 236 (PDF p. 2).
The attainable set and its extrema depend only on the ratio of probability bounds and reduce to the sample mean at ratio one.
-/
theorem SAP.P025b.T18 : SAP.P025b.T18Statement := by sorry

/-- P025-T19; p. 237 (PDF p. 3); proof in the Supplement, p. 1.
For a sorted sample of at least two outcomes and 0 < alpha <= beta <= 1,
the upper and corrected lower least cuts exist uniquely and select feasible
optimal physical weights. Every tied pair receives equal weights. When
gamma = beta/alpha > 1, equality of adjacent weights is equivalent to the
cut not separating that pair, so neither cut separates tied observations.
All finite threshold formulas have positive denominators. For constant
outcomes the upper cut is zero and every upper weight is 1/alpha;
otherwise the zero-cut upper value is the sample mean, strictly above the
first outcome, and the upper cut is positive. At each adjacent tie at or
before either cut, the preceding test fails strictly, the corresponding
Supplement numerator/residual recurrence propagates strict failure, and
the next cut index is still at or before the selected cut.
-/
theorem SAP.P025b.T19 : SAP.P025b.T19WholeStatement := by sorry

/-- P025-T20; p. 237 (PDF p. 3).
Every nonempty binary sample has exactly the displayed attainable interval and
optimization endpoints, including zero, one, and equal probability cases. The
classes have counts np and n(1-p); their normalized weight sums A and C give
the ratio A/(A+C), satisfy the stated bounds, and make that ratio nondecreasing
in A and nonincreasing in C.
-/
theorem SAP.P025b.T20 : SAP.P025b.T20WholeStatement := by sorry

/-- P025-T21; p. 238 (PDF p. 4); proof in the Supplement, p. 2.
Under Assumptions 1 and 2 on the valid finite cut range, both actual pooled endpoints converge almost surely to the limiting class extrema.
-/
theorem SAP.P025b.T21 : SAP.P025b.T21Statement := by sorry

