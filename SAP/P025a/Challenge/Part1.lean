import SAP.P025a.Defs
import SAP.P025a.Defs.WholeW2
import SAP.P025a.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P025-T1; p. 236 (PDF p. 2).
The realizable two-unit sample refutes the printed lower rule: its true range is
[1/3,2/3], with the displayed residual certificates and independent inclusion
indicators. For every sorted nonempty sample the printed rule stops at zero;
the sample-mean residual and exact one-coordinate change explain its strict
nonoptimality whenever the bound ratio exceeds one and the outcomes vary. -/
theorem SAP.P025a.T1 : SAP.P025a.T1WholeStatement := by sorry

/-- P025-T2; p. 238 (PDF p. 4), below Table 1; (7), p. 237 (PDF p. 3).
The two-class design, with independent Brewer replication, has singleton
classes, totals (1/2,1), true weights (2,1), and mean 1/2. The printed lower
cut gives 2/3, while the true extrema are 1/2 and 4/5, certified by the two
displayed residuals; the upper first cut is one and Assumption 2 holds.
For all strictly ordered positive class totals the printed rule stops at zero
and is strictly nonoptimal when the bound ratio exceeds one and there are at
least two classes. -/
theorem SAP.P025a.T2 : SAP.P025a.T2WholeStatement := by sorry

/-- P025-T3; p. 236 (PDF p. 2); Appendix, pp. 239-240 (PDF pp. 5-6).
Both corrected first cuts exist. Their prescribed feasible threshold vectors
attain the global minimum and maximum and the full interval of ratios.
The objective is continuous on their feasible connecting segment, which
attains every intermediate value. Both increment identities and the lower
separator and termwise residual certificate hold, including original-scale
weights, tied outcomes, singleton samples, and equal bounds. -/
theorem SAP.P025a.T3 : SAP.P025a.T3WholeStatement := by sorry

/-- P025-T4; pp. 237-238 (PDF pp. 3-4); proof in the Supplement, pp. 1-2.
Both corrected first class cuts exist. Their prescribed original-scale threshold vectors are feasible,
have the displayed disjoint prefix/tail values, and attain the global minimum and maximum. Both last-cut
inequalities and both class-weight increment identities hold, including equal probability bounds.
Every displayed denominator is positive; optimality does not assert uniqueness. -/
theorem SAP.P025a.T4 : SAP.P025a.T4WholeStatement := by sorry

/-- P025-T5; pp. 238-239 (PDF pp. 4-5); Table 1 on p. 238 (PDF p. 4).
These two finite population pairs refute the reading of the application sentence that equal gallery
and exchange population prevalences require both actual directional selection ratios to exceed three:
the pairs have equal prevalences and the reported samples, while respectively the exchange and gallery
selection ratio is below three.
Their joint independent uniform fixed-quota sampling designs are normalized, have the stated actual
unit marginals in [1/4,1], and on every draw yield the reported counts and equal Hajek estimates.
The interval memberships, rounding bounds, ratio identities, and both exact rounded-input variants hold. -/
theorem SAP.P025a.T5 : SAP.P025a.T5WholeStatement := by sorry

/-- P025-T6; pp. 238-239 (PDF pp. 4-5).
The binary intervals overlap at the exact odds-ratio threshold, with both numerical thresholds, the
reweighted-odds and ratio-product identities, and the common-cap consequence. -/
theorem SAP.P025a.T6 : SAP.P025a.T6Statement := by sorry

/-- The printed claim is false: P025-T7; p. 236 (PDF p. 2); proof of the upper half in the Appendix, pp.
239-240 (PDF pp. 5-6).
The printed sample lower optimizer and range assertion fail, while the upper first-cut formula remains
valid. -/
theorem SAP.P025a.T7 : SAP.P025a.T7Statement := by sorry

/-- The printed claim is false: P025-T8; pp. 237-238 (PDF pp. 3-4); proof in the Supplement, pp. 1-2.
The printed lower first-cut rule returns zero. At a realizable six-unit,
four-outcome design with γ = 2, the resulting weight vector has value 3/2,
while the attainable minimum is 7/6, so it is not the optimizer of (7).
The separate lower display is undefined at that printed cut; this observation
does not carry the refutation. The upper first-cut rule, optimizer, and endpoint
formula remain valid. -/
theorem SAP.P025a.T8 : SAP.P025a.T8Statement := by sorry

/-- P025-T9; p. 237 (PDF p. 3).
The corrected lower display partitions every threshold vector correctly, equals the minimum at a
corrected first cut, and gives the exact duplicated-class error and undefined-index cases. -/
theorem SAP.P025a.T9 : SAP.P025a.T9Statement := by sorry

/-- P025-T10; p. 237 (PDF p. 3).
The six-unit design realizes the four-class counterexample. Over the whole
real weight box its minimum is 7/6, uniquely at (2,2,1,1), as certified by
the displayed residual equality and its nonnegative slack terms. The
corrected first cut is two, where the printed display gives 1 instead of
7/6; the printed stopping rule gives zero, where that display is undefined. -/
theorem SAP.P025a.T10 : SAP.P025a.T10WholeStatement := by sorry

/-- P025-T11; pp. 239-240 (PDF pp. 5-6); Supplement p. 2.
The repaired proof includes the original-scale threshold formulas and increments.
At equal bounds the sample box is a singleton and both endpoints are the
sample mean; its outcome-test first cut exists, while the first stationary
index is zero. At strict bounds the stationary and outcome-test first cuts
agree and attain the global threshold maximum. The exact two-coordinate
identities give strict improvement only for strict bounds. At equal inclusion
probabilities the actual class totals are probability times class size, and
both class optimization problems attain the finite-population mean. -/
theorem SAP.P025a.T11 : SAP.P025a.T11WholeStatement := by sorry
