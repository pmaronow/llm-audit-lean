import SAP.P030.Defs.WholeW1
import SAP.P030.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P030-T1, p. 7 (PDF p. 5): the five-unit experiment has no effects, defined
Spearman statistics equal to one, printed rejection probability one, and corrected
rejection probability zero, with the stated distances and rank computations. -/
theorem SAP.P030.T1 : SAP.P030.T1Statement := by sorry

/-- P030-T2, p. 7 and Table 1, p. 9 (PDF pp. 5, 7): a genuine no-effects ten-unit population realizes the table's six-assignment conditional law. All midranks, centered ranks, products, square sums, squared correlations, strict orders, roundings, and inclusive tails have their stated values. For 0 < alpha <= 2/3 the printed rule rejects exactly the three assignments with p = 1 and has conditional size 1/2; the corrected rule rejects none. The printed size exceeds every positive alpha < 1/2, including alpha = 1/20. -/
theorem SAP.P030.T2 : SAP.P030.T2WholeStatement := by sorry

/-- P030-T3, p. 7 (PDF p. 5), corrected: the two-inclusive-tail rule controls size
for every finite probability law, with the tail identity, super-uniformity, union
bound, printed-rule inclusion, genuine strictness example, and conventional alternative. -/
theorem SAP.P030.T3 : SAP.P030.T3Statement := by sorry

/-- The printed claim is false: P030-T4, p. 7 (PDF p. 5), the printed two-tailed
rule does not universally control conditional Type I error under no interference. -/
theorem SAP.P030.T4 : SAP.P030.T4Statement := by sorry

/-- P030-T5, p. 7 (PDF p. 5), Equation (1): no interference, even no effects of any kind, does not force statistic constancy. The genuine ten-unit experiment has all the stated midranks, centered ranks, products, square sums, rational squared correlations, exact correlations, strict orders, and roundings, and exactly three distinct actual conditional statistics. Its observed-data p-value at unit 7 is 1/3, rounding to 0.333. On any nonempty finite reference support, a constant statistic instead gives a point mass at its observed value and p = 1. -/
theorem SAP.P030.T5 : SAP.P030.T5WholeStatement := by sorry

/-- P030-T6, p. 7 (PDF p. 5), corrected: no interference fixes the fixed units'
outcomes and validates observed-data imputation of the conditional reference law;
the genuine ten-unit counterexample shows that the statistic can still vary. -/
theorem SAP.P030.T6 : SAP.P030.T6Statement := by sorry

/-- P030-T7, pp. 5-6 (PDF pp. 3-4), corrected: conditional assignments preserve
fixed treatments, no interference fixes their outcomes, fixed-outcome variation
refutes no interference, direct effects are allowed, and no effects implies no interference. -/
theorem SAP.P030.T7 : SAP.P030.T7Statement := by sorry

/-- P030-T8, p. 8 (PDF p. 6): the printed covariance-over-product-of-variances formula is false as a formula for rank correlation. The observed midranks, centered ranks, products, square sums, and population and sample moments give the two wrong values -4/5 and -3/5, with the stated rational square comparisons. All six printed-formula values, correct correlations, and roundings are as stated; the corrected expression is invariant under positive moment divisors. The two explicit tied vectors reverse the printed formula's ordering, and the nonconstant weakly monotone example has the stated ranks, products, variances, and correlation sqrt(3)/2, rounding to 0.866 and unequal to either 1 or -1. -/
theorem SAP.P030.T8 : SAP.P030.T8WholeStatement := by sorry

/-- P030-T9, p. 8 (PDF p. 6), corrected: Spearman correlation has divisor
invariance, bounds, the exact proportionality characterization and its signs,
the tie-preserving monotone cases, the weak-monotonicity counterexample, and all six table values. -/
theorem SAP.P030.T9 : SAP.P030.T9Statement := by sorry

/-- P030-T10, p. 10 (PDF p. 8), corrected: excluding self yields defined inverse-square
sums at positive off-diagonal distances, with the stated decay, values, non-exponential
character, explicit divergence bound, and contrasting finite exponential limit. -/
theorem SAP.P030.T10 : SAP.P030.T10Statement := by sorry

/-- P030-T11, p. 13 (PDF p. 11), corrected: disjoint sample counts must add,
the printed counts do not, and exactly the four stated single-entry repairs reconcile them. -/
theorem SAP.P030.T11 : SAP.P030.T11Statement := by sorry

/-- P030-T12, abstract p. 3 and Equation (2), p. 7 (PDF pp. 1, 5): the uniform
conditional one-tailed p-value permits observed-data imputation, equals its
assignment-count formula, is super-uniform, and is exact at attainable levels
with the stated greatest-attainable-level formula at every threshold. -/
theorem SAP.P030.T12 : SAP.P030.T12Statement := by sorry

/-- P030-T13, p. 5 (PDF p. 3): complete randomization gives all three proximal
exposure expectations, strict comparisons with neighborhood size and own treatment,
and total expectation, with conditional means used only on nonempty supports. -/
theorem SAP.P030.T13 : SAP.P030.T13Statement := by sorry

/-- P030-T14, pp. 9-10 (PDF pp. 7-8): the actual adjacency outcome model gives all the printed spatial, indirect, total, and fixed observations, including fixed-outcome midranks (3/2, 4, 3, 3/2). The six conditional assignments have the stated masses, distances, defined and unique reference correlations, exact values, and roundings. Exactly the assignments treating units 6 and 7 lie in the observed lower tail, giving the actual observed-data p = 2/6 = 1/3, rounding to 0.333; every reference value is negative. -/
theorem SAP.P030.T14 : SAP.P030.T14WholeStatement := by sorry

/-- P030-T15, Equation (3), pp. 8-9 (PDF pp. 6-7): completion of the square
gives exactly half the controls as the unique even-count maximizer and the two
nearest halves as exactly the odd-count maximizers, for positive treatment and control counts. -/
theorem SAP.P030.T15 : SAP.P030.T15Statement := by sorry
