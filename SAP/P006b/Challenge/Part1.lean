import SAP.P006b.Defs.WholeW1
import SAP.P006b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P006-T16; PDF p. 23 (Appendix D.3, first paragraph; Assumption 4; Theorem 5); PDF p. 24 (proof; Lemma 3).
Corrected untreated-arm positivity gives the conditional-law, selected-mean, bias and regret bounds, with the sufficient pointwise condition and full-information identity. -/
theorem SAP.P006b.T16 : SAP.P006b.T16Statement := by sorry

/-- P006-T17; PDF p. 23 (Appendix D.3, paragraph after Assumption 4).
For finite positive-mass conditional types, the actual untreated outcome mean
is the probability-weighted selection ratio. Leaving only one type untreated
selects its mean; treating only it selects the complementary mean (the three-type
values are 0 and 2). Under the usual measure-theoretic conditions, for every
conditional probability kernel, including infinite and nonatomic private spaces,
the marginal deviation is integrable and bounded almost surely and in expectation
by the maximum deviation. Thus Assumption 4 implies Assumption 2 with the same
constant. Marginal heterogeneity alone cannot bound endogenous-baseline regret:
it can equal 1 while regret exceeds every prescribed positive threshold. -/
theorem SAP.P006b.T17 : SAP.P006b.T17WholeStatement := by sorry

/-- The printed claim is false: P006-T18; PDF p. 17 (Appendix B.4, proof of
Proposition 1). The fair two-unit deterministic example has samplewise ATO
bounded by the event that some type is 1, with equality under (0,1). Its exact
reward is b(4-a-b)/4, uniquely maximized at (0,1), with value 3/4. Welfare is
a/2-3b/2, with maximum 1/2 and selected value -3/2. Regret is 2; the printed
expression is -1. Every feasible policy's regret from an attained maximum is
nonnegative. -/
theorem SAP.P006b.T18 : SAP.P006b.T18WholeStatement := by sorry

/-- P006-T19; PDF p. 17 (Appendix B.4, proof of Proposition 1).
The corrected second-mode welfare and regret formulas have a positive discrepancy from the printed formula and diverge as beta increases; the half-probability example is stated in its beta-greater-than-one range. -/
theorem SAP.P006b.T19 : SAP.P006b.T19Statement := by sorry

/-- P006-T20; PDF p. 25 (Appendix E.2.1).
The normalized four-state logistic witness has signed means zero and minus one half, contradicting the printed probability-as-mean formula and changing the TO decision. -/
theorem SAP.P006b.T20 : SAP.P006b.T20Statement := by sorry

/-- P006-T21; PDF p. 25 (Appendix E.2.1).
For outcomes coded as one and minus one, logistic probabilities give means 2 sigma minus 1, twice the probability difference as the effect, and never the printed mean. -/
theorem SAP.P006b.T21 : SAP.P006b.T21Statement := by sorry

/-- P006-T22; PDF p. 26 (Appendix E.4).
Nonempty empirical groups use the corrected count denominator, obey the bounds and zero-deviation identity, preserve the overall mean, and give 2 in the two-row example rather than 4. -/
theorem SAP.P006b.T22 : SAP.P006b.T22Statement := by sorry

/-- P006-T23; PDF p. 13 (Appendix A.1, item 2).
Two complete missing-outcome laws satisfy treatment independence and observation positivity and share every observed record, but have different untreated means. -/
theorem SAP.P006b.T23 : SAP.P006b.T23Statement := by sorry

/-- P006-T24; PDF p. 13 (Appendix A.1, item 2).
Within any supplied covariate-stratum law, mean representativeness identifies the untreated mean, the mixture gives the equality criterion, and observation independence implies representativeness. -/
theorem SAP.P006b.T24 : SAP.P006b.T24Statement := by sorry

/-- P006-T25; PDF p. 7 (Section 5); PDF pp. 22-23 (Appendix D.2).
For arbitrary public covariates independent of a fair binary private type,
integrable noisy outcomes and every estimator satisfying corrected T8, the TT
reward, full response set, welfare, regret and minimal marginal heterogeneity
are the stated two-coordinate formulas. The displayed bad response attains
regret alpha-beta/2. Taking beta=min(epsilon,alpha/2) gives the lower bound.
For 0<beta,eta<alpha the perturbed family has a unique response up to null sets
and regret alpha-(beta+eta)/2; taking both parameters to be that minimum gives
the same lower bound. The deterministic zero-estimator family supplies actual
finite-sample existential witnesses. -/
theorem SAP.P006b.T25 : SAP.P006b.T25WholeStatement := by sorry

/-- The printed claim is false: with a discrete covariate law having positive
mass at every point of its stated space, the joint universal ATO/ATT
best-response assertion fails under the standing assumptions and fixed-query
unbiasedness. The statement negates the conjunction without claiming separate
failures of both rules; the shared unbiasedness premise also applies to ATO,
although Proposition 6 does not require it.
P006-T26; PDF p. 15 (Proposition 6 and proof); PDF p. 16 (Proposition 7 and proof); PDF pp. 4-5 (Section 3). -/
theorem SAP.P006b.T26 : SAP.P006b.T26Statement := by sorry

/-- The printed claim is false: fixed-query unbiasedness does not imply the joint universal TT alignment, maximizer, zero-regret and positive-rule assertions; this negates the conjunction without claiming separate failure of every clause.
P006-T27; PDF p. 4 (Assumption 1); PDF p. 5 (Reward Function 3, Proposition 3); PDF p. 17 (Proposition 9 and proof); PDF p. 18 (Proposition 3 and proof). -/
theorem SAP.P006b.T27 : SAP.P006b.T27Statement := by sorry

/-- P006-T29; PDF p. 4 (Section 3); PDF p. 17 (Appendix B.4).
ATO regret exceeds every positive threshold. For every iid integrable
conditional-outcome law in the binary family, its exact expected reward is
h_n(q)pb. For n>=2 the unique response is (0,1); for n=1 exactly b=1 is
required. In the first failure mode welfare has maximum -alpha(1-p)+p,
selected value p and regret -alpha(1-p), which diverges as alpha tends to
minus infinity at fixed 0<p<1. The claim allows arbitrary outcome noise. -/
theorem SAP.P006b.T29 : SAP.P006b.T29WholeStatement := by sorry

/-- P006-T30; PDF p. 6 (Section 4); PDF pp. 18-19 (Appendix C.2).
Under the usual measure-theoretic conditions (policies are measurable maps into
[0,1]; outcomes, conditional means and the treated estimator residual are
integrable), with corrected T6 and otherwise unconstrained policies, each agent's
attained maximum TT score is its sample size times its mean positive effect.
For two agents with the common untreated mean of the multi-agent setting,
identical covariate laws, pointwise effect dominance and a positive mean positive
effect for the dominated agent, these positive-effect means are ordered; a
reversed sample-size-weighted inequality violates both ranking properties, for
every reference law with finite effect means. The ratio condition is equivalent
because its denominator is positive. Identical unit effects with sample sizes
1 and 2 give actual best scores 1 and 2 and witness the existential failure of
both properties. -/
theorem SAP.P006b.T30 : SAP.P006b.T30WholeStatement := by sorry

