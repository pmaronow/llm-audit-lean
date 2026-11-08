import SAP.P001b.Defs.WholeW1
import SAP.P001b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

/-- P001-T20. Location: pp. 271–272 (PDF pp. 289–290), Definition 7.3.1,
Theorem 7.3.2 and the surrounding corrected discussion.
The usual measure-theoretic conditions are assumed. Uniform propensity positivity
implies complete overlap of the conditional covariate laws; positive-probability
zero/one propensity regions prevent overlap. For discrete covariates the two arm
PMF supports have the stated propensity descriptions, overlap is equivalent to
pointwise positivity, and finite support yields a uniform bound. The specified
infinite geometric joint law has complete overlap without a uniform bound.
Density supports are version-invariant modulo null sets; coherently normalized
joint-density versions also satisfy the exact pointwise support identity.
-/
theorem T20 : SAP.P001b.T20WholeStatement := by sorry

/-- P001-T21. Location: p. 278 (PDF p. 296), paragraph beginning 'The fact that random assignment is unlikely to hold'; the application's setting: pp. 276–278 (PDF pp. 294–296).
Counterexample to the reading that complete coding of the applicant information available to voters in (X_i, D_i), with no personal acquaintance, forces conditional independence of (Y_i(0), Y_i(1)) and D_i given X_i.
The four-atom 100-voter model has fully coded leaflets and positivity, violates conditional independence, and gives contrast 25 rather than average effect 5.
-/
theorem T21 : T21Statement := by sorry

/-- P001-T22. Location: p. 278 (PDF p. 296), corrected ignorability discussion;
Theorem 7.1.13, p. 248 (PDF p. 266).
The usual measure-theoretic conditions are assumed, including measurable response
sections on the covariate space and integrability where expectations are used.
(i) Complete coding can coexist with failure of ignorability in the stated four-atom
electorate model, with constant covariates and positivity.
(ii) A fixed measurable response to description and treatment alone implies
conditional independence of the potential-outcome pair and treatment given X.
(iii) Under explicit conditional independence and uniform positivity, discrete
covariates give the ATE as the difference of the two absolutely convergent
population-weighted observed-arm conditional-mean sums. The arm means are actual
positive-cell ratios, not extra model assumptions.
All three canonical clauses are stated in full under these conditions.
-/
theorem T22 : SAP.P001b.T22WholeStatement := by sorry

/-- P001-T23. Location: Gloss: p. 9 (PDF p. 27), first paragraph. Theorem 1.1.4: p. 8 (PDF p. 26). Theorem 1.1.7: p. 9 (PDF p. 27), proof on p. 10 (PDF p. 28).
The corrected subset gloss, all basic probability rules, the addition rule, and failure of the reversed gloss for every proper subset hold.
-/
theorem T23 : T23Statement := by sorry

/-- P001-T24. Location: Theorem 1.1.13: p. 12 (PDF p. 30). Proof and the remark after it: p. 13 (PDF p. 31). Definition 1.1.12: p. 12 (PDF p. 30). Definition 1.1.8 and Theorem 1.1.9: p. 10 (PDF p. 28).
Countable total probability holds with conditional ratios on positive cells, and deleting empty members repairs the event/complement partition remark.
-/
theorem T24 : T24Statement := by sorry

/-- The printed claim is false: P001-T25. Location: p. 20 (PDF p. 38), first bulleted list, third bullet.
The constant-zero integer-valued law has lower-tail probability one but printed mass sum zero.
Scope: Retains only counterexample (a), the constant-zero one-atom law. Omits counterexample (b), the Bernoulli law with masses two thirds and one third and its printed-sum value one third.
-/
theorem T25 : T25Statement := by sorry

/-- P001-T26. Location: p. 20 (PDF p. 38), first bulleted list, third bullet.
For every discrete real random variable whose PMF vanishes off the integers, the
probability below four is the sum of all integer masses through three. Its excess
over the masses at one, two and three is exactly the probability of a nonpositive
value, and the printed equality holds exactly when that probability is zero.
For the fair die, the displayed specialization is three sixths, equal to one half.
The usual measure-theoretic conditions are assumed. Null sample points with noninteger values are allowed.
-/
theorem T26 : SAP.P001b.T26WholeStatement := by sorry

/-- P001-T27. Location: p. 23 (PDF p. 41), Example 1.2.13; Definition 1.2.4,
p. 18 (PDF p. 36).
The specified dyadic atom law has level masses 2^(-(m+1)) summing to one, all
subsets measurable, and an injective random variable with exactly the dyadic
rationals in (0,1) as its countable range. Each value has its stated positive mass.
Its CDF is the stated mass sum, strictly increases on (0,1), and is constant on no
nonempty open subinterval there. It gives one third mass zero and is continuous
there, while constant on no neighborhood of one third. This supplies all parts
of the canonical counterexample to local flatness at every non-jump point.
The usual measure-theoretic conditions are assumed.
-/
theorem T27 : SAP.P001b.T27WholeStatement := by sorry

/-- P001-T28. Location: p. 23 (PDF p. 41), Example 1.2.13, first sentence; the analogy on p. 116 (PDF p. 134).
Countable discrete CDFs are point-mass sums, finite ordered CDFs have the stated interval formulas, and the six fair-die evaluations hold.
-/
theorem T28 : T28Statement := by sorry

/-- The printed claim is false: P001-T29. Location: p. 24 (PDF p. 42), sentence after Definition 1.2.14; p. 25 (PDF p. 43), Definition 1.2.15 and the proof of Theorem 1.2.16. Example 1.2.18: p. 28 (PDF p. 46).
Three distinct nonnegative uniform density versions give the same CDF, whose endpoint derivatives fail with the displayed one-sided quotients.
-/
theorem T29 : T29Statement := by sorry

end SAP.P001b
