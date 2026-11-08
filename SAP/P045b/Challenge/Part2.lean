import SAP.P045b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The printed claim is false: within a group under Bernoulli assignment, the arm mean conditional on a nonempty arm need not be unbiased for the group average of marginal potential outcomes.
P045-T25; p. 310 (PDF p. 22).
The theorem negates the printed within-group assertion itself, and hence refutes the printed conjunction without quantifying over first-stage designs. -/
theorem SAP.P045b.T25 : SAP.P045b.T25Statement := by sorry

/-- P045-T26; pp. 310–311 (PDF pp. 22–23).
The universal conjunction of additive-effect unbiasedness and conservativeness fails for the package statistic with singleton-arm variance contributions dropped.
Restriction: This refutes only the extension of the guarantee to that software statistic when singleton arms are allowed. It does not refute the Hudgens–Halloran estimator on its defined domain, where each required arm has at least two units, or establish the printed direct-effect variance values as values of that estimator. -/
theorem SAP.P045b.T26 : SAP.P045b.T26Statement := by sorry

/-- The printed claim is false: the documented full-neighborhood control indicator differs from the indicator returned by the package.
P045-T27; pp. 304–305 (PDF pp. 16–17), staged full-neighborhood mapping.
The theorem negates their asserted equivalence on every simple undirected network and assignment. -/
theorem SAP.P045b.T27 : SAP.P045b.T27Statement := by sorry

/-- The printed claim is false: the package's cluster sampler as coded does not always return a three-net.
P045-T29; p. 305 (PDF p. 17), staged cluster sampler.
The theorem negates the documentation's universal contract for that implementation, with the actual singleton-number draw and retry traces included. The intended sampler that draws uniformly among unmarked vertices is outside this refutation. -/
theorem SAP.P045b.T29 : SAP.P045b.T29Statement := by sorry

/-- P045-T30; pp. 297–298 (PDF pp. 9–10).
Positive exact marginal exposure probabilities make the HT total and the exposure contrast unbiased under a correctly specified mapping. -/
theorem SAP.P045b.T30 : SAP.P045b.T30Statement := by sorry

/-- P045-T31; p. 315 (PDF p. 27).
The indirect household effect has both contagion decompositions, and an unchanged mediator gives zero household contagion contribution. -/
theorem SAP.P045b.T31 : SAP.P045b.T31Statement := by sorry

/-- P045-T32; pp. 298–299 (PDF pp. 10–11), audit counterexample to a stronger finite-simulation extension.
The specified twelve-unit, three-clique witness has all the stated exposure counts, exact and simulated moments, strict shortfalls, and fixed-table and relabeling facts.
Exact rational certificates use canonical real embedding; the final clause states the shortfall for the real-valued estimator under both sampling regimes.
This refutes the stronger exact finite-simulation reading, without refuting the contextual exact-probability assertion. -/
theorem SAP.P045b.T32 : SAP.P045b.T32Statement := by sorry

/-- P045-T33; pp. 298–299 (PDF pp. 10–11), Section 16.4.2.
With positive exact marginal probabilities, the adjusted HT contrast variance estimate has precisely the structural-zero squared-outcome surplus, is conservative in expectation, and the point estimator is unbiased. -/
theorem SAP.P045b.T33 : SAP.P045b.T33Statement := by sorry

