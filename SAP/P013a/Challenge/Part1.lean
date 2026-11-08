import SAP.P013a.Defs.WholeW1
import SAP.P013a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P013-T1; Proposition 6.2, as printed, p. 1926 (PDF p. 15), and Appendix A.7,
p. 1943 (PDF p. 32). The paired family satisfies the standing conditions and genuine
degree-two dependence, but its positive unbiased variance estimate has scaled probability
limit six instead of eight and its Wald intervals strictly undercover. All finite identities,
asymptotic limits and the decimal coverage at level 95 percent are included. -/
theorem SAP.P013a.T1 : SAP.P013a.T1WholeStatement := by sorry

/-- P013-T2; corrected Proposition 6.2, p. 1926 (PDF p. 15), and Appendix A.7,
p. 1943 (PDF p. 32). Comparison boundedness, genuine bounded-degree dependence, positive
limiting scaled variance and the added lower-tail condition ensure nominal lower-limit
coverage of the population contrast. Centered concentration suffices; both joint-probability
rates and their concentration consequences hold without outcome stability across sizes.
The three original conditions alone permit strict undercoverage. -/
theorem SAP.P013a.T2 : SAP.P013a.T2WholeStatement := by sorry

/-- P013-T3; Proposition 4.1 and the replicate rule, as printed; p. 1920 (PDF p. 9); proof in Appendix A.3, p. 1938 (PDF p. 27).
The two-unit signed-outcome experiment refutes the printed relative-bias bound and replicate rule, and its zero-total variant refutes the absolute-bias inequality. -/
theorem SAP.P013a.T3 : SAP.P013a.T3Statement := by sorry

/-- P013-T4; Proposition 4.1 and the replicate rule, corrected; p. 1920 (PDF p. 9); proof in Appendix A.3, p. 1938 (PDF p. 27).
Independent simulated assignments yield the corrected exact expectation, absolute and relative bias bounds, sign-qualified replicate rule and numerical threshold. -/
theorem SAP.P013a.T4 : SAP.P013a.T4Statement := by sorry

/-- P013-T5; Definition of the dependency indicator $h_{ij}$ and Condition 5, as printed, with the claim that Condition 5 subsumes Condition 4; p. 1925 (PDF p. 14); p. 1926 (PDF p. 15).
The printed dependency condition is vacuous for identity and triangle indicators with row sums exactly one and two, respectively, and permits the fully shared Bernoulli counterexample to Condition 4. -/
theorem SAP.P013a.T5 : SAP.P013a.T5Statement := by sorry

/-- P013-T6; Definition of the dependency indicator $h_{ij}$, corrected, with Condition 5 and the claim that Condition 5 subsumes Condition 4; p. 1925 (PDF p. 14); p. 1926 (PDF p. 15).
The corrected edge condition supplies pairwise independence, the directed and symmetric pair-count bounds, and Condition 5 implies Condition 4. -/
theorem SAP.P013a.T6 : SAP.P013a.T6Statement := by sorry

/-- P013-T7; Appendix A.7 (proof of Proposition 6.2), convergence claims of the first and last paragraphs, as printed; p. 1943 (PDF p. 32).
The fixed block family has a concentrating scaled variance estimate with two subsequential limits and no limiting variance ratio or studentized law. -/
theorem SAP.P013a.T7 : SAP.P013a.T7Statement := by sorry

