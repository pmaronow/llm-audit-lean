import SAP.P006a.Defs.WholeW2
import SAP.P006a.Defs.WholeW1
import SAP.P006a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P006-T1; PDF p. 15 (Proposition 6 and proof, Appendix B.3); PDF p. 16 (Proposition 7 and proof); PDF pp. 4-5 (Section 3, after Reward Functions 1 and 2). The pages are unnumbered.
The specified two-unit experiment establishes the canonical counterexample to the paper's printed Propositions 6 and 7 and their first proof displays, including the unique finite-sample optimum, reward polynomial, and welfare gaps.
-/
theorem SAP.P006a.T1 : SAP.P006a.T1Statement := by sorry

/-- P006-T2; PDF pp. 15-16 (Propositions 6 and 7); PDF pp. 4-5 (Section 3).
The zero-on-empty ATO and conditionally unbiased ATT rewards have exact expectation
h_n(q) A, empty probability (1-q)^n, and conditional means A/q when q>0.
Their best responses maximize this finite-sample objective. On finite support the
fixed-mass frontier is attained by a fractional threshold, and maximizing it over
q gives an attained threshold optimum. Such an optimum can treat a nonmaximal
score. The printed positive-maximizer rule optimizes the population conditional
average; for one unit the corrected objective is A. Oracle and independent
pointwise-unbiased estimators supply the vector condition on its ordinary L1 domain.
-/
theorem SAP.P006a.T2 : SAP.P006a.T2WholeStatement := by sorry

/-- P006-T3; PDF p. 5 (Proposition 2); PDF pp. 17-18 (Appendix B.4).
For every feasible class containing zero, vector-conditionally unbiased ATT has
expected reward h_n(q)V and h_n(q)>=1. Zero has reward and welfare zero.
Every reward best response has nonnegative reward and welfare, hence regret at
most the finite supremum of feasible welfare. An attained welfare maximum gives
the stated maximum formula. Per-policy identities require no maximizers and no
estimator moments outside the feasible class. In the two-type example the actual
regret is 1/40, whereas the printed closed form is 9/20.
-/
theorem SAP.P006a.T3 : SAP.P006a.T3WholeStatement := by sorry

/-- P006-T4; PDF p. 4 (Assumption 1); PDF p. 16 (proof of Proposition 7); PDF p. 17 (proof of Proposition 9); PDF p. 18 (Proposition 3); PDF p. 19 (Theorem 1); PDF p. 22 (Theorem 3 and proof); PDF pp. 5 and 17 (Proposition 2)
Both canonical pointwise-unbiased estimator witnesses under Assumption 1 alone have the stated evaluation biases, actual ATT/TT reward maxima, and positive welfare regrets, including zero private heterogeneity.
-/
theorem SAP.P006a.T4 : SAP.P006a.T4Statement := by sorry

/-- P006-T5; PDF p. 6 (Theorem 2); PDF p. 20 (restatement, equation (2), proof: 'As shown in the proof of Theorem 1')
The canonical shared-estimator witness C reverses both ranking orders claimed for the two specified agents under pointwise Assumption 1 alone.
-/
theorem SAP.P006a.T5 : SAP.P006a.T5Statement := by sorry

/-- P006-T6; PDF p. 4 (Assumption 1); PDF p. 5 (Reward Function 3, Proposition 3); PDF p. 17 (Proposition 9 and proof); PDF p. 18 (Proposition 3 and proof)
Corrected treated-evaluation unbiasedness aligns TT with welfare on every feasible class, with the positive-effect rule in the unconstrained class and the stated independent-estimation implementation.
-/
theorem SAP.P006a.T6 : SAP.P006a.T6Statement := by sorry

/-- P006-T7; PDF p. 6 (Section 4); PDF p. 19 (Appendix C.2, restatement and proof)
Strictly positive weighted TT aligns every maximizing policy with the welfare optimum under the corrected moment and integrability conditions.
-/
theorem SAP.P006a.T7 : SAP.P006a.T7Statement := by sorry

/-- P006-T8; PDF p. 7 (Section 5); PDF pp. 21-22 (Appendix D.2:
Lemma 2, Proposition 10, Theorem 3 and proof).
Under the usual measure-theoretic conditions, treated conditional unbiasedness
at the marginal untreated baseline gives the normalized TT identity, the exact
marginal-heterogeneity bias identity and bound, and regret at most twice the
marginal heterogeneity for every reward and welfare maximizing pair in any
feasible class. The selected conditional-mean formulation is equivalent, and
independent pointwise-unbiased auxiliary data suffice on the treated-residual
integrability domain. Qualified Lemma 2 is a sum over units; its n-times form
for every fixed unit is equivalent to equality of weighted evaluation means,
which a common joint evaluation law supplies. Conditional independence implies
the required weighted moment, equivalent to factorization when the full
evaluation is integrable. Qualified Proposition 10 gives the uniform absolute
error and regret/triangle bounds for a common evaluation law, including the
derived independent auxiliary-data case, without unbiasedness. All estimator
moments are confined to feasible policies; the main clauses require no
integrability on untreated observations. Maximizers are needed only for regret.
-/
theorem SAP.P006a.T8 : SAP.P006a.T8WholeStatement_W2 := by sorry

/-- P006-T9; PDF p. 7 (Section 6, 'Horse Colic dataset'); PDF pp. 7-8 (Section 6, 'International Stroke Trial dataset'); Table 1, PDF p. 9, row $w_{\mathrm{TT}}$
The fitted whole-sample and beneficiary means obey the exact denominator identity, numerical intervals, printed-table bounds, and three-decimal rounding intervals.
-/
theorem SAP.P006a.T9 : SAP.P006a.T9Statement := by sorry

/-- P006-T10; PDF p. 14 (Appendix A.2: Assumption 3, Theorem 4 and proof)
The canonical singleton always-treated counterexample has identically zero regret despite nondegeneracy and treated-data invariance, contradicting the paper's printed impossibility statement and its withholding step.
The general one-unit expectation identities assume finite-moment probability laws and admissible policies.
-/
theorem SAP.P006a.T10 : SAP.P006a.T10Statement := by sorry

/-- P006-T11; PDF p. 14 (Appendix A.2)
Feasible zero treatment and treated-data invariance permit unbounded regret for some best response through the explicit shifted-law construction, while the zero-reward tie example rules out a conclusion for every best response.
-/
theorem SAP.P006a.T11 : SAP.P006a.T11Statement := by sorry

/-- P006-T12; PDF p. 6 (Theorem 2); PDF p. 20 (Appendix C.2).
Counterexample to the sufficiency reading of the printed absolute-continuity
direction: P_agent << P_reference alone need not supply the named
reference-to-agent density. Lebesgue probability on [0,1] and its
half-Lebesgue, half-atom reference have the same support and satisfy the printed
direction, but the reference has mass 1/2 at the Lebesgue-null singleton {1/2}
and has no representing density. Complete both agents with one unit, independent
uniform treatment seeds, unconstrained policies, potential outcomes 0 and 1,
common zero baseline and oracle estimator. Every other stochastic-model condition
holds and both treatment effects are identically one.
This does not refute the ranking conclusion under a separate assumption that
the named representing density exists.
-/
theorem SAP.P006a.T12 : SAP.P006a.T12WholeStatement := by sorry

/-- P006-T13; PDF p. 6 (Theorem 2); PDF p. 20 (restatement, equation (2), proof)
The corrected normalized reference density gives the score identity, change of measure, attained optimal scores, integrated positive-part comparison, and both specified ranking properties.
-/
theorem SAP.P006a.T13 : SAP.P006a.T13Statement := by sorry

/-- P006-T14; PDF p. 5 (Definitions 1 and 2); PDF pp. 19-20 (score corrections).
Pointwise treatment-effect dominance orders reference positive-part expectations
in [0,infinity], without a finiteness assumption. When both positive parts are
integrable, the same comparison holds for real expectations. Each corrected
ranking compares its own agent's score, and the weighted reward evaluates the
unit's own weight inside the sum; the separate score identities belong to T30,
T7 and T13 as specified by the canonical claim.
-/
theorem SAP.P006a.T14 : SAP.P006a.T14WholeStatement := by sorry

/-- P006-T15; PDF p. 23 (Appendix D.3, first paragraph; definition of $\hat\mu_0^\pi$; Theorem 5); PDF p. 24 (proof of Theorem 5; Lemma 3)
Both canonical positive-treatment counterexamples establish failure of untreated identification and of positive treatment alone to supply the untreated mass needed for the conditional-mean construction and Lemma 3; their singleton-private-covariate maximum heterogeneity is zero.
-/
theorem SAP.P006a.T15 : SAP.P006a.T15Statement := by sorry

