import SAP.P011a.Defs
import SAP.P011a.Defs.WholeW1
import SAP.P011a.Defs.WholeW2
import SAP.P011a.Defs.WholeW3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P011-T1; Proposition 1, p. 2242 (PDF p. 5); Corollary 1, p. 2245 (PDF p. 8);
sentence after Assumption 3, p. 2246 (PDF p. 9); Corollary 3, p. 2248 (PDF p. 11).
The stated independent-sign four-cycle constructions satisfy Assumptions 1–3 and have a
singleton compatible set, exact scaled variance 4 and mean bias -9/4, all stated finite
moments, estimator limit 7/4, failure probabilities tending to one, and the exact all-alpha
undercoverage formula. At alpha=0.05 its coverage limit is between 0.8045 and 0.8055.
The a=3 construction has limit -5 and the stated positive-probability negative estimate.
These counterexample facts refute the quoted printed assertions. -/
theorem SAP.P011a.T1 : SAP.P011a.T1WholeStatement := by sorry

/-- P011-T2; Proposition 1, p. 2242 (PDF p. 5); Corollary 1, p. 2245 (PDF p. 8);
sentence after Assumption 3, p. 2246 (PDF p. 9); Corollary 3, p. 2248 (PDF p. 11).
Both independent-sign path-block laws satisfy Assumptions 1–3, the bound 27/5, the displayed
mean/covariance matrices, singleton compatibility, all S/L/Q polynomials and block moments,
the samplewise centering formula and the exact finite oracle expectation. For t=1 the
estimator tends to 19/15 instead of 29/15 and its all-alpha coverage is strictly deficient;
at alpha=0.05 its coverage limit is between 0.8873623230 and 0.8873623231. For t=2 it
tends to -11/15, is negative with probability tending to one and has zero clipped coverage.
Both are correctly specified OLS intercept examples. These facts refute the printed assertions. -/
theorem SAP.P011a.T2 : SAP.P011a.T2WholeStatement := by sorry

/-- P011-T3; p. 2242 (PDF p. 5), replacing the proof step on p. 2243 (PDF p. 6).
Under Assumption 2, without induced nesting of observed graphs, the scaled oracle converges
to the scaled true variance plus the mean quadratic b_n. Its expectation remainder is bounded
by 3(1+c2)²c1²/n and the sample variance converges to average marginal variance plus mean
spread. Consistency is equivalent to b_n tending to zero; common means suffice.
Conservativeness is equivalent to liminf b_n≥0; positive semidefiniteness suffices.
The mean deviations sum to zero and |b_n|≤(1+c2)c1². The matrix I+A is positive semidefinite
exactly for disjoint unions of cliques, with the stated clique-square variance formula. -/
theorem SAP.P011a.T3 : SAP.P011a.T3WholeStatement := by sorry

/-- P011-T4; Replaces the argument of the proof of Proposition 1,
pp. 2242–2244 (PDF pp. 5–7); not printed in the paper.
For deterministic symmetric matrices with uniformly bounded spectral norm,
Assumption 2 gives both exact expectations, linear variance growth, and F1.
PSD majorants give conservativeness for arbitrary unit means; nonnegative traces
against admissible covariances suffice in place of the PSD difference condition,
and only diagonal and true-edge entries enter those traces. The oracle matrix
is PSD exactly for unions of cliques. Independent fair signs give the stated
bounded-norm data-dependent counterexample. No nesting of observed graphs or
monotonicity of observed sizes is required. -/
theorem SAP.P011a.T4 : SAP.P011a.T4WholeStatement := by sorry

/-- P011-T5; Replaces Corollary 1, p. 2245 (PDF p. 8), and the use of (3.1)
in programs (3.5)–(3.6), pp. 2244–2245 (PDF pp. 7–8); not printed in the paper.
The degree-corrected estimator and Young bound satisfy all finite decompositions,
PSD and nonnegativity conclusions, norm and oracle bounds, affine edge-objective
and attained-optimum identities, and the constant-cap and regular-graph formulas,
including zero degree. Under Assumption 2 and valid constraints the corrected
oracle, sample maximizer, Young bound, and their stated minimum are conservative
for arbitrary unit means, with no uniform bound on supplied degree caps. Common
caps give the same conclusion for (3.9), without homoskedasticity. No nesting of
observed graphs or monotonicity of observed sizes is required. -/
theorem SAP.P011a.T5 : SAP.P011a.T5WholeStatement := by sorry

/-- P011-T6; replaces the known-graph use of (3.1), p. 2242 (PDF p. 5).
Spectral clipping is a PSD majorant with the degree norm bound, dominates both the
oracle estimate and zero, and is asymptotically conservative under Assumption 2.
It is the unique nearest PSD matrix in Frobenius norm, but is neither a least
Loewner majorant nor affine in the adjacency entries. The four-cycle spectrum,
quadratic identities, alternative majorant, exact expectation 4-12/n and limit 4
are included. -/
theorem SAP.P011a.T6 : SAP.P011a.T6WholeStatement := by sorry

/-- P011-T7; Corollary 1, p. 2245 (PDF p. 8), and the degree-only case on p. 2248
(PDF p. 11).
The degree identity and both fixed-cap finite comparisons hold. Under Assumption 2,
the degree-only maximum is conservative and has conservative clipped Wald coverage,
even for unbounded supplied caps; residuals are bounded by 2c1 almost surely.
For independent fair signs with caps n-1, every nonconstant sample has exactly the
two residual-sign cliques as optimizer, while the exact estimates converge unscaled
to 1/2 and 1, respectively. -/
theorem SAP.P011a.T7 : SAP.P011a.T7WholeStatement := by sorry

/-- P011-T8; Corollary 1, p. 2245 (PDF p. 8), and Corollary 3, p. 2248 (PDF p. 11);
the homoskedasticity sentence on p. 2246 (PDF p. 9) is deleted.
Under Assumption 2, every estimator in the corrected list has one-sided asymptotic
variance control and conservative clipped Wald coverage: the four corrected/Young
estimators under valid constraints, spectral clipping, the degree-only original
maximum, and the oracle or original maximum when the mean-bias limit inferior is
nonnegative. Equal unit means and disjoint clique graphs imply that condition.
The first two branches are nonnegative in every sample. The homoskedastic cycle
and path counterexamples show why no such conclusion holds for the unrestricted
original estimator with known edges. -/
theorem SAP.P011a.T8 : SAP.P011a.T8WholeStatement := by sorry

/-- P011-T9; replaces centring in (3.1) and (3.5), pp. 2242 and 2244 (PDF pp. 5 and 7),
for the regression example, pp. 2240–2241 (PDF pp. 3–4); corrected statement, not printed.
Under Assumption 2 and the correct bounded finite-dimensional mean model, root-n coefficient
estimation gives zero-mean residuals with covariance C, the three stated stochastic norm rates,
oracle consistency and maximal-estimator conservativeness. The finite symmetric quadratic
perturbation bound holds. Bounded residuals and prediction error o_p(sqrt(n)) also suffice;
a misspecified model adds the quadratic mean term. The independent-sign OLS example satisfies
Assumption 2 with exact scaled variance 2, but has intercept variance n/2+1/(2n), residual
expectation n+2-7/n (17/4 and 73/8 at n=4 and 8) and fails consistency, with the explicit
slope weights and samplewise residual sum. No observed-graph nesting is required. -/
theorem SAP.P011a.T9 : SAP.P011a.T9WholeStatement := by sorry

/-- P011-T10; bears on the abstract, p. 2238 (PDF p. 1), and Proposition 1, p. 2242
(PDF p. 5); corrected statement, not printed.
For every a,b>0 the independent fixed-sign-mean and random-sign-mixture models satisfy all
scaling assumptions, have the stated finite means and scaled variances b² and a²+b², and
obey the exact finite mixture identity. No statistic is scaled consistent in all these
models, and mixture conservativeness prevents consistency in every fixed mean pattern.
Consequently no law-independent observed-data variance rule is universally scaled consistent.
The zero statistic is unscaled consistent under Assumption 2. Extra sampling-design information
can permit unbiased variance estimation: independent half-probability inclusion of population
values 1 gives betaHat=average(2I) and the unbiased estimator average(2I)/n. -/
theorem SAP.P011a.T10 : SAP.P011a.T10WholeStatement := by sorry

/-- P011-T11; p. 2246 (PDF p. 9), proof of Proposition 2.
The alternating-means counterexample refutes the quoted auxiliary proof step both as printed with
< epsilon and under the intended > epsilon consistency reading. It establishes the exact finite
moments and both failure limits, while preserving Proposition 2's one-sided conservativeness
conclusion. -/
theorem SAP.P011a.T11 : SAP.P011a.T11Statement := by sorry

/-- P011-T12; p. 2246 (PDF p. 9).
Under Assumptions 2 and 3, the homoskedastic oracle estimator satisfies the entire
finite moment, covariance and scalar gap chain, the explicit tail bound
4(1+c2)^3 c1^4/(n epsilon^2), and one-sided asymptotic conservativeness.
Unit means may differ, early common variances may vanish, and neither the mean
spread nor the common variance needs a limit. -/
theorem SAP.P011a.T12 : SAP.P011a.T12WholeStatement := by sorry

/-- P011-T13; p. 2245 (PDF p. 8), the two paragraphs after program (3.6); programs (3.5) p. 2244 (PDF p.
7), (3.6) p. 2245 (PDF p. 8), (3.8) p. 2246 (PDF p. 9).
The finite degree-constrained optimization problem reduces to a matching gadget with exact decoding,
counts, and two attained numerical instances.
Restriction: Retains the finite feasibility test, existential mandatory/optional decomposition,
optimal decoding and objective recovery for every supplied maximum matching, exact gadget counts and
combinatorial size bounds, and both exact attained instances. Drops (a)'s equivalence with the
paper's programs, (b)'s explicit uniqueness and separate optional-optimum identity, a general
existence assertion for maximum matchings and an independently defined optimum-value identity in
(c), and all runtime and complexity-class conclusions of (e). No encoded-bit-length conclusion is
stated. -/
theorem SAP.P011a.T13 : SAP.P011a.T13Statement := by sorry

/-- P011-T14; p. 2245 (PDF p. 8), after program (3.6); p. 2248 (PDF p. 11), "Upper bounds for the
variance estimates can be obtained by solving a relaxed form of the programs (3.5) and (3.8)";
Appendix B, p. 2250 (PDF p. 13).
Certified relaxed bounds control integer objectives and both variance estimators, and the six-unit
and triangle examples have strictly fractional optima. -/
theorem SAP.P011a.T14 : SAP.P011a.T14Statement := by sorry
