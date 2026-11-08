import SAP.P011c.Defs
import SAP.P011c.Defs.WholeW1
import SAP.P011c.Defs.WholeW2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P011-T29; Definition 3 and Section 2, pp. 2240–2241.
OLS coefficients have the stated linear representation and are unbiased under an integrable
linear mean model with invertible Gram matrix, and any linear estimator has the stated
covariance-sum variance under finite second moments and positive sample size. -/
theorem SAP.P011c.T29 : SAP.P011c.T29Statement := by sorry

/-- P011-T30; program (3.6) and its computational classification, p. 2245.
For positive sample size, the degree-constrained unordered-edge program has exactly the
same maximizers as the two-endpoint incidence 0/1 knapsack with the same mandatory edges
and empirical edge profits; the variance objective is their positive affine normalization.
Restricted to C1's optimization encoding: omit C2's NP-hardness assertion or its correction,
C3's PTAS assertion, and running-time and decision-variable-count assertions.
No algorithm or hardness transfer from general knapsack is asserted. -/
theorem SAP.P011c.T30 : SAP.P011c.T30Statement := by sorry

/-- The printed claim is false: P011-T31; Proposition 1, p. 2242.
The universal n-scaled consistency guarantee for the general oracle estimator fails under
the printed assumptions. -/
theorem SAP.P011c.T31 : SAP.P011c.T31Statement := by sorry

/-- The printed claim is false: P011-T32; Corollary 1, p. 2245, and its homoskedastic
specialization on p. 2246; proof (A.1), p. 2249.
The combined universal conservativeness contract fails; this negation does not separately
assert that its homoskedastic specialization fails. -/
theorem SAP.P011c.T32 : SAP.P011c.T32Statement := by sorry

/-- P011-T33; Corollary 3, p. 2248.
The universal nominal asymptotic coverage guarantee fails under the explicit convention
that negative-estimate realizations, whose printed intervals are undefined, count as misses.
Restricted to this extension of the partial printed interval: the proof does not refute
the guarantee on its real-square-root domain or establish undercoverage for estimates
that are nonnegative almost surely. No assertion about such defined intervals is added. -/
theorem SAP.P011c.T33 : SAP.P011c.T33Statement := by sorry

/-- The printed claim is false: P011-T34; proof of Proposition 2, p. 2246.
Independent fair signs with unit weights and empty dependency graphs satisfy
Assumptions 2 and 3, valid constraints, and even the stronger observed-graph nesting.
Their sample sizes are k+1, their target means are zero, and their scaled estimator
variances are one. For every choice of the undefined one-index coefficients and every
positive epsilon, the printed auxiliary estimator's less-than-epsilon probability tends
to one and does not tend to zero. This refutes the printed argument through its P4
assertion without assigning a meaning to the undefined correlations or repairing P2. -/
theorem SAP.P011c.T34 : SAP.P011c.T34WholeStatement := by sorry

/-- The printed claim is false: P011-T35; package README line 3 and vignette
lines 15, 100–105; Appendix B, p. 2250.
There is a correctly specified two-column OLS coefficient problem with coefficient
vector (0,1), invertible designs, valid known-edge and degree constraints, and
Assumption 2 constants (6,2,29/15,2), whose maximizing divisor-n general estimator
fails n-scaled variance conservativeness. The witness even has nested observed
graphs, which can serve as the full graphs. Thus the combined formal variance and
printed Wald-coverage guarantee is false. These are mathematical counterexample
facts; they make no assertion about the vignette's realized standard errors. -/
theorem SAP.P011c.T35 : SAP.P011c.T35WholeStatement := by sorry

/-- P011-T36; Proposition 2 and its introductory sentence, p. 2246.
Under Assumptions 2 and 3 the homoskedastic oracle estimator is asymptotically
conservative, with arbitrary individual weighted means. No relation between the
observed graphs is required. It need not be consistent in the surrounding
n-scaled sense: there is a family with constants (2,1,1,2), even with nested
observed graphs, for which n times the oracle estimate does not converge in
probability to n times the true variance. This states the relative/scaled meaning
of consistency used for variance inference here. -/
theorem SAP.P011c.T36 : SAP.P011c.T36WholeStatement := by sorry

/-- P011-T37; Corollary 2, p. 2247.
Under Assumptions 2 and 3 and valid graph constraints, both the maximizing
homoskedastic estimator and the degree-only estimator are asymptotically
conservative. The supplied degree caps are unrestricted, individual weighted
means can differ, and no relation between observed graphs or measurable choice
of maximizing graphs is required. -/
theorem SAP.P011c.T37 : SAP.P011c.T37WholeStatement := by sorry

/-- P011-T38; Lemma 2, p. 2247.
Under Assumption 2 the estimator has eventually positive variance and its standardized
cdf converges at every real threshold to the standard normal cdf. The conclusion holds
for arbitrary positive sample sizes tending to infinity and rowwise dependency graphs,
and hence in the printed setting of nested full graphs and arbitrary observed subsets.
No equality of the individual means is assumed. -/
theorem SAP.P011c.T38 : SAP.P011c.T38WholeStatement := by sorry

/-- P011-T39; Lemma 3 and Proposition 3, pp. 2247–2248.
Under Assumption 2, scaled consistency gives exact limiting coverage and scaled
one-sided conservativeness gives at least nominal limiting inferior coverage, for every
level strictly between zero and one. Intervals use nonnegative clipping. Statistics may
be measurable for the completed joint law, represented by a.e. measurable real functions
on the raw outcome space. This includes all a.e. versions. No relation between successive
observed graphs or monotonicity of sample sizes is required. -/
theorem SAP.P011c.T39 : SAP.P011c.T39WholeStatement := by sorry

/-- P011-T40; Corollary 4, p. 2248.
Under Assumptions 2 and 3 and valid constraints, both the maximizing homoskedastic
estimator and the degree-only estimator are everywhere nonnegative, and their printed
intervals have at least nominal asymptotic coverage at every level strictly between
zero and one. Their values are measurable even for an arbitrary maximizing selector.
Supplied degree caps need not be uniformly bounded; weighted means may differ. No
relation between successive observed graphs or monotonicity of sample sizes is required. -/
theorem SAP.P011c.T40 : SAP.P011c.T40WholeStatement := by sorry

/-- P011-T41; accepted repair of P011-E001, broader sufficient condition and fixed
corrections after maximization in the 19 October review draft.
The capacity matrix always equals the signless Laplacian plus the displayed real
diagonal correction. The capacity condition makes it positive semidefinite and, for
positive sample size, makes every normalized quadratic form nonnegative. Adding a
graph-independent constant preserves all maximizers over the same compatible graphs,
including ties. The decomposition, positivity, and maximizer equivalence include size
zero; only division by sample size requires positivity. -/
theorem SAP.P011c.T41 : SAP.P011c.T41WholeStatement := by sorry
