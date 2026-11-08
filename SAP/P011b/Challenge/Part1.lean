import SAP.P011b.Defs.WholeW2
import SAP.P011b.Defs
import SAP.P011b.Defs.WholeW1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P011b
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

/-- P011-T15; package README line 3 and vignette lines 100–105; Section 2,
pp. 2240–2241; Corollary 1, p. 2245.
The two correctly specified binary star regressions satisfy the standing assumptions,
full-rank design identities, independent Bernoulli leaf and conditional centre laws,
and saturated binary and fractional constraints. Their raw maximal variance estimates
converge below and above the true variance, respectively. The first has ratio 8/9,
underestimation probability tending to one, and the stated strict undercoverage for
both the clipped and printed-domain intervals; negative estimates vanish in probability.
The explicit mean offsets have the stated negative and positive quadratics, while
true-error products converge to the true variance in both models. -/
theorem SAP.P011b.T15 : SAP.P011b.T15WholeStatement := by sorry

/-- P011-T16; regression example, pp. 2240–2241; (3.1), p. 2242; package
vignette lines 100–105. Corrected claim (2026-11-04).
For a full-rank fixed-design OLS coefficient, weighted unit means and their offsets
have the exact stated formulas. Under Assumption 2 the raw oracle has the moving
mean-bias limit, is consistent exactly when that bias tends to zero, and is
conservative exactly when its liminf is nonnegative. With valid constraints this
condition suffices for every compatible maximum, but is not necessary in general,
as the independent binary-star regression with empty recruitment demonstrates.
Equal weighted unit means suffice for consistency and maximal conservativeness.
Every design-space outcome shift leaves fitted residual products and all residual
objectives unchanged and has the stated effect on raw centred products. With an
intercept, constant shifts preserve slopes and residual objectives, but can change
raw slope variance, as an explicit two-point example shows. Under Assumption 2,
fixed dimension, uniformly bounded rows and outcomes, and a uniformly coercive
normalized Gram matrix, OLS has the root-n rate. The displayed normalized residual
perturbation inequality holds and its right side tends to zero in probability;
the residual oracle is consistent and every compatible residual maximum is
conservative. Deterministic coefficients and targets may vary with sample size.
The usual measure-theoretic conditions are assumed. -/
theorem SAP.P011b.T16 : SAP.P011b.T16WholeStatement_W2 := by sorry

/-- P011-T17; (3.3), p. 2243; (3.4), pp. 2243–2244.
The corrected pair and fourth moments and constant-centering covariance expansion hold on their separate integrable moment domains. -/
theorem SAP.P011b.T17
    {n : ℕ} (hn : 0 < n) (m : Model n) (i j k l : Fin n) : SAP.P011b.T17Statement hn m i j k l := by sorry

/-- The printed claim is false: The constant-outcome witness gives true covariance zero, printed values 9/4 and 93009/16, the named bracket-only repair -70, and fully corrected value zero.
P011-T18; (3.3), p. 2243. -/
theorem SAP.P011b.T18 : SAP.P011b.T18Statement := by sorry

/-- P011-T19; proof of Proposition 2, p. 2246.
For positive common variance under Assumptions 2 and 3, the auxiliary error is
k times the sample-variance error, where k is the true scaled variance divided by
the common variance and lies between zero and 1+c2. The sample-variance remainder
after subtracting between-unit mean spread converges to zero in probability.
Vanishing mean spread, in particular equal weighted unit means, suffices for auxiliary
consistency. The explicit alternating-mean independent-sign family satisfies all these
standing assumptions with positive common variance, yet its mean spread tends to one
and its auxiliary error exceeds 1/2 with probability tending to one. -/
theorem SAP.P011b.T19 : SAP.P011b.T19WholeStatement := by sorry

/-- The printed claim is false: Fair signs refute the printed limit-zero display and give its exact inside-event probabilities and limit one.
P011-T20; proof of Proposition 2, p. 2246. -/
theorem SAP.P011b.T20 : SAP.P011b.T20Statement := by sorry

/-- P011-T21; proof of Proposition 2, p. 2246.
Pairwise correlations give the exact variance identity and oracle bound, and the path witness has distinct adjacent correlations.
The usual measure-theoretic conditions, including finite second moments of the weighted outcomes, are assumed. -/
theorem SAP.P011b.T21 {n : ℕ} (hn : 0 < n) (m : SAP.P011b.Model n)
    (hdep : SAP.P011b.Dependency m) (hs : SAP.P011b.Homoskedastic m)
    (hL2 : ∀ i, MemLp (fun y => SAP.P011b.weighted m y i) 2 m.law) :
    SAP.P011b.T21Statement hn m hdep hs hL2 := by sorry

/-- P011-T22; decision-variable sentence, p. 2244; (3.6), p. 2245.
Binary edge decisions and symmetric adjacency matrices describe the same finite programs, objectives and maximizers. -/
theorem SAP.P011b.T22 {n : ℕ} (hn : 0 < n) : SAP.P011b.T22Statement hn := by sorry

/-- P011-T23; decision-variable sentence, p. 2244; (3.6), p. 2245.
Refutes interpreting the nonzero-product instruction as a data-determined feasible or optimal edge assignment:
the specified three-vertex examples violate degree caps or omit a forced edge, and the unit-cap example
has unique optimum edge23 with value 3/4. -/
theorem SAP.P011b.T23 : SAP.P011b.T23Statement := by sorry

/-- P011-T24; Assumption 2, p. 2242; (3.5), p. 2244; Assumption 3, p. 2246; Discussion, p. 2248.
Element-wise graph inequalities describe exactly the compatible graphs and admit the true graph under valid constraints.
Restriction: Only formal content (i), the graph feasible-set equivalence and true-graph feasibility under valid constraints, is stated. The observed-data tuple correction, the Assumption 3 index-set correction and all of formal content (ii), including its covariance bound and scope of the cited statistical results, and the edge-set typography correction are omitted. -/
theorem SAP.P011b.T24 {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) : SAP.P011b.T24Statement R G d hv := by sorry

/-- P011-T25; Appendix B, p. 2250; (3.1), p. 2242; (3.7), p. 2246; (3.9), p. 2247; helper code lines 11, 19, 27.
Changing the helper divisor from n to n minus one has the stated exact discrepancies, order, maximizing graphs and bound. -/
theorem SAP.P011b.T25 {n : ℕ} (hn : 1 < n) (R : SAP.P011b.Graph n) (d : Fin n → ℕ)
    (x : Fin n → ℝ) : SAP.P011b.T25Statement hn R d x := by sorry

/-- The printed claim is false: Three exact data vectors separate the helper formulas from the paper formulas, and one occurs with positive probability in an admissible family.
P011-T26; Appendix B, p. 2250; helper code lines 11, 19, 27. -/
theorem SAP.P011b.T26 : SAP.P011b.T26Statement := by sorry

/-- P011-T27; Definitions 4–6, p. 2241; (3.5), p. 2244; (3.6), p. 2245; (3.8), p. 2246.
Compatible variance maximizers exist, bound the oracle sharply, and are characterized by the stated finite integer programs. -/
theorem SAP.P011b.T27 {n : ℕ} (hn : 0 < n) (R G : SAP.P011b.Graph n) (d : Fin n → ℕ)
    (hv : SAP.P011b.Compatible R d G) (x : Fin n → ℝ) :
    SAP.P011b.T27Statement hn R G d hv x := by sorry

/-- P011-T28; Lemma 1, p. 2247; Appendix A, pp. 2249–2250.
The maximal homoskedastic estimator lies between the oracle and the truncated-degree bound, with equality when every cap is attained. -/
theorem SAP.P011b.T28 {n : ℕ} (hn : 0 < n) (R G A : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (x : Fin n → ℝ)
    (hm : Maximizes R d (fun B => V2 B x) A) : SAP.P011b.T28Statement hn R G A d hv x hm := by sorry

