import Mathlib
import SAP.P011c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- Assumption 2's rowwise conditions. Positive sample sizes and growth are fields of
`Family`. No relation between two observed graphs is imposed. This is stronger in
scope than the printed setting of nested full graphs, with arbitrary observed subsets.
The a.e. bound on the measurable weighted coordinates implies finite second moments. -/
def WholeScaling (F : Family) (c1 c2 c3 c4 : ℝ) : Prop :=
  0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < c4 ∧
  (∀ k, Dependency (F.model k)) ∧
  (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
    |weighted (F.model k) y i - beta (F.model k)| ≤ c1) ∧
  (∀ k i, (degree (F.model k).G i : ℝ) ≤ c2) ∧
  Tendsto (scaledTrue F) atTop (𝓝 c3) ∧
  (∀ k i, |(F.model k).theta i| < c4)

/-- The printed one-index auxiliary expression, with its otherwise unspecified
coefficients supplied explicitly. On an edgeless graph it is independent of them. -/
def printedAuxiliary {n : ℕ} (A : Graph n) (r : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, ∑ j, adjacency A i j * r i) / n)

/-- The exact joint law of n independent fair signs, obtained from uniform Boolean
vectors. This is a probability law, including at n = 0. -/
def wholeFairSignLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  ((PMF.uniformOfFintype (Fin n → Bool)).map
    (fun u => fun i => if u i then (1 : ℝ) else -1)).toMeasure

/-- P011-T38; Lemma 2, p. 2247.
Under Assumption 2 the estimator has eventually positive variance and its standardized
cdf converges at every real threshold to the standard normal cdf. The conclusion holds
for arbitrary positive sample sizes tending to infinity and rowwise dependency graphs,
and hence in the printed setting of nested full graphs and arbitrary observed subsets.
No equality of the individual means is assumed. -/
def T38WholeStatement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    (∀ᶠ k in atTop, 0 < var (F.model k) (betaHat (F.model k))) ∧
    ∀ t : ℝ, Tendsto
      (fun k => probability (F.model k) {y | standardized (F.model k) y ≤ t})
      atTop (𝓝 (Phi t))

/-- P011-T39; Lemma 3 and Proposition 3, pp. 2247–2248.
Under Assumption 2, scaled consistency gives exact limiting coverage and scaled
one-sided conservativeness gives at least nominal limiting inferior coverage, for every
level strictly between zero and one. Intervals use nonnegative clipping. Statistics may
be measurable for the completed joint law, represented by a.e. measurable real functions
on the raw outcome space. This includes all a.e. versions. No relation between successive
observed graphs or monotonicity of sample sizes is required. -/
def T39WholeStatement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    ∀ (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ),
      (∀ k, AEMeasurable (V k) (F.model k).law) →
      (InProbability F (fun k y => (F.size k : ℝ) * V k y) (scaledTrue F) →
        ∀ α : ℝ, 0 < α → α < 1 → Tendsto
          (fun k => coverage (F.model k) (V k) α) atTop (𝓝 (1 - α))) ∧
      (Conservative F V → ConservativeCoverage F V)

/-- P011-T40; Corollary 4, p. 2248.
Under Assumptions 2 and 3 and valid constraints, both the maximizing homoskedastic
estimator and the degree-only estimator are everywhere nonnegative, and their printed
intervals have at least nominal asymptotic coverage at every level strictly between
zero and one. Their values are measurable even for an arbitrary maximizing selector.
Supplied degree caps need not be uniformly bounded; weighted means may differ. No
relation between successive observed graphs or monotonicity of sample sizes is required. -/
def T40WholeStatement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    (∀ k, Homoskedastic (F.model k)) → Valid F →
    ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V2 B (weighted (F.model k) y)) (A k y)) →
      (∀ k, Measurable (fun y => V2 (A k y) (weighted (F.model k) y)) ∧
        Measurable (fun y => V2prime (F.model k).d (weighted (F.model k) y))) ∧
      (∀ k y, 0 ≤ V2 (A k y) (weighted (F.model k) y) ∧
        0 ≤ V2prime (F.model k).d (weighted (F.model k) y)) ∧
      PrintedConservativeCoverage F
        (fun k y => V2 (A k y) (weighted (F.model k) y)) ∧
      PrintedConservativeCoverage F
        (fun k y => V2prime (F.model k).d (weighted (F.model k) y))

/-- P011-T41; accepted repair of P011-E001, broader sufficient condition and fixed
corrections after maximization in the 19 October review draft.
The capacity matrix always equals the signless Laplacian plus the displayed real
diagonal correction. The capacity condition makes it positive semidefinite and, for
positive sample size, makes every normalized quadratic form nonnegative. Adding a
graph-independent constant preserves all maximizers over the same compatible graphs,
including ties. The decomposition, positivity, and maximizer equivalence include size
zero; only division by sample size requires positivity. -/
def T41WholeStatement : Prop :=
  (∀ (n : ℕ) (R : Graph n) (h : Fin n → ℕ),
    recruitmentCapacityMatrix R h =
      (adjacency R + Matrix.diagonal (fun i => (degree R i : ℝ))) +
        Matrix.diagonal (fun i => 1 + (h i : ℝ) - 2 * (degree R i : ℝ))) ∧
  (∀ (n : ℕ) (R : Graph n) (h : Fin n → ℕ),
    (∀ i, 2 * (degree R i : ℝ) - 1 ≤ (h i : ℝ)) →
      PSD (recruitmentCapacityMatrix R h) ∧
      (0 < n → ∀ δ : Fin n → ℝ,
        0 ≤ quadratic (recruitmentCapacityMatrix R h) δ / (n : ℝ))) ∧
  (∀ (n : ℕ) (R : Graph n) (d : Fin n → ℕ) (f : Graph n → ℝ)
      (c : ℝ) (A : Graph n),
    Maximizes R d (fun B => f B + c) A ↔ Maximizes R d f A)

/-- The printed claim is false: P011-T34; proof of Proposition 2, p. 2246.
Independent fair signs with unit weights and empty dependency graphs satisfy
Assumptions 2 and 3, valid constraints, and even the stronger observed-graph nesting.
Their sample sizes are k+1, their target means are zero, and their scaled estimator
variances are one. For every choice of the undefined one-index coefficients and every
positive epsilon, the printed auxiliary estimator's less-than-epsilon probability tends
to one and does not tend to zero. This refutes the printed argument through its P4
assertion without assigning a meaning to the undefined correlations or repairing P2. -/
def T34WholeStatement : Prop :=
  ∃ F : Family,
    (∀ k, F.size k = k + 1) ∧ Nested F ∧ WholeScaling F 1 1 1 2 ∧ Valid F ∧
    (∀ k, (F.model k).law = wholeFairSignLaw (F.size k) ∧
      (∀ i, (F.model k).theta i = 1) ∧
      (∀ i j, (F.model k).G.val i j = false) ∧
      Homoskedastic (F.model k) ∧ beta (F.model k) = 0 ∧ scaledTrue F k = 1) ∧
    ∀ (r : ∀ k, Fin (F.size k) → ℝ) (ε : ℝ), 0 < ε →
      Tendsto (fun k => probability (F.model k) {y |
        |(F.size k : ℝ) * printedAuxiliary (F.model k).G (r k)
          (weighted (F.model k) y) - scaledTrue F k| < ε}) atTop (𝓝 1) ∧
      ¬ Tendsto (fun k => probability (F.model k) {y |
        |(F.size k : ℝ) * printedAuxiliary (F.model k).G (r k)
          (weighted (F.model k) y) - scaledTrue F k| < ε}) atTop (𝓝 0)

end
end SAP.P011c
