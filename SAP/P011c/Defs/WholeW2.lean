import Mathlib
import SAP.P011c.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- Assumption 2's numerical and dependency conditions, without imposing embeddings
between the observed graphs. `Family` supplies positive sample sizes tending to infinity.
The conclusions below hold without any relation between rows, so in particular apply
when the full graphs are nested as in the paper. The almost-everywhere bound supplies
all moments of the weighted outcomes needed by the variance estimators. -/
def WholeW2Scaling (F : Family) (c1 c2 c3 c4 : ℝ) : Prop :=
  0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < c4 ∧
  (∀ k, Dependency (F.model k)) ∧
  (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
    |weighted (F.model k) y i - beta (F.model k)| ≤ c1) ∧
  (∀ k i, (degree (F.model k).G i : ℝ) ≤ c2) ∧
  Tendsto (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)))
    atTop (𝓝 c3) ∧ (∀ k i, |(F.model k).theta i| < c4)

/-- The printed claim is false: P011-T35; package README line 3 and vignette
lines 15, 100–105; Appendix B, p. 2250.
There is a correctly specified two-column OLS coefficient problem with coefficient
vector (0,1), invertible designs, valid known-edge and degree constraints, and
Assumption 2 constants (6,2,29/15,2), whose maximizing divisor-n general estimator
fails n-scaled variance conservativeness. The witness even has nested observed
graphs, which can serve as the full graphs. Thus the combined formal variance and
printed Wald-coverage guarantee is false. These are mathematical counterexample
facts; they make no assertion about the vignette's realized standard errors. -/
def T35WholeStatement : Prop :=
  ∃ (F : Family)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin 2) ℝ)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
    WholeW2Scaling F 6 2 (29 / 15) 2 ∧ Nested F ∧ Valid F ∧
    (∀ k, ((D k)ᵀ * D k).det ≠ 0) ∧
    (∀ k, MeanModel (F.model k) (D k) (![0, 1] : Fin 2 → ℝ)) ∧
    (∀ k i, (F.model k).theta i = olsTheta (D k) (0 : Fin 2) i) ∧
    (∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) ∧
    ¬ Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y))

/-- P011-T36; Proposition 2 and its introductory sentence, p. 2246.
Under Assumptions 2 and 3 the homoskedastic oracle estimator is asymptotically
conservative, with arbitrary individual weighted means. No relation between the
observed graphs is required. It need not be consistent in the surrounding
n-scaled sense: there is a family with constants (2,1,1,2), even with nested
observed graphs, for which n times the oracle estimate does not converge in
probability to n times the true variance. This states the relative/scaled meaning
of consistency used for variance inference here. -/
def T36WholeStatement : Prop :=
  (∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeW2Scaling F c1 c2 c3 c4 →
    (∀ k, Homoskedastic (F.model k)) →
    Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y))) ∧
  (∃ F : Family, WholeW2Scaling F 2 1 1 2 ∧ Nested F ∧
    (∀ k, Homoskedastic (F.model k)) ∧
    ¬ InProbability F
      (fun k y => (F.size k : ℝ) * V2 (F.model k).G (weighted (F.model k) y))
      (scaledTrue F))

/-- P011-T37; Corollary 2, p. 2247.
Under Assumptions 2 and 3 and valid graph constraints, both the maximizing
homoskedastic estimator and the degree-only estimator are asymptotically
conservative. The supplied degree caps are unrestricted, individual weighted
means can differ, and no relation between observed graphs or measurable choice
of maximizing graphs is required. -/
def T37WholeStatement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeW2Scaling F c1 c2 c3 c4 →
    (∀ k, Homoskedastic (F.model k)) → Valid F →
    ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V2 B (weighted (F.model k) y)) (A k y)) →
      Conservative F (fun k y => V2 (A k y) (weighted (F.model k) y)) ∧
      Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y))

end
end SAP.P011c
