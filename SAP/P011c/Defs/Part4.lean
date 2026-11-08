import Mathlib
import SAP.P011c.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- Lemma 2 as cdf convergence at every real threshold; the denominator is eventually positive. -/
def T38Statement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
    (∀ᶠ k in atTop, 0 < var (F.model k) (betaHat (F.model k))) ∧
    ∀ t : ℝ, Tendsto
      (fun k => probability (F.model k) {y | standardized (F.model k) y ≤ t})
      atTop (𝓝 (Phi t))

/-- Both conditional coverage implications, for Borel measurable statistics. -/
def T39Statement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
    ∀ (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ), (∀ k, Measurable (V k)) →
      (InProbability F (fun k y => (F.size k : ℝ)*V k y) (scaledTrue F) →
        ∀ α : ℝ, 0 < α → α < 1 → Tendsto
          (fun k => coverage (F.model k) (V k) α) atTop (𝓝 (1-α))) ∧
      (Conservative F V → ConservativeCoverage F V)

/-- Both printed intervals of Corollary 4, without clipping. -/
def T40Statement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
    (∀ k, Homoskedastic (F.model k)) → Valid F →
    ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V2 B (weighted (F.model k) y)) (A k y)) →
      PrintedConservativeCoverage F
        (fun k y => V2 (A k y) (weighted (F.model k) y)) ∧
      PrintedConservativeCoverage F
        (fun k y => V2prime (F.model k).d (weighted (F.model k) y))

/-- Finite positivity and exact invariance of maximizers under a fixed correction. -/
def T41Statement : Prop :=
  (∀ (n : ℕ) (R : Graph n) (h : Fin n → ℕ),
    (∀ i, 2 * (degree R i : ℝ) - 1 ≤ (h i : ℝ)) →
      PSD (recruitmentCapacityMatrix R h) ∧
      (0 < n → ∀ δ : Fin n → ℝ,
        0 ≤ quadratic (recruitmentCapacityMatrix R h) δ / (n : ℝ))) ∧
  (∀ (n : ℕ) (R : Graph n) (d : Fin n → ℕ) (f : Graph n → ℝ)
      (c : ℝ) (A : Graph n),
    Maximizes R d (fun B => f B + c) A ↔ Maximizes R d f A)

end
end SAP.P011c
