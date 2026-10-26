import AronowAudit.P001.P001_Foundations

/-!
# Sample-mean moments and tail bound (P001-T108)

Theorems 3.2.3–3.2.5 (pp. 97–99), for every `n ≥ 1`:
unbiasedness under L¹ (finite expectation, footnote 2, p. 45),
`V[X̄] = V[X]/n` under L², and the Chebyshev bound under L² and `V[X] > 0`.
Each conclusion has its own moment hypothesis.
`Target` is universe polymorphic in `Ω`, and `N1 = Target`.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.SampleMean

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section


def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → Integrable (X 0) μ → ∀ (n : ℕ), 0 < n →
    mean μ (sampleMean X n) = mean μ (X 0) ∧
    (MemLp (X 0) 2 μ →
      var μ (sampleMean X n) = var μ (X 0) / (n : ℝ) ∧
      (0 < var μ (X 0) → ∀ ε : ℝ, 0 < ε →
        prob μ {ω | ε ≤ |sampleMean X n ω - mean μ (X 0)|} ≤
          var μ (X 0) / (ε ^ 2 * (n : ℝ))))

/-- The three sample-mean conclusions, equal to `Target`. -/
def N1 : Prop := Target.{u}

/-- The single intermediate statement is the target. -/
theorem assemble (h1 : N1.{u}) : Target.{u} := h1

end

end AronowAudit.P001.Wave1.SampleMean
