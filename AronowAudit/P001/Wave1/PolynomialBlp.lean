import AronowAudit.P001.Wave1.PolynomialBlpBlueprint
import AronowAudit.P001.Wave1.PolynomialBlp.N1
import AronowAudit.P001.Wave1.PolynomialBlp.N2
import AronowAudit.P001.Wave1.PolynomialBlp.N3
import AronowAudit.P001.Wave1.PolynomialBlp.N4
import AronowAudit.P001.Wave1.PolynomialBlp.N5

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Population polynomial least squares exists and approximates a continuous CEF on
the paper's full interval support, for every minimizing family. -/
theorem polynomial_blp_paper_support_approximation
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : MemLp Y 2 μ)
    (a b : ℝ) (hsupp : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hfull : (∃ f : ℝ → ℝ, HasPDF (μ.map X) f ∧ paperSupport f = Set.Icc a b) ∨
      (Set.Countable (Set.range X) ∧
        ∀ x : ℝ, 0 < prob μ {ω | X ω = x} ↔ x ∈ Set.Icc a b))
    (m : ℝ → ℝ) (hm : IsCEF μ X Y m) (hc : ContinuousOn m (Set.Icc a b)) :
    (∃ p : ℕ → Polynomial ℝ, (∀ J, (p J).natDegree ≤ J) ∧
      (∀ (J : ℕ) (q : Polynomial ℝ), q.natDegree ≤ J →
        mean μ (fun ω => (Y ω - (p J).eval (X ω)) ^ 2) ≤
          mean μ (fun ω => (Y ω - q.eval (X ω)) ^ 2))) ∧
    (∀ p : ℕ → Polynomial ℝ, (∀ J, (p J).natDegree ≤ J) →
      (∀ (J : ℕ) (q : Polynomial ℝ), q.natDegree ≤ J →
        mean μ (fun ω => (Y ω - (p J).eval (X ω)) ^ 2) ≤
          mean μ (fun ω => (Y ω - q.eval (X ω)) ^ 2)) →
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ J', J ≤ J' →
        mean μ (fun ω => (m (X ω) - (p J').eval (X ω)) ^ 2) < ε) := by
  exact PolynomialBlp.assemble PolynomialBlp.n1_proof PolynomialBlp.n2_proof
    PolynomialBlp.n3_proof PolynomialBlp.n4_proof PolynomialBlp.n5_proof
    μ X Y hX hY a b hsupp hfull m hm hc

end

end AronowAudit.P001.Wave1
