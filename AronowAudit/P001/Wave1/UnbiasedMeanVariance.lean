import AronowAudit.P001.Wave1.UnbiasedMeanVarianceBlueprint
import AronowAudit.P001.Wave1.UnbiasedMeanVariance.N1
import AronowAudit.P001.Wave1.UnbiasedMeanVariance.N2

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableP001cFinalUnbiasedMeanVariance (p : Prop) : Decidable p := Classical.propDecidable p

theorem sample_mean_unbiased_variance_contract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
    (hv : 0 < var μ (X 0)) :
    let vhat : ℕ → Ω → ℝ := fun n ω => sampleVariance X n ω / ((n : ℝ) - 1)
    (∀ n, Measurable (vhat n)) ∧
    (∀ n ω, 0 ≤ vhat n ω) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ ω,
      vhat n ω = (∑ i ∈ Finset.range n, (X i ω - sampleMean X n ω)^2) /
        ((n : ℝ) * ((n : ℝ) - 1)) ∧
      (n : ℝ) * vhat n ω = ((n : ℝ) / ((n : ℝ) - 1)) * sampleVariance X n ω) ∧
    (∀ n : ℕ, 2 ≤ n → mean μ (vhat n) = var μ (X 0) / (n : ℝ)) ∧
    CD μ (fun n ω => Real.sqrt n * (sampleMean X n ω - mean μ (X 0)))
      (gaussianReal 0 ⟨var μ (X 0), le_of_lt hv⟩) ∧
    VarianceConsistent μ vhat (var μ (X 0)) ∧
    SEConsistent μ vhat (var μ (X 0)) ∧
    CP μ (fun n ω => (n : ℝ) * vhat n ω - var μ (X 0)) 0 ∧
    CP μ (fun n ω => Real.sqrt n * Real.sqrt (vhat n ω) -
      Real.sqrt (var μ (X 0))) 0 :=
  UnbiasedMeanVariance.assemble UnbiasedMeanVariance.n1_proof UnbiasedMeanVariance.n2_proof
    μ X hiid h2 hv

example : UnbiasedMeanVariance.Target := sample_mean_unbiased_variance_contract

end
end AronowAudit.P001.Wave1
