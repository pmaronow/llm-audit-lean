import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Moments.SubGaussian

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- Hoeffding's bounded-variable lemma, specialized to the centred two-point law. -/
theorem n2_proof : N2 := by
  intro p c hp hp1
  let q : unitInterval := ⟨p, hp, hp1⟩
  let μ : Measure Bool := ProbabilityTheory.bernoulliMeasure true false q
  let X : Bool → ℝ := fun b => if b then 1 - p else -p
  have hm : AEMeasurable X μ := .of_discrete
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc (-p) (1 - p) := by
    apply ae_of_all
    intro b
    cases b
    · change -p ≤ -p ∧ -p ≤ 1 - p
      exact ⟨le_rfl, by linarith⟩
    · change -p ≤ 1 - p ∧ 1 - p ≤ 1 - p
      exact ⟨by linarith, le_rfl⟩
  have hc : (∫ b, X b ∂μ) = 0 := by
    change (∫ b, X b ∂ProbabilityTheory.bernoulliMeasure true false q) = 0
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    change p * (1 - p) + (1 - p) * (-p) = 0
    ring
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc
  have h := hsub.mgf_le c
  have hmgf : ProbabilityTheory.mgf X μ c =
      p * Real.exp (c * (1 - p)) + (1 - p) * Real.exp (-(c * p)) := by
    unfold ProbabilityTheory.mgf
    change (∫ b, Real.exp (c * X b)
      ∂ProbabilityTheory.bernoulliMeasure true false q) = _
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    change p * Real.exp (c * (1 - p)) + (1 - p) * Real.exp (c * (-p)) = _
    rw [mul_neg]
  rw [hmgf] at h
  have hlen : (1 - p) - (-p) = (1 : ℝ) := by ring
  have hparam : (((‖(1 - p) - (-p)‖₊ / 2) ^ 2 : NNReal) : ℝ) = 1 / 4 := by
    rw [hlen]
    norm_num
  calc
    _ ≤ Real.exp ((1 / 4 : ℝ) * c ^ 2 / 2) := by simpa only [hparam] using h
    _ = _ := by congr 1; ring

end
end AronowAudit.P002.Wave1.E61Eigenvalue
