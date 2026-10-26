import AronowAudit.P001.Wave1.CompleteDescriptionBlueprint

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.CompleteDescription

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1 := by
  classical
  intro Ω E F G _ _ _ _ μ _ e Y Z hY hZ hCI A B hA hB
  have hYA : MeasurableSet (Y ⁻¹' A) := hY hA
  have hZB : MeasurableSet (Z ⁻¹' B) := hZ hB
  have hAB : MeasurableSet (Y ⁻¹' A ∩ Z ⁻¹' B) := hYA.inter hZB
  have hfactor := hCI A B hA hB
  simp only [MeasurableSpace.comap_const, condExp_bot] at hfactor
  -- Conditional expectations on the trivial sigma-field are constant functions.
  obtain ⟨ω, hω⟩ := hfactor.exists
  have indicator_integral (S : Set Ω) (hS : MeasurableSet S) :
      (∫ ω, (if ω ∈ S then (1 : ℝ) else 0) ∂μ) = (μ S).toReal := by
    change (∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
    rw [integral_indicator hS]
    simp [integral_const, measureReal_def]
  have eAB : (∫ ω, (if Y ω ∈ A ∧ Z ω ∈ B then (1 : ℝ) else 0) ∂μ) =
      (μ (Y ⁻¹' A ∩ Z ⁻¹' B)).toReal := by
    rw [← indicator_integral _ hAB]
    congr 1
    funext ω
    by_cases h : Y ω ∈ A ∧ Z ω ∈ B
    · rw [if_pos h, if_pos (show ω ∈ Y ⁻¹' A ∩ Z ⁻¹' B from h)]
    · rw [if_neg h, if_neg (show ω ∉ Y ⁻¹' A ∩ Z ⁻¹' B from h)]
  have eA : (∫ ω, (if Y ω ∈ A then (1 : ℝ) else 0) ∂μ) =
      (μ (Y ⁻¹' A)).toReal := indicator_integral _ hYA
  have eB : (∫ ω, (if Z ω ∈ B then (1 : ℝ) else 0) ∂μ) =
      (μ (Z ⁻¹' B)).toReal := indicator_integral _ hZB
  change (∫ ω, (if Y ω ∈ A ∧ Z ω ∈ B then (1 : ℝ) else 0) ∂μ) =
    (∫ ω, (if Y ω ∈ A then (1 : ℝ) else 0) ∂μ) *
      (∫ ω, (if Z ω ∈ B then (1 : ℝ) else 0) ∂μ) at hω
  rwa [eAB, eA, eB] at hω

end

end AronowAudit.P001.Wave1.CompleteDescription
