import AronowAudit.P001.Wave1.MarBalanceBlueprint

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1.MarBalance

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n1_proof : N1.{u, v} := by
  classical
  intro Ω E _ _ μ _ X R p hX hR hbin hp A _hA
  let I : Ω → ℝ := fun ω => if R ω ∈ A then 1 else 0
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hpCE : μ[R | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] p ∘ X := (isCEF_condExp μ X hX R p hp).symm
  have hcomp : μ[(fun ω => 1 - R ω) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] (fun ω => 1 - p (X ω)) := by
    have hs := condExp_sub (integrable_const (1 : ℝ)) hp.2.1 (MeasurableSpace.comap X inferInstance)
    rw [condExp_const hG (1 : ℝ)] at hs
    filter_upwards [hs, hpCE] with ω hωsub hωp
    change (μ[(fun ω => 1 - R ω) | (MeasurableSpace.comap X inferInstance)]) ω = 1 - (μ[R | (MeasurableSpace.comap X inferInstance)]) ω at hωsub
    change (μ[R | (MeasurableSpace.comap X inferInstance)]) ω = p (X ω) at hωp
    rw [hωsub, hωp]
  by_cases h0 : (0 : ℝ) ∈ A <;> by_cases h1 : (1 : ℝ) ∈ A
  · have hI : I =ᵐ[μ] (fun _ => (1 : ℝ)) := by
      filter_upwards [hbin] with ω hω
      rcases hω with hω | hω <;> simp [I, hω, h0, h1]
    have he := condExp_congr_ae (m := (MeasurableSpace.comap X inferInstance)) hI
    rw [condExp_const hG (1 : ℝ)] at he
    filter_upwards [he] with ω hω
    simp only [if_pos h0, if_pos h1]
    rw [hω]
    ring
  · have hI : I =ᵐ[μ] (fun ω => 1 - R ω) := by
      filter_upwards [hbin] with ω hω
      rcases hω with hω | hω <;> simp [I, hω, h0, h1]
    simpa only [if_pos h0, if_neg h1, add_zero] using
      (condExp_congr_ae (m := (MeasurableSpace.comap X inferInstance)) hI).trans hcomp
  · have hI : I =ᵐ[μ] R := by
      filter_upwards [hbin] with ω hω
      rcases hω with hω | hω <;> simp [I, hω, h0, h1]
    refine ((condExp_congr_ae (m := (MeasurableSpace.comap X inferInstance)) hI).trans
      hpCE).trans (Filter.Eventually.of_forall fun ω => ?_)
    simp [h0, h1]
  · have hI : I =ᵐ[μ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hbin] with ω hω
      rcases hω with hω | hω <;> simp [I, hω, h0, h1]
    have he := condExp_congr_ae (m := (MeasurableSpace.comap X inferInstance)) hI
    rw [condExp_const hG (0 : ℝ)] at he
    simpa only [if_neg h0, if_neg h1, zero_add] using he

end

end AronowAudit.P001.Wave1.MarBalance
