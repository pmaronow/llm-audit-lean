import AronowAudit.P001.Wave1.MarSelectionBlueprint
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n2_proof : N2.{u, v, w} := by
  classical
  intro Ω E F _ _ _ μ _ X hX U R hU hR hbin hCI C A hC hA
  let ρ : Ω → ℝ := μ[R | (MeasurableSpace.comap X inferInstance)]
  let I : Ω → ℝ := (U ⁻¹' A).indicator (fun _ => 1)
  have hGi : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hCX : MeasurableSet[(MeasurableSpace.comap X inferInstance)] (X ⁻¹' C) := ⟨C, hC, rfl⟩
  have hUA : MeasurableSet (U ⁻¹' A) := hA.preimage hU
  have hIm : Measurable I := measurable_const.indicator hUA
  have hIb : ∀ᵐ ω ∂μ, ‖I ω‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun ω => by
      by_cases h : U ω ∈ A <;> simp [I, Set.indicator, h]
  have hIi : Integrable I μ := Integrable.of_bound hIm.aestronglyMeasurable 1 hIb
  have hRb : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hRi : Integrable R μ := Integrable.of_bound hR.aestronglyMeasurable 1 hRb
  have hRIi : Integrable (R * I) μ := hRi.mul_bdd hIm.aestronglyMeasurable hIb
  have hρi : Integrable ρ μ := integrable_condExp
  have hρm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] ρ := stronglyMeasurable_condExp
  have hρIi : Integrable (ρ * I) μ := hρi.mul_bdd hIm.aestronglyMeasurable hIb
  have hci := hCI A {1} hA (measurableSet_singleton (1 : ℝ))
  have key : ∀ {f g k : Ω → ℝ},
      μ[f | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ]
        (fun ω => (μ[g | (MeasurableSpace.comap X inferInstance)]) ω * (μ[k | (MeasurableSpace.comap X inferInstance)]) ω) →
      f =ᵐ[μ] R * I → g =ᵐ[μ] I → k =ᵐ[μ] R →
      μ[R * I | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] ρ * μ[I | (MeasurableSpace.comap X inferInstance)] := by
    intro f g k hc hf hg hk
    filter_upwards [hc, condExp_congr_ae (m := (MeasurableSpace.comap X inferInstance)) hf,
      condExp_congr_ae (m := (MeasurableSpace.comap X inferInstance)) hg, condExp_congr_ae (m := (MeasurableSpace.comap X inferInstance)) hk] with ω h1 h2 h3 h4
    change (μ[R * I | (MeasurableSpace.comap X inferInstance)]) ω = ρ ω * (μ[I | (MeasurableSpace.comap X inferInstance)]) ω
    rw [← h2, h1, h3, h4]
    exact mul_comm _ _
  have hfactor := key hci
    (by
      filter_upwards [hbin] with ω hω
      rcases hω with hω | hω <;>
        by_cases h : U ω ∈ A <;> simp [I, Set.indicator, hω, h])
    (Filter.Eventually.of_forall fun ω => by
      by_cases h : U ω ∈ A <;> simp [I, Set.indicator, h])
    (by
      filter_upwards [hbin] with ω hω
      rcases hω with hω | hω <;> simp [hω])
  have hpull : μ[ρ * I | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] ρ * μ[I | (MeasurableSpace.comap X inferInstance)] :=
    condExp_mul_of_stronglyMeasurable_left hρm hρIi hIi
  have hRIeq : R * I = (U ⁻¹' A).indicator R := by
    funext ω
    by_cases h : U ω ∈ A <;> simp [I, Set.indicator, h]
  have hρIeq : ρ * I = (U ⁻¹' A).indicator ρ := by
    funext ω
    by_cases h : U ω ∈ A <;> simp [I, Set.indicator, h]
  calc
    (∫ ω in X ⁻¹' C ∩ U ⁻¹' A, R ω ∂μ) = ∫ ω in X ⁻¹' C, (R * I) ω ∂μ := by
      rw [hRIeq, setIntegral_indicator hUA]
    _ = ∫ ω in X ⁻¹' C, (μ[R * I | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
      (setIntegral_condExp hGi hRIi hCX).symm
    _ = ∫ ω in X ⁻¹' C, (ρ * μ[I | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hfactor)
    _ = ∫ ω in X ⁻¹' C, (μ[ρ * I | (MeasurableSpace.comap X inferInstance)]) ω ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hpull.symm)
    _ = ∫ ω in X ⁻¹' C, (ρ * I) ω ∂μ := setIntegral_condExp hGi hρIi hCX
    _ = ∫ ω in X ⁻¹' C ∩ U ⁻¹' A, (μ[R | (MeasurableSpace.comap X inferInstance)]) ω ∂μ := by
      rw [hρIeq, setIntegral_indicator hUA]

end

end AronowAudit.P001.Wave1.MarSelection
