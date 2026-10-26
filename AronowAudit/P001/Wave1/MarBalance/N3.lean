import AronowAudit.P001.Wave1.MarBalanceBlueprint
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1.MarBalance

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n3_proof : N3.{u, v} := by
  classical
  intro hbinary _hunit Ω E _ _ μ _ X hX Y R p hp _hY hR hbin hCI
  let S : Ω → ℝ := p ∘ X
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := comap_measurable X
  have hHG : (MeasurableSpace.comap S inferInstance) ≤ (MeasurableSpace.comap X inferInstance) := (hp.1.comp hXm).comap_le
  have hH : (MeasurableSpace.comap S inferInstance) ≤ ‹MeasurableSpace Ω› := (hp.1.comp hX).comap_le
  intro A B hA hB
  let I : Ω → ℝ := (Y ⁻¹' A).indicator (fun _ => 1)
  let J : Ω → ℝ := (R ⁻¹' B).indicator (fun _ => 1)
  let f : ℝ → ℝ := fun s => (if (0 : ℝ) ∈ B then 1 - s else 0) +
    (if (1 : ℝ) ∈ B then s else 0)
  let r : Ω → ℝ := f ∘ S
  have hfm : Measurable f := by
    dsimp [f]
    split_ifs <;> fun_prop
  have hrm : StronglyMeasurable[(MeasurableSpace.comap S inferInstance)] r := (hfm.comp (comap_measurable S)).stronglyMeasurable
  have hb : μ[J | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] r := hbinary μ X R p hX hR hbin hp B hB
  have hri : Integrable r μ := integrable_condExp.congr hb
  have hrfix : μ[r | (MeasurableSpace.comap S inferInstance)] = r := condExp_of_stronglyMeasurable hH hrm hri
  have hJH : μ[J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] r := by
    calc
      μ[J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] μ[μ[J | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := (condExp_condExp_of_le hHG hG).symm
      _ =ᵐ[μ] μ[r | (MeasurableSpace.comap S inferInstance)] := condExp_congr_ae hb
      _ =ᵐ[μ] r := Filter.Eventually.of_forall (congrFun hrfix)
  have hjoin : (fun ω => if Y ω ∈ A ∧ R ω ∈ B then (1 : ℝ) else 0) = I * J := by
    funext ω
    by_cases hωA : Y ω ∈ A <;> by_cases hωB : R ω ∈ B <;>
      simp [I, J, Set.indicator, hωA, hωB]
  have hci : μ[I * J | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[I | (MeasurableSpace.comap X inferInstance)] * μ[J | (MeasurableSpace.comap X inferInstance)] := by
    rw [← hjoin]
    exact hCI A B hA hB
  have hinner : μ[I * J | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] r * μ[I | (MeasurableSpace.comap X inferInstance)] := by
    filter_upwards [hci, hb] with ω hω hωb
    change (μ[I * J | (MeasurableSpace.comap X inferInstance)]) ω = r ω * (μ[I | (MeasurableSpace.comap X inferInstance)]) ω
    calc
      (μ[I * J | (MeasurableSpace.comap X inferInstance)]) ω = (μ[I | (MeasurableSpace.comap X inferInstance)]) ω * (μ[J | (MeasurableSpace.comap X inferInstance)]) ω := hω
      _ = r ω * (μ[I | (MeasurableSpace.comap X inferInstance)]) ω := by rw [hωb]; ring
  -- Integrability of the product follows from its equality to a conditional
  -- expectation, so no outcome moment or separate bound on Y is needed.
  have hinneri : Integrable (r * μ[I | (MeasurableSpace.comap X inferInstance)]) μ := integrable_condExp.congr hinner
  have hpull : μ[r * μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] r * μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] :=
    condExp_mul_of_stronglyMeasurable_left hrm hinneri integrable_condExp
  have htowerI : μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] μ[I | (MeasurableSpace.comap S inferInstance)] := condExp_condExp_of_le hHG hG
  have hproduct : μ[I * J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] r * μ[I | (MeasurableSpace.comap S inferInstance)] := by
    calc
      μ[I * J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] μ[μ[I * J | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := (condExp_condExp_of_le hHG hG).symm
      _ =ᵐ[μ] μ[r * μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := condExp_congr_ae hinner
      _ =ᵐ[μ] r * μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := hpull
      _ =ᵐ[μ] r * μ[I | (MeasurableSpace.comap S inferInstance)] := by
        filter_upwards [htowerI] with ω hω
        change r ω * (μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)]) ω = r ω * (μ[I | (MeasurableSpace.comap S inferInstance)]) ω
        rw [hω]
  change μ[(fun ω => if Y ω ∈ A ∧ R ω ∈ B then (1 : ℝ) else 0) | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ]
    μ[I | (MeasurableSpace.comap S inferInstance)] * μ[J | (MeasurableSpace.comap S inferInstance)]
  rw [hjoin]
  filter_upwards [hproduct, hJH] with ω hω hωJ
  change (μ[I * J | (MeasurableSpace.comap S inferInstance)]) ω = (μ[I | (MeasurableSpace.comap S inferInstance)]) ω * (μ[J | (MeasurableSpace.comap S inferInstance)]) ω
  rw [hω]
  change r ω * (μ[I | (MeasurableSpace.comap S inferInstance)]) ω = (μ[I | (MeasurableSpace.comap S inferInstance)]) ω * (μ[J | (MeasurableSpace.comap S inferInstance)]) ω
  rw [hωJ]
  ring

end

end AronowAudit.P001.Wave1.MarBalance
