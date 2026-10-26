import AronowAudit.P001.Wave1.MarBalanceBlueprint
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1.MarBalance

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n2_proof : N2.{u, v} := by
  classical
  intro hbinary _hunit Ω E _ _ μ _ X hX R p hp hR hbin
  let S : Ω → ℝ := p ∘ X
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := comap_measurable X
  have hHG : (MeasurableSpace.comap S inferInstance) ≤ (MeasurableSpace.comap X inferInstance) := (hp.1.comp hXm).comap_le
  have hH : (MeasurableSpace.comap S inferInstance) ≤ ‹MeasurableSpace Ω› := (hp.1.comp hX).comap_le
  have hself : IsCEF μ S R id := by
    refine ⟨measurable_id, hp.2.1, hp.2.2.1, ?_⟩
    intro A hA
    exact hp.2.2.2 (p ⁻¹' A) (hA.preimage hp.1)
  refine ⟨?_, hself⟩
  intro A B hA hB
  let I : Ω → ℝ := (R ⁻¹' A).indicator (fun _ => 1)
  let J : Ω → ℝ := (X ⁻¹' B).indicator (fun _ => 1)
  let f : ℝ → ℝ := fun s => (if (0 : ℝ) ∈ A then 1 - s else 0) +
    (if (1 : ℝ) ∈ A then s else 0)
  let r : Ω → ℝ := f ∘ S
  have hfm : Measurable f := by
    dsimp [f]
    split_ifs <;> fun_prop
  have hrm : StronglyMeasurable[(MeasurableSpace.comap S inferInstance)] r := (hfm.comp (comap_measurable S)).stronglyMeasurable
  have hb : μ[I | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] r := hbinary μ X R p hX hR hbin hp A hA
  have hri : Integrable r μ := integrable_condExp.congr hb
  have hrfix : μ[r | (MeasurableSpace.comap S inferInstance)] = r := condExp_of_stronglyMeasurable hH hrm hri
  have hIH : μ[I | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] r := by
    calc
      μ[I | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := (condExp_condExp_of_le hHG hG).symm
      _ =ᵐ[μ] μ[r | (MeasurableSpace.comap S inferInstance)] := condExp_congr_ae hb
      _ =ᵐ[μ] r := Filter.Eventually.of_forall (congrFun hrfix)
  have hIm : Measurable I := measurable_const.indicator (hA.preimage hR)
  have hJm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] J :=
    (measurable_const.indicator (show MeasurableSet[(MeasurableSpace.comap X inferInstance)] (X ⁻¹' B) from ⟨B, hB, rfl⟩)).stronglyMeasurable
  have hIb : ∀ᵐ ω ∂μ, ‖I ω‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun ω => by
      by_cases h : R ω ∈ A <;> simp [I, Set.indicator, h]
  have hJb : ∀ᵐ ω ∂μ, ‖J ω‖ ≤ (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun ω => by
      by_cases h : X ω ∈ B <;> simp [J, Set.indicator, h]
  have hIi : Integrable I μ := Integrable.of_bound hIm.aestronglyMeasurable 1 hIb
  have hIJi : Integrable (I * J) μ :=
    hIi.mul_bdd (hJm.mono hG).aestronglyMeasurable hJb
  have hrJi : Integrable (r * J) μ :=
    hri.mul_bdd (hJm.mono hG).aestronglyMeasurable hJb
  have hpullG : μ[I * J | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[I | (MeasurableSpace.comap X inferInstance)] * J :=
    condExp_mul_of_stronglyMeasurable_right hJm hIJi hIi
  have hinner : μ[I * J | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] r * J := by
    filter_upwards [hpullG, hb] with ω hω hωb
    simpa only [Pi.mul_apply, hωb] using hω
  have hproduct : μ[I * J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] r * μ[J | (MeasurableSpace.comap S inferInstance)] := by
    calc
      μ[I * J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] μ[μ[I * J | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := (condExp_condExp_of_le hHG hG).symm
      _ =ᵐ[μ] μ[r * J | (MeasurableSpace.comap S inferInstance)] := condExp_congr_ae hinner
      _ =ᵐ[μ] r * μ[J | (MeasurableSpace.comap S inferInstance)] := condExp_mul_of_stronglyMeasurable_left hrm hrJi
        (Integrable.of_bound (hJm.mono hG).aestronglyMeasurable 1 hJb)
  have hjoin : (fun ω => if R ω ∈ A ∧ X ω ∈ B then (1 : ℝ) else 0) = I * J := by
    funext ω
    by_cases hωA : R ω ∈ A <;> by_cases hωB : X ω ∈ B <;>
      simp [I, J, Set.indicator, hωA, hωB]
  change μ[(fun ω => if R ω ∈ A ∧ X ω ∈ B then (1 : ℝ) else 0) | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ]
    μ[I | (MeasurableSpace.comap S inferInstance)] * μ[J | (MeasurableSpace.comap S inferInstance)]
  rw [hjoin]
  filter_upwards [hproduct, hIH] with ω hω hωI
  simpa only [Pi.mul_apply, hωI] using hω

end

end AronowAudit.P001.Wave1.MarBalance
