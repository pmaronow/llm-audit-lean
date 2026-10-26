import AronowAudit.P001.Wave1.MarSelectionBlueprint
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.MeasurableSpace.Prod

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The `[0,1]` bound of `N1`, for an indicator measurable for the ambient σ-algebra. -/
private lemma condExp_bounds01 {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (R : Ω → ℝ)
    (hR : Measurable[mΩ] R) (hbin : ∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) :
    ∀ᵐ ω ∂μ, 0 ≤ (μ[R | m]) ω ∧ (μ[R | m]) ω ≤ 1 := by
  have hbound : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hRi : Integrable R μ := Integrable.of_bound hR.aestronglyMeasurable 1 hbound
  have hnonneg : (0 : Ω → ℝ) ≤ᵐ[μ] R := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hle : R ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hlow := condExp_nonneg (m := m) hnonneg
  have hupp := condExp_mono (m := m) hRi (integrable_const (1 : ℝ)) hle
  rw [condExp_const hm (1 : ℝ)] at hupp
  filter_upwards [hlow, hupp] with ω hω0 hω1
  exact ⟨hω0, hω1⟩

theorem n4_proof : N4.{u, v, w} := by
  intro hN1 hN3 hN2 Ω E F _ _ _ μ _ X hX U R hU hR hbin hCI g hg hVi
  let P : Ω → E × F := fun ω => (X ω, U ω)
  let V : Ω → ℝ := fun ω => g (X ω, U ω)
  let ρ : Ω → ℝ := μ[R | (MeasurableSpace.comap X inferInstance)]
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hH : (MeasurableSpace.comap P inferInstance) ≤ ‹MeasurableSpace Ω› := (hX.prodMk hU).comap_le
  have hGH : (MeasurableSpace.comap X inferInstance) ≤ (MeasurableSpace.comap P inferInstance) := by
    exact (measurable_fst.comp (comap_measurable P)).comap_le
  have hVm : StronglyMeasurable[(MeasurableSpace.comap P inferInstance)] V := (hg.comp (comap_measurable P)).stronglyMeasurable
  have hRb : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hbin] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hRi : Integrable R μ := Integrable.of_bound hR.aestronglyMeasurable 1 hRb
  have hρm : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] ρ := stronglyMeasurable_condExp
  have hρb : ∀ᵐ ω ∂μ, ‖ρ ω‖ ≤ (1 : ℝ) := by
    filter_upwards [condExp_bounds01 μ (MeasurableSpace.comap X inferInstance) hG R hR hbin]
      with ω hω
    show ‖(μ[R | MeasurableSpace.comap X inferInstance]) ω‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2
  have hRVi : Integrable (R * V) μ := hVi.bdd_mul hR.aestronglyMeasurable hRb
  have hρVi : Integrable (ρ * V) μ :=
    hVi.bdd_mul (hρm.mono hG).aestronglyMeasurable hρb
  have hpullH : μ[R * V | (MeasurableSpace.comap P inferInstance)] =ᵐ[μ] μ[R | (MeasurableSpace.comap P inferInstance)] * V :=
    condExp_mul_of_stronglyMeasurable_right hVm hRVi hRi
  have hselect : μ[R | (MeasurableSpace.comap P inferInstance)] =ᵐ[μ] ρ := hN3 hN1 hN2 μ X hX U R hU hR hbin hCI
  have hinner : μ[R * V | (MeasurableSpace.comap P inferInstance)] =ᵐ[μ] ρ * V := by
    filter_upwards [hpullH, hselect] with ω hω hωR
    simpa only [Pi.mul_apply, hωR] using hω
  refine ⟨hRVi, ?_⟩
  change μ[R * V | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] ρ * μ[V | (MeasurableSpace.comap X inferInstance)]
  calc
    μ[R * V | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[μ[R * V | (MeasurableSpace.comap P inferInstance)] | (MeasurableSpace.comap X inferInstance)] := (condExp_condExp_of_le hGH hH).symm
    _ =ᵐ[μ] μ[ρ * V | (MeasurableSpace.comap X inferInstance)] := condExp_congr_ae hinner
    _ =ᵐ[μ] ρ * μ[V | (MeasurableSpace.comap X inferInstance)] := condExp_mul_of_stronglyMeasurable_left hρm hρVi hVi

end

end AronowAudit.P001.Wave1.MarSelection
