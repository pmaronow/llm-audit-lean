import AronowAudit.P001.Wave1.MarSelectionBlueprint
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n6_proof : N6.{u, v, w} := by
  intro hN1 hN4 hN3 hN2 Ω E F _ _ _ μ _ X hX U R g q
    hU hR hg hq hbin hCI hVi hbound
  let V : Ω → ℝ := fun ω => g (X ω, U ω)
  let a : Ω → ℝ := fun ω => (q (X ω))⁻¹
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := comap_measurable X
  have ham : StronglyMeasurable[(MeasurableSpace.comap X inferInstance)] a := ((hq.comp hXm).inv).stronglyMeasurable
  obtain ⟨c, hc, hcq⟩ := hbound
  have hab : ∀ᵐ ω ∂μ, ‖a ω‖ ≤ c⁻¹ := by
    filter_upwards [hcq] with ω hω
    have hqpos : 0 < q (X ω) := hc.trans_le hω
    change ‖(q (X ω))⁻¹‖ ≤ c⁻¹
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hqpos]
    simpa only [one_div] using one_div_le_one_div_of_le hc hω
  obtain ⟨hRVi, hfactor⟩ := hN4 hN1 hN3 hN2 μ X hX U R hU hR hbin hCI g hg hVi
  have hweighted : Integrable (a * (R * V)) μ :=
    hRVi.bdd_mul (ham.mono hG).aestronglyMeasurable hab
  have heq : a * (R * V) = (fun ω => R ω * g (X ω, U ω) / q (X ω)) := by
    funext ω
    simp only [a, V, Pi.mul_apply, div_eq_mul_inv]
    ring
  have hpull : μ[a * (R * V) | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] a * μ[R * V | (MeasurableSpace.comap X inferInstance)] :=
    condExp_mul_of_stronglyMeasurable_left ham hweighted hRVi
  refine ⟨hweighted.congr (Filter.Eventually.of_forall (congrFun heq)), ?_⟩
  calc
    (∫ ω, R ω * g (X ω, U ω) / q (X ω) ∂μ) = ∫ ω, (a * (R * V)) ω ∂μ := by rw [heq]
    _ = ∫ ω, (μ[a * (R * V) | (MeasurableSpace.comap X inferInstance)]) ω ∂μ := (integral_condExp hG).symm
    _ = ∫ ω, (a * μ[R * V | (MeasurableSpace.comap X inferInstance)]) ω ∂μ := integral_congr_ae hpull
    _ = ∫ ω, (μ[R | (MeasurableSpace.comap X inferInstance)]) ω * (μ[V | (MeasurableSpace.comap X inferInstance)]) ω / q (X ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfactor] with ω hω
      change a ω * (μ[(fun ω => R ω * g (X ω, U ω)) | (MeasurableSpace.comap X inferInstance)]) ω =
        (μ[R | (MeasurableSpace.comap X inferInstance)]) ω * (μ[(fun ω => g (X ω, U ω)) | (MeasurableSpace.comap X inferInstance)]) ω / q (X ω)
      rw [hω]
      simp only [a, div_eq_mul_inv]
      ring

end

end AronowAudit.P001.Wave1.MarSelection
