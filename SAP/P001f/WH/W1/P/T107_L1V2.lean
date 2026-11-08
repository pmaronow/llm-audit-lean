import SAP.P001f.WH.W1.Leaves
import AronowAudit.P001.P001_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory

namespace SAP.P001f.WH.W1.P.T107_L1V2

private theorem residual_isCEF {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Measurable Y) (m : E → ℝ)
    (hm : SAP.P001f.ConditionalMean μ X Y m) :
    AronowAudit.P001.IsCEF μ X (fun ω => Y ω - m (X ω)) (fun _ => 0) := by
  change AronowAudit.P001.IsCEF μ X Y m at hm
  let R : Ω → ℝ := fun ω => Y ω - m (X ω)
  have hMi : Integrable (m ∘ X) μ := hm.2.2.1
  have hRi : Integrable R μ := by
    exact hm.2.1.sub hMi
  have hRc : Measurable R := by
    exact hY.sub (hm.1.comp hX)
  refine ⟨measurable_const, hRi, integrable_const _, ?_⟩
  intro A hA
  have hSubSet :
      (∫ ω in X ⁻¹' A, (Y - m ∘ X) ω ∂μ) =
        (∫ ω in X ⁻¹' A, Y ω ∂μ) - (∫ ω in X ⁻¹' A, (m ∘ X) ω ∂μ) := by
    exact integral_sub hm.2.1.integrableOn hMi.integrableOn
  change (∫ ω in X ⁻¹' A, (Y - m ∘ X) ω ∂μ) = _
  rw [hSubSet, hm.2.2.2 A hA]
  simp

end SAP.P001f.WH.W1.P.T107_L1V2

theorem SAP.P001f.WH.W1.T107_L1V2_proof : SAP.P001f.WH.W1.T107_L1V2 := by
  intro Ω E _ _ μ _ X hX Y hY m hm hRsq d hd hd2
  let R : Ω → ℝ := fun ω => Y ω - m (X ω)
  have hRcef : AronowAudit.P001.IsCEF μ X R (fun _ => 0) := by
    simpa [R] using SAP.P001f.WH.W1.P.T107_L1V2.residual_isCEF μ X hX Y hY m hm
  have hRm : Measurable R := by
    exact hY.sub (hm.1.comp hX)
  have hR2 : MemLp R 2 μ :=
    (memLp_two_iff_integrable_sq hRm.aestronglyMeasurable).2 (by simpa [R] using hRsq)
  have hRi : Integrable R μ := hRcef.2.1
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hDm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (d ∘ X) :=
    (hd.comp hXm).stronglyMeasurable
  have hz : μ[R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] (fun _ => 0) :=
    (AronowAudit.P001.isCEF_condExp μ X hX R (fun _ => 0) hRcef).symm
  have hmul := condExp_mul_of_stronglyMeasurable_left hDm (hd2.integrable_mul hR2) hRi
  have hprod : (∫ ω, ((d ∘ X) * R) ω ∂μ) = 0 := by
    rw [← integral_condExp hX.comap_le (f := (d ∘ X) * R)]
    apply integral_eq_zero_of_ae
    filter_upwards [hmul, hz] with ω hω hzero
    simp only [hω, Pi.mul_apply, hzero, mul_zero, Pi.zero_apply]
  change (∫ ω, d (X ω) * (Y ω - m (X ω)) ∂μ) = 0
  simpa [R, Function.comp_def] using hprod
