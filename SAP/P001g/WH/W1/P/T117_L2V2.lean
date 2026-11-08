import SAP.P001g.WH.W1.Leaves
import AronowAudit.P001.P001_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.WH.W1.P.T117_L2V2

open MeasureTheory
open scoped MeasureTheory

noncomputable section

private theorem residual_isCEF {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ) (p : E → ℝ)
    (hp : AronowAudit.P001.IsCEF μ X D p) :
    AronowAudit.P001.IsCEF μ X (fun ω => p (X ω) - D ω) (fun _ => 0) := by
  have hpX : Integrable (fun ω => p (X ω)) μ := hp.2.2.1
  have hD : Integrable D μ := hp.2.1
  have hR : Integrable (fun ω => p (X ω) - D ω) μ := hpX.sub hD
  refine ⟨measurable_const, hR, integrable_const _, ?_⟩
  intro A hA
  change (∫ ω in X ⁻¹' A, p (X ω) - D ω ∂μ) = ∫ ω in X ⁻¹' A, (0 : ℝ) ∂μ
  rw [integral_sub hpX.integrableOn hD.integrableOn, hp.2.2.2 A hA]
  simp

end

end SAP.P001g.WH.W1.P.T117_L2V2

open MeasureTheory
open scoped MeasureTheory

theorem SAP.P001g.WH.W1.T117_L2V2_proof : SAP.P001g.WH.W1.T117_L2V2 := by
  intro Ω E instΩ instE μ hμ X hX D p hp H hH hprod
  let R : Ω → ℝ := fun ω => p (X ω) - D ω
  have hR : Integrable R μ := by
    exact (hp.2.2.1.sub hp.2.1)
  have hRcef : AronowAudit.P001.IsCEF μ X R (fun _ => 0) := by
    simpa [R] using
      @SAP.P001g.WH.W1.P.T117_L2V2.residual_isCEF Ω E instΩ instE μ hμ X D p hp
  have hX_m : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hH_m : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (H ∘ X) :=
    (hH.comp hX_m).stronglyMeasurable
  have hzero : μ[R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] (fun _ => 0) := by
    simpa [Function.comp_def] using
      (AronowAudit.P001.isCEF_condExp μ X hX R (fun _ => 0) hRcef).symm
  have hpull : μ[(H ∘ X) * R | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      (H ∘ X) * μ[R | MeasurableSpace.comap X inferInstance] := by
    apply condExp_mul_of_stronglyMeasurable_left hH_m
    · change Integrable (fun ω => H (X ω) * (p (X ω) - D ω)) μ
      exact hprod
    · exact hR
  change (∫ ω, H (X ω) * (p (X ω) - D ω) ∂μ) = 0
  calc
    (∫ ω, H (X ω) * (p (X ω) - D ω) ∂μ) =
        ∫ ω, μ[(H ∘ X) * R | MeasurableSpace.comap X inferInstance] ω ∂μ := by
          simpa [R, Function.comp_def] using
            (integral_condExp hX.comap_le (f := (H ∘ X) * R)).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hpull, hzero] with ω hpullω hzeroω
      rw [hpullω]
      simp [hzeroω]
