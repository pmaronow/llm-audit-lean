import SAP.P001d.WH.W1.Leaves
import Mathlib.MeasureTheory.Function.FactorsThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W1.P.T74_L2V2

end SAP.P001d.WH.W1.P.T74_L2V2

theorem SAP.P001d.WH.W1.T74_L2V2_proof : SAP.P001d.WH.W1.T74_L2V2 := by
  classical
  intro Ω E _ _ μ _ X hX Y hY m hm hR2
  let R : Ω → ℝ := fun ω => Y ω - m (X ω)
  have hG : MeasurableSpace.comap X inferInstance ≤
      (inferInstance : MeasurableSpace Ω) := hX.comap_le
  have hRmeas : Measurable R := hY.sub (hm.1.comp hX)
  have hres := SAP.P001d.WH.W1.residual_means μ X hX Y m hm
  have hRi : Integrable R μ := hres.1
  have hRcef : IsCEF μ X R (fun _ => 0) := hres.2.1
  have hmean : (∫ ω, R ω ∂μ) = 0 := hres.2.2.1
  have hRce0 : (fun _ => (0 : ℝ)) =ᵐ[μ]
      μ[R | MeasurableSpace.comap X inferInstance] := hres.2.2.2
  have hR2i : Integrable (fun ω => R ω ^ 2) μ := hR2

  obtain ⟨v, hvsm, hVeq⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap X inferInstance)
      (f := fun ω => R ω ^ 2)).exists_eq_measurable_comp
  have hVi : Integrable
      (μ[(fun ω => R ω ^ 2) | MeasurableSpace.comap X inferInstance]) μ :=
    integrable_condExp (m := MeasurableSpace.comap X inferInstance)
      (f := fun ω => R ω ^ 2)
  have hvXi : Integrable (v ∘ X) μ :=
    hVi.congr (Filter.Eventually.of_forall fun ω => congrFun hVeq ω)
  have hcefR2 : IsCEF μ X (fun ω => R ω ^ 2) v := by
    refine ⟨hvsm.measurable, hR2i, hvXi, ?_⟩
    intro A hA
    calc
      (∫ ω in X ⁻¹' A, R ω ^ 2 ∂μ) =
          ∫ ω in X ⁻¹' A,
            μ[(fun ω => R ω ^ 2) | MeasurableSpace.comap X inferInstance] ω ∂μ :=
        (setIntegral_condExp (m := MeasurableSpace.comap X inferInstance)
          hG hR2i ⟨A, hA, rfl⟩).symm
      _ = ∫ ω in X ⁻¹' A, v (X ω) ∂μ :=
        setIntegral_congr_ae (hA.preimage hX)
          (Filter.Eventually.of_forall fun ω _ => congrFun hVeq ω)

  have hYce : (m ∘ X) =ᵐ[μ]
      μ[Y | MeasurableSpace.comap X inferInstance] :=
    AronowAudit.P001.isCEF_condExp μ X hX Y m hm
  have hYcenter : (fun ω =>
      Y ω - μ[Y | MeasurableSpace.comap X inferInstance] ω) =ᵐ[μ] R := by
    filter_upwards [hYce] with ω hω
    change Y ω - μ[Y | MeasurableSpace.comap X inferInstance] ω =
      Y ω - m (X ω)
    rw [← hω]
    rfl
  have hRcenter : (fun ω =>
      R ω - μ[R | MeasurableSpace.comap X inferInstance] ω) =ᵐ[μ] R := by
    filter_upwards [hRce0] with ω hω
    rw [← hω]
    simp
  have hYsq : (fun ω =>
      (Y ω - μ[Y | MeasurableSpace.comap X inferInstance] ω) ^ 2) =ᵐ[μ]
      (fun ω => R ω ^ 2) := hYcenter.mono fun ω h => congrArg (fun z : ℝ => z ^ 2) h
  have hRsq : (fun ω =>
      (R ω - μ[R | MeasurableSpace.comap X inferInstance] ω) ^ 2) =ᵐ[μ]
      (fun ω => R ω ^ 2) := hRcenter.mono fun ω h => congrArg (fun z : ℝ => z ^ 2) h
  have hYcond : wholeConditionalVariance μ X Y =ᵐ[μ]
      μ[(fun ω => R ω ^ 2) | MeasurableSpace.comap X inferInstance] := by
    change μ[(fun ω =>
      (Y ω - μ[Y | MeasurableSpace.comap X inferInstance] ω) ^ 2) |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[(fun ω => R ω ^ 2) | MeasurableSpace.comap X inferInstance]
    exact condExp_congr_ae (m := MeasurableSpace.comap X inferInstance) hYsq
  have hRcond : wholeConditionalVariance μ X R =ᵐ[μ]
      μ[(fun ω => R ω ^ 2) | MeasurableSpace.comap X inferInstance] := by
    change μ[(fun ω =>
      (R ω - μ[R | MeasurableSpace.comap X inferInstance] ω) ^ 2) |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[(fun ω => R ω ^ 2) | MeasurableSpace.comap X inferInstance]
    exact condExp_congr_ae (m := MeasurableSpace.comap X inferInstance) hRsq
  have hYv : wholeConditionalVariance μ X Y =ᵐ[μ] v ∘ X :=
    hYcond.trans (Filter.Eventually.of_forall fun ω => congrFun hVeq ω)
  have hYint : Integrable (wholeConditionalVariance μ X Y) μ :=
    hVi.congr hYcond.symm
  have htotal : variance R μ =
      ∫ ω, wholeConditionalVariance μ X Y ω ∂μ := by
    calc
      variance R μ = ∫ ω, (R ω - ∫ ω', R ω' ∂μ) ^ 2 ∂μ :=
        ProbabilityTheory.variance_eq_integral hRmeas.aemeasurable
      _ = ∫ ω, R ω ^ 2 ∂μ := by rw [hmean]; simp
      _ = ∫ ω,
          μ[(fun ω => R ω ^ 2) | MeasurableSpace.comap X inferInstance] ω ∂μ :=
        (integral_condExp (m := MeasurableSpace.comap X inferInstance)
          (f := fun ω => R ω ^ 2) hG).symm
      _ = ∫ ω, wholeConditionalVariance μ X Y ω ∂μ :=
        integral_congr_ae hYcond.symm
  refine ⟨v, hcefR2, ?_, hYv, hYint, htotal⟩
  exact hRcond.trans hYcond.symm
