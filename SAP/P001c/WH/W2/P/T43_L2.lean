import SAP.P001c.WH.W2.Leaves
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory

theorem SAP.P001c.WH.W2.T43_L2_proof : SAP.P001c.WH.W2.T43_L2 := by
  classical
  intro Ω hΩ μ hμ X Y hX hY
  obtain ⟨m, hm, hfactor⟩ :=
    (MeasureTheory.stronglyMeasurable_condExp (μ := μ)
      (m := MeasurableSpace.comap X inferInstance) (f := Y)).measurable.exists_eq_measurable_comp
  have hCE2 : MemLp (μ[Y | (MeasurableSpace.comap X inferInstance)]) 2 μ :=
    hY.condExp (by norm_num)
  have hcomp2 : MemLp (m ∘ X) 2 μ := by
    exact (memLp_congr_ae (Eventually.of_forall fun ω => congrFun hfactor ω)).mp hCE2
  have hcef : isConditionalMean μ X Y m := by
    change AronowAudit.P001.IsCEF μ X Y m
    refine ⟨hm, hY.integrable one_le_two, hcomp2.integrable one_le_two, ?_⟩
    intro A hA
    calc
      (∫ ω in X ⁻¹' A, Y ω ∂μ) =
        ∫ ω in X ⁻¹' A, μ[Y | (MeasurableSpace.comap X inferInstance)] ω ∂μ := by
        exact (setIntegral_condExp hX.comap_le (hY.integrable one_le_two)
          ⟨A, hA, rfl⟩).symm
      _ = ∫ ω in X ⁻¹' A, m (X ω) ∂μ := by
        exact setIntegral_congr_ae (hA.preimage hX)
          (Eventually.of_forall fun ω _ => congrFun hfactor ω)
  constructor
  · exact ⟨m, hcef, hcomp2⟩
  · intro m hm'
    have hmcef : AronowAudit.P001.IsCEF μ X Y m := hm'
    have hae : (m ∘ X) =ᵐ[μ]
        μ[Y | (MeasurableSpace.comap X inferInstance)] :=
      AronowAudit.P001.isCEF_condExp μ X hX Y m hmcef
    exact (memLp_congr_ae hae).mpr hCE2
