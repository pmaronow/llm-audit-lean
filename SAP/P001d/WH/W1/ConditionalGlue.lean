import SAP.P001d.Defs.WholeW1
import SAP.P001d.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W1

/-- First moments suffice for both residual mean identities. -/
theorem residual_means {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y : Ω → ℝ) (m : E → ℝ) (hm : IsCEF μ X Y m) :
    let ε := fun ω => Y ω - m (X ω)
    Integrable ε μ ∧ IsCEF μ X ε (fun _ => 0) ∧ (∫ ω, ε ω ∂μ) = 0 ∧
    ((fun _ : Ω => (0 : ℝ)) =ᵐ[μ] μ[ε | MeasurableSpace.comap X inferInstance]) := by
  let ε := fun ω => Y ω - m (X ω)
  have hεi : Integrable ε μ := hm.2.1.sub hm.2.2.1
  have hc : IsCEF μ X ε (fun _ => 0) := by
    refine ⟨measurable_const, hεi, integrable_const _, ?_⟩
    intro A hA
    change (∫ ω in X ⁻¹' A, Y ω - (m ∘ X) ω ∂μ) =
      ∫ ω in X ⁻¹' A, (0 : ℝ) ∂μ
    rw [integral_sub hm.2.1.integrableOn hm.2.2.1.integrableOn]
    simp only [Function.comp_apply]
    rw [hm.2.2.2 A hA, sub_self, integral_zero]
  have hmean : (∫ ω, ε ω ∂μ) = 0 := by
    have h := hc.2.2.2 Set.univ MeasurableSet.univ
    simpa only [Set.preimage_univ, Measure.restrict_univ, integral_zero] using h
  exact ⟨hεi, hc, hmean, AronowAudit.P001.isCEF_condExp μ X hX ε (fun _ => 0)
    ((Bridge.cef_iff _ _ _ _).mp hc)⟩

/-- Independence and the marginal law give a constant conditional-law version. -/
theorem independent_conditional_law {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlaw : μ.map Z = ν) (hi : IndepFun X Z μ) :
    WholeConditionalLaw μ X Z (fun _ => ν) := by
  refine ⟨fun _ => inferInstance, fun _ _ => measurable_const, ?_⟩
  intro A B hA hB
  have he : {ω | X ω ∈ A ∧ Z ω ∈ B} = X ⁻¹' A ∩ Z ⁻¹' B := rfl
  rw [he, (indepFun_iff_measure_inter_preimage_eq_mul.mp hi) A B hA hB,
    ← Measure.map_apply hX hA, ← Measure.map_apply hZ hB, hlaw]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  exact mul_comm _ _

/-- The general additive-noise CEF identity, with the author's usual
measurability convention and explicit existence of all expectations used. -/
theorem whole68 : T68WholeStatement := by
  intro Ω _ μ _ X ε hX hε hi hεi hε0 g hg hgi
  have hc := AronowAudit.P001.additive_independent_noise_cef μ X ε hX hε hi
    hεi hε0 g hg hgi
  exact ⟨hgi.add hεi, (Bridge.cef_iff _ _ _ _).mpr hc,
    AronowAudit.P001.isCEF_condExp μ X hX _ g hc⟩

/-- The existing four-point example explicitly fails event factorization. -/
theorem ordinary_nonindependence : T73Statement := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [finiteProb, heteroX, Fin.sum_univ_succ]
  · norm_num [finiteProb, heteroX, Fin.sum_univ_succ]
  · simpa only [Bridge.finiteCond_eq, Bridge.finiteMean_eq, Bridge.finiteCov_eq,
      Bridge.project_finiteProb_eq, Bridge.heteroX_eq, Bridge.heteroY_eq,
      Bridge.heteroResidual_eq] using AronowAudit.P001.cef_residual_not_independent

end SAP.P001d.WH.W1
