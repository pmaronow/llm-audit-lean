import SAP.P001c.Defs.WholeW2
import SAP.P001c.Bridge
import AronowAudit.P001.Wave1.UnbiasedMeanVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W2

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001 AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical ContDiff
universe u
noncomputable section

private theorem independent_blp {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 μ) (hi : IndepFun X Y μ) :
    wholeIndependentBlp μ X Y := by
  refine ⟨fun a b => independent_affine_risk_minimum μ X Y hX2 hY2 hi a b, ?_⟩
  intro hv
  have hs : regressionSlope μ X Y = 0 := by
    simp [regressionSlope, hi.covariance_eq_zero hX2 hY2]
  have ha : regressionIntercept μ X Y = expectation μ Y := by
    simp [regressionIntercept, hs]
  refine ⟨hs, ha, ?_⟩
  intro a b
  have hh :
      affineRisk μ X Y a b = affineRisk μ X Y (regressionIntercept μ X Y) (regressionSlope μ X Y) ↔
      a = regressionIntercept μ X Y ∧ b = regressionSlope μ X Y :=
    ((blp_corrected_derivatives_and_minimum μ X Y hX2 hY2 hv).2.2 a b).2
  simpa only [ha, hs] using hh

private theorem independent_covariance_L1 {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y μ)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) : covariance X Y μ = 0 := by
  have hmx : expectation μ (fun z => X z-expectation μ X) = 0 := by
    unfold expectation
    rw [integral_sub hXi (integrable_const _)]
    simp
  have hmy : expectation μ (fun z => Y z-expectation μ Y) = 0 := by
    unfold expectation
    rw [integral_sub hYi (integrable_const _)]
    simp
  have hi' : IndepFun (fun z => X z-expectation μ X) (fun z => Y z-expectation μ Y) μ :=
    hi.comp (show Measurable (fun x : ℝ => x-expectation μ X) by fun_prop)
      (show Measurable (fun y : ℝ => y-expectation μ Y) by fun_prop)
  calc
    covariance X Y μ = expectation μ (fun z => X z-expectation μ X) *
        expectation μ (fun z => Y z-expectation μ Y) :=
      hi'.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)
    _ = 0 := by rw [hmx, hmy]; ring

/-- Under the author's 2026-11-04 convention, all transformations are measurable.
Existing independence, integration and regression theorems prove the entire corrected
claim, with only the moments needed for each clause. No new mathematical leaf is needed. -/
theorem T47_assembly : T47WholeStatement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω _ μ _ X Y _ _
    constructor
    · intro hi g h hg hh
      exact hi.comp hg hh
    · intro hall
      exact hall id id measurable_id measurable_id
  · intro Ω _ μ _ X Y hX hY hi
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hYi
      exact independent_constant_cef μ X Y hX hY hYi hi
    · intro hY2
      have hsq : Integrable (fun z => (Y z-expectation μ Y)^2) μ :=
        (hY2.sub (memLp_const (expectation μ Y))).integrable_sq
      have hisq : IndepFun X (fun z => (Y z-expectation μ Y)^2) μ :=
        hi.comp measurable_id
          (show Measurable (fun y : ℝ => (y-expectation μ Y)^2) by fun_prop)
      have hh : isConditionalMean μ X (fun z => (Y z-expectation μ Y)^2)
          (fun _ => expectation μ (fun z => (Y z-expectation μ Y)^2)) :=
        independent_constant_cef μ X _ hX (by fun_prop) hsq hisq
      have hV : expectation μ (fun z => (Y z-expectation μ Y)^2) = variance Y μ :=
        (variance_eq_integral hY.aemeasurable).symm
      simpa only [hV] using hh
    · intro hXi hYi
      exact ⟨hi.integrable_mul hXi hYi,
        hi.integral_fun_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable,
        independent_covariance_L1 μ X Y hX hY hi hXi hYi⟩
    · intro hX2 hY2
      refine ⟨hi.variance_fun_add hX2 hY2, ?_, independent_blp μ X Y hX2 hY2 hi⟩
      intro _ _
      simp [correlationCoefficient, hi.covariance_eq_zero hX2 hY2]
    · intro g h hg hh
      have hit := hi.comp hg hh
      exact ⟨hit,
        fun hhi => independent_constant_cef μ (g ∘ X) (h ∘ Y) (hg.comp hX) (hh.comp hY) hhi hit,
        fun hg2 hh2 => independent_blp μ (g ∘ X) (h ∘ Y) hg2 hh2 hit⟩
  · intro Ω _ μ _ X Y _ _ hX2 hY2 hv
    exact (blp_corrected_derivatives_and_minimum μ X Y hX2 hY2 hv).2.2

end
end SAP.P001c.WH.W2
