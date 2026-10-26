import AronowAudit.P001.P001_Foundations

/-!
P001-T47: independence, constant conditional expectations, and best linear prediction
for transformations that are a.e. measurable under the marginal laws.
-/

namespace AronowAudit.P001.Wave1
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableDecisionT47 (p : Prop) : Decidable p := Classical.propDecidable p

theorem independent_functions_cef_law_measurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y μ) (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 μ)
    (g h : ℝ → ℝ) (hgX : Measurable (g ∘ X)) (hhY : Measurable (h ∘ Y))
    (hg : AEMeasurable g (μ.map X)) (hh : AEMeasurable h (μ.map Y))
    (hg2 : MemLp (g ∘ X) 2 μ) (hh2 : MemLp (h ∘ Y) 2 μ) :
    IsCEF μ X Y (fun _ => mean μ Y) ∧
    IsCEF μ X (fun ω => (Y ω - mean μ Y)^2) (fun _ => var μ Y) ∧
    (∀ a b : ℝ, linearRisk μ X Y (mean μ Y) 0 ≤ linearRisk μ X Y a b) ∧
    (0 < var μ X → blpSlope μ X Y = 0 ∧ blpIntercept μ X Y = mean μ Y) ∧
    IndepFun (g ∘ X) (h ∘ Y) μ ∧
    IsCEF μ (g ∘ X) (h ∘ Y) (fun _ => mean μ (h ∘ Y)) ∧
    (∀ a b : ℝ,
      linearRisk μ (g ∘ X) (h ∘ Y) (mean μ (h ∘ Y)) 0 ≤
        linearRisk μ (g ∘ X) (h ∘ Y) a b) ∧
    (0 < var μ (g ∘ X) →
      blpSlope μ (g ∘ X) (h ∘ Y) = 0 ∧
      blpIntercept μ (g ∘ X) (h ∘ Y) = mean μ (h ∘ Y)) := by
  have hiTrans : IndepFun (g ∘ X) (h ∘ Y) μ :=
    hi.comp₀ hX.aemeasurable hY.aemeasurable hg hh
  have hOriginal := independence_variance_and_blp μ X Y hX2 hY2 hi
  refine ⟨independent_constant_cef μ X Y hX hY (hY2.integrable one_le_two) hi,
    hOriginal.1, hOriginal.2.1, ?_, hiTrans,
    independent_constant_cef μ (g ∘ X) (h ∘ Y) hgX hhY
      (hh2.integrable one_le_two) hiTrans,
    fun a b => independent_affine_risk_minimum μ (g ∘ X) (h ∘ Y) hg2 hh2 hiTrans a b,
    ?_⟩
  · intro _
    simp [blpSlope, blpIntercept, hi.covariance_eq_zero hX2 hY2]
  · intro _
    simp [blpSlope, blpIntercept, hiTrans.covariance_eq_zero hg2 hh2]


end
end AronowAudit.P001.Wave1
