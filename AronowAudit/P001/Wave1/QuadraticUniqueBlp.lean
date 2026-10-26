import AronowAudit.P001.Wave1.QuadraticUniqueBlpBlueprint
import AronowAudit.P001.Wave1.QuadraticUniqueBlp.N1

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableP001cFinalQuadraticUniqueBlp (p : Prop) : Decidable p := Classical.propDecidable p

theorem uniform_quadratic_cef_unique_blp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X W : Ω → ℝ) (hX : Measurable X) (hW : Measurable W)
    (hi : IndepFun X W μ) (hx : μ.map X = uniformLaw 0 1)
    (hw : μ.map W = gaussianReal 0 1) :
    let Y : Ω → ℝ := fun ω => 10 * (X ω)^2 + W ω
    IsCEF μ X Y (fun x => 10 * x^2) ∧
    blpSlope μ X Y = 10 ∧ blpIntercept μ X Y = -5 / 3 ∧
    (∀ a b : ℝ,
      linearRisk μ X Y (-5 / 3) 10 ≤ linearRisk μ X Y a b ∧
      (linearRisk μ X Y a b = linearRisk μ X Y (-5 / 3) 10 ↔
        a = -5 / 3 ∧ b = 10)) :=
  QuadraticUniqueBlp.assemble QuadraticUniqueBlp.n1_proof μ X W hX hW hi hx hw

end
end AronowAudit.P001.Wave1
