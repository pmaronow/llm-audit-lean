import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T11. -/
def T11Statement : Prop :=
  ((∀ h s : ℝ, printedInterval 0.691 h → printedInterval 0.318 s →
      0.4205 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.4232) ∧
    (∀ h s : ℝ, printedInterval 0.775 h → printedInterval 0.503 s →
      0.6936 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.6954) ∧
    (∀ h s : ℝ, printedInterval 0.627 h → printedInterval 0.406 s →
      0.4700 ≤ normalTwoSided (hazardWald h s) ∧ normalTwoSided (hazardWald h s) ≤ 0.4720) ∧
    abs (abs (hazardWald 0.691 0.318) - 0.8032) ≤ 0.00005 ∧
    abs (abs (hazardWald 0.775 0.503) - 0.3927) ≤ 0.00005 ∧
    abs (abs (hazardWald 0.627 0.406) - 0.7209) ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.691 0.318) - 0.4219| ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.775 0.503) - 0.6945| ≤ 0.00005 ∧
    |normalTwoSided (hazardWald 0.627 0.406) - 0.4710| ≤ 0.00005) ∧
  ((∀ h s : ℝ, printedInterval 0.691 h → printedInterval 0.318 s → |hazardWald h s| < 1) ∧
    (∀ h s : ℝ, printedInterval 0.775 h → printedInterval 0.503 s → |hazardWald h s| < 1) ∧
    (∀ h s : ℝ, printedInterval 0.627 h → printedInterval 0.406 s → |hazardWald h s| < 1))

end SAP.P041
