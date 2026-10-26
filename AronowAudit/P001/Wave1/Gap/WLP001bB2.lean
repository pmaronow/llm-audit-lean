import AronowAudit.P001.Wave1.Gap.PlaceboFTest

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter Set AronowAudit.P001
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableWLP001bB2 (p : Prop) : Decidable p := Classical.propDecidable p

/-- P001-T17: iid placebo F/Wald failure, using finite-support regression,
OLS/HC0 covariance estimates, reference quantiles, and rejection probabilities. -/
theorem placebo_iid_f_wald_failure {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
  (hiid : IID μ Z) (hlaw : μ.map (Z 0)=finiteLawMeasure placeboLaw) :
  FCondIndep placeboLaw placeboW placeboD placeboX ∧
  FCondIndep placeboLaw (fun i => (2+placeboZ i,3+placeboZ i)) placeboD placeboX ∧
  placeboMoment.det=17/54 ∧
  (∀ a b c : ℝ, placeboRisk (29/68) 0 (4/17) ≤ placeboRisk a b c ∧
    (placeboRisk a b c=placeboRisk (29/68) 0 (4/17) ↔ a=29/68 ∧ b=0 ∧ c=4/17)) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleF Z n ω/(n : ℝ)) atTop (nhds (64/531))) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleWald Z n ω/(n : ℝ)) atTop (nhds (18496/135315))) ∧
  (∀ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 → ∀ critical : ℕ → ℝ,
    (∀ n : ℕ, 3 < n → prob (fReference 1 (n-3)) (Set.Iic (critical n))=1-α) →
    Tendsto (fun n => prob μ {ω | critical n < placeboSampleF Z n ω}) atTop (nhds 1)) ∧
  (∀ c : ℝ, Tendsto (fun n => prob μ {ω | c < placeboSampleWald Z n ω}) atTop (nhds 1)) ∧
  240*placeboRisk (7/12) 0 0=175/3 ∧
  240*placeboRisk (29/68) 0 (4/17)=885/17 ∧
  ((240*placeboRisk (7/12) 0 0-240*placeboRisk (29/68) 0 (4/17))/
    (240*placeboRisk (29/68) 0 (4/17)/(240-3))=5056/177) := by
  exact placebo_linear_test_counterexample_proof μ Z hiid hlaw

end
end AronowAudit.P001.Wave1
