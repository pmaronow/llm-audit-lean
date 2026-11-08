import SAP.P002a.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

/-- Standard normal absolute tail probability `P(|𝒵| ≥ x)` (Supplement p. 21, A.2). The measure is
a probability measure, so `toReal` never meets `∞`. -/
def normalTail (x : ℝ) : ℝ := (ProbabilityTheory.gaussianReal 0 1 {z : ℝ | x ≤ |z|}).toReal

def T7Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω)
    [IsProbabilityMeasure μ] (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k)
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ n, Xi (P n) δ e A B r)
    (hpositive : ∀ n a, 0 < popVar (residual (P n) a (late (P n).pop)))
    (hZ : RandomizationSequence (fun n => (P n).pop) μ Z)
    (sub : ℕ → ℕ) (hsub : StrictMono sub),
  ∀ᵐ ω ∂μ,
    (∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N).pop (late (P N).pop) (Z N ω)
      probability (P N).pop (fun S => |adjustedTau (P N) q S - oracleStar (P N) q S| ≥
        κ * Real.sqrt (designVariance (P N).pop (oracleStar (P N) q)))) atTop (nhds 0)) ∧
    (∀ x : ℝ, 0 < x → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N).pop (late (P N).pop) (Z N ω)
      |probability (P N).pop (fun S => |oracleStar (P N) q S| ≥
        x * Real.sqrt (designVariance (P N).pop (oracleStar (P N) q))) - normalTail x|)
      atTop (nhds 0)) ∧
    (∀ x : ℝ, 0 < x → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N).pop (late (P N).pop) (Z N ω)
      |probability (P N).pop (fun S => |adjustedTau (P N) q S| ≥
        x * Real.sqrt (designVariance (P N).pop (oracleStar (P N) q))) - normalTail x|)
      atTop (nhds 0)) ∧
    (∀ κ : ℝ, 0 < κ → Tendsto (fun j =>
      let N := sub j
      let q := observedW (P N).pop (late (P N).pop) (Z N ω)
      probability (P N).pop (fun S => |adjustedSigma2 (P N) q S /
        designVariance (P N).pop (oracleStar (P N) q) - 1| ≥ κ)) atTop (nhds 0))

end
end SAP.P002a
