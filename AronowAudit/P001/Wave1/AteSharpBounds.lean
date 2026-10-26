import AronowAudit.P001.Wave1.AteSharpBoundsBlueprint
import AronowAudit.P001.Wave1.AteSharpBounds.N1
import AronowAudit.P001.Wave1.AteSharpBounds.N2
import AronowAudit.P001.Wave1.AteSharpBounds.N3

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem ate_sharp_paper_bounds_same_observable_law :
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D → ∀ (a b : ℝ),
    (∀ᵐ ω ∂μ, Y0 ω ∈ Set.Icc a b ∧ Y1 ω ∈ Set.Icc a b) →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} →
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    let L := conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + a * prob μ {ω | D ω = 0} -
      (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + b * prob μ {ω | D ω = 1})
    let U := conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + b * prob μ {ω | D ω = 0} -
      (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + a * prob μ {ω | D ω = 1})
    mean μ (fun ω => Y1 ω - Y0 ω) ∈ Set.Icc L U ∧ U - L = b - a ∧
    ∀ c ∈ Set.Icc L U, ∃ Z0 Z1 : Ω → ℝ,
      Measurable Z0 ∧ Measurable Z1 ∧
      (∀ᵐ ω ∂μ, Z0 ω ∈ Set.Icc a b ∧ Z1 ω ∈ Set.Icc a b) ∧
      μ.map (fun ω => (observedOutcome (Z0 ω) (Z1 ω) (D ω), D ω)) =
        μ.map (fun ω => (Y ω, D ω)) ∧
      mean μ (fun ω => Z1 ω - Z0 ω) = c :=
  AteSharpBounds.assemble AteSharpBounds.n1_proof AteSharpBounds.n2_proof AteSharpBounds.n3_proof

end

end AronowAudit.P001.Wave1
