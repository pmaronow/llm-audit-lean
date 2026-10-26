import AronowAudit.P018.Wave1.WeightedConsistency.G6
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem g7_proof : G7.{u} := by
  intro k G₀ hG₀
  have hc : ContinuousAt (fun A : Mat k => A⁻¹) G₀ := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hG₀
  constructor
  · intro G hG
    exact hc.tendsto.comp hG
  · intro Ω _ μ _ G hG
    exact inProbability_continuousAt μ hc hG

end
end AronowAudit.P018.Wave1.WeightedConsistency
