import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Bracket the moving threshold by two fixed thresholds, use
pointwise convergence along the subsequence there, and absorb the comparison
error. All four errors are bounded explicitly by one quarter of the target
tolerance. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n9_proof : N9 := by
  intro F G Φ φ c ε x hmono hΦ hG hφ hc hε herror
  have hthreshold : Tendsto (fun n => c n * x) atTop (nhds x) := by
    simpa only [one_mul] using hc.mul_const x
  apply Metric.tendsto_nhds.2
  intro η hη
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨δ, hδ, hcont⟩ := (Metric.continuousAt_iff.mp hΦ) (η / 4) hη4
  have hδ2 : 0 < δ / 2 := by positivity
  have hleft_dist : dist (x - δ / 2) x < δ := by
    rw [Real.dist_eq, show (x - δ / 2) - x = -(δ / 2) by ring,
      abs_neg, abs_of_pos hδ2]
    linarith
  have hright_dist : dist (x + δ / 2) x < δ := by
    rw [Real.dist_eq, show (x + δ / 2) - x = δ / 2 by ring,
      abs_of_pos hδ2]
    linarith
  have hleft_cont : |Φ (x - δ / 2) - Φ x| < η / 4 := by
    simpa only [Real.dist_eq] using hcont hleft_dist
  have hright_cont : |Φ (x + δ / 2) - Φ x| < η / 4 := by
    simpa only [Real.dist_eq] using hcont hright_dist
  have hleft_limit : Tendsto (fun n => G (φ n) (x - δ / 2)) atTop
      (nhds (Φ (x - δ / 2))) := (hG (x - δ / 2)).comp hφ
  have hright_limit : Tendsto (fun n => G (φ n) (x + δ / 2)) atTop
      (nhds (Φ (x + δ / 2))) := (hG (x + δ / 2)).comp hφ
  have hleft_event : ∀ᶠ n in atTop,
      dist (G (φ n) (x - δ / 2)) (Φ (x - δ / 2)) < η / 4 :=
    (Metric.tendsto_nhds.1 hleft_limit) (η / 4) hη4
  have hright_event : ∀ᶠ n in atTop,
      dist (G (φ n) (x + δ / 2)) (Φ (x + δ / 2)) < η / 4 :=
    (Metric.tendsto_nhds.1 hright_limit) (η / 4) hη4
  have hthreshold_event : ∀ᶠ n in atTop, dist (c n * x) x < δ / 2 :=
    (Metric.tendsto_nhds.1 hthreshold) (δ / 2) hδ2
  have herror_event : ∀ᶠ n in atTop, dist (ε n) 0 < η / 4 :=
    (Metric.tendsto_nhds.1 hε) (η / 4) hη4
  filter_upwards [hleft_event, hright_event, hthreshold_event, herror_event]
    with n hnleft hnright hnthreshold hnerror
  rw [Real.dist_eq] at hnleft hnright hnthreshold
  have hεn : ε n < η / 4 := by
    have habs : |ε n| < η / 4 := by
      simpa only [Real.dist_eq, sub_zero] using hnerror
    exact (abs_lt.mp habs).2
  rcases abs_lt.mp hnthreshold with ⟨hthreshold_lower, hthreshold_upper⟩
  have hbelow : G (φ n) (x - δ / 2) ≤ G (φ n) (c n * x) :=
    hmono (φ n) (by linarith)
  have habove : G (φ n) (c n * x) ≤ G (φ n) (x + δ / 2) :=
    hmono (φ n) (by linarith)
  rcases abs_le.mp (herror n) with ⟨hFn_lower, hFn_upper⟩
  rcases abs_lt.mp hnleft with ⟨hleft_lower, hleft_upper⟩
  rcases abs_lt.mp hnright with ⟨hright_lower, hright_upper⟩
  rcases abs_lt.mp hleft_cont with ⟨hleft_cont_lower, hleft_cont_upper⟩
  rcases abs_lt.mp hright_cont with ⟨hright_cont_lower, hright_cont_upper⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
