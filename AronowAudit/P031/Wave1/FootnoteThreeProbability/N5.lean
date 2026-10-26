import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- Expand the OLS residual SSE separately in the two realized arms. -/
theorem n5_proof : N5 := by
  classical
  intro Q s hs
  have ha : Admissible s := population_assignment_admissible Q s hs
  have hc : s.card = Q.M := (Finset.mem_powersetCard.mp hs).2
  have hMN : Q.M ≤ Q.N := (population_sizes Q).2.2.1
  have hcc : (sᶜ.card : ℝ) = (Q.N : ℝ) - Q.M := by
    rw [Finset.card_compl, hc, Fintype.card_fin, Nat.cast_sub hMN]
  have hg : gramInverse s 1 1 = 1 / (s.card : ℝ) + 1 / (sᶜ.card : ℝ) := by
    simp [gramInverse]
  unfold olsEstimator ols
  rw [residual_sse s (observed s Q.y1 Q.y0) ha,
    sample_variance_congr s (fun i hi => observed_treatment s Q.y1 Q.y0 hi),
    sample_variance_congr sᶜ (fun i hi => observed_control s Q.y1 Q.y0 hi)]
  rw [hg]
  simp only [hc, hcc,
    Fintype.card_fin, olsWeightT, olsWeightC]
  ring

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
