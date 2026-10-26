import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- Indicator inequalities give the finite-design event calculus. -/
theorem n7_proof : N7 := by
  classical
  intro Q
  have hMN : Q.M ≤ Fintype.card (Fin Q.N) := by
    simpa only [Fintype.card_fin] using (population_sizes Q).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E
    unfold eventProbability
    exact expectation_nonneg Q.M _ (fun s _ => by split_ifs <;> norm_num)
  · intro E F hEF
    unfold eventProbability
    apply expectation_mono
    intro s hs
    by_cases hE : E s
    · have hF : F s := hEF s hs hE
      simp only [if_pos hE, if_pos hF, le_refl]
    · simp only [if_neg hE]
      split_ifs <;> norm_num
  · intro E F
    unfold eventProbability
    rw [← expectation_add]
    apply expectation_mono
    intro s _
    by_cases hE : E s <;> by_cases hF : F s <;> norm_num [hE, hF]
  · intro E
    unfold eventProbability
    calc
      _ = expectation Q.M (fun s => (1 : ℝ) - (if E s then 1 else 0)) := by
        apply expectation_congr
        intro s _
        by_cases hE : E s <;> norm_num [hE]
      _ = _ := by rw [expectation_sub, expectation_const Q.M hMN]

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
