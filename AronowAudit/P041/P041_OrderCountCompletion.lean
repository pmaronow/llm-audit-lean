import AronowAudit.P041.P041_Order
import AronowAudit.P041.P041_OrderCounting

noncomputable section
namespace AronowAudit.P041

/-- The actual balanced sequence count, for every m≥1, expressed as a
binomial coefficient without assuming a distribution formula. -/
theorem leading_cited_count_exact {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m) :
    ((balancedSequences m).filter (fun z => leadingCited z = k)).card =
      (2*m-k-1).choose (m-1) := by
  classical
  have hL (z : Finset (Fin (2*m))) : leadingCited z = OrderCompletion.leadingRun z := by
    unfold leadingCited OrderCompletion.leadingRun
    congr 1 <;> ext r <;> simp
  unfold balancedSequences
  simp_rw [hL]
  exact OrderCompletion.balanced_leading_count hm hk

/-- Exact probability in the uniform balanced-subset law. -/
theorem leading_cited_probability_exact {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m) :
    leadingCitedProbability m k =
      (((2*m-k-1).choose (m-1) : ℝ) / ((2*m).choose m : ℝ)) := by
  unfold leadingCitedProbability
  rw [leading_cited_count_exact hm hk,(balanced_sequence_card m).1]

end AronowAudit.P041

