import AronowAudit.P013.P013_Audit

/-!
P013-T6: the corrected directed Condition 5 implies Condition 4.
The bound on outgoing rows is uniform over the population sequence.
-/

namespace AronowAudit.P013.Wave1

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset

noncomputable section

/-- Corrected Condition 5 with a uniform row bound and directed indicators. -/
def Condition5CorrectedDirected (S : AronowAudit.P013.ExperimentSequence) : Prop :=
  ∃ m : ℕ, ∃ h : ∀ n : ℕ, Fin (n + 1) → Fin (n + 1) → Bool,
    ∀ n : ℕ,
      AronowAudit.P013.GenuineDependency
        (AronowAudit.P013.seqLaw S n)
        (AronowAudit.P013.seqPopulation S n).exposure (h n) ∧
      AronowAudit.P013.RowBound (h n) m

/-- The corrected directed Condition 5 implies Condition 4 (P013-T6(c)). -/
theorem directed_condition5_implies_condition4
    (S : AronowAudit.P013.ExperimentSequence)
    (hc5 : AronowAudit.P013.Wave1.Condition5CorrectedDirected S) :
    AronowAudit.P013.Condition4 S := by
  classical
  obtain ⟨m, h, hb⟩ := hc5
  let g : ∀ n : ℕ, Fin (n + 1) → Fin (n + 1) → Bool :=
    fun n i j => decide (i = j ∨ h n i j = true ∨ h n j i = true)
  refine ⟨g, ?_, ?_⟩
  · intro n i j hx
    have hn : i ≠ j ∧ h n i j = false ∧ h n j i = false := by
      simpa [g] using hx
    exact genuine_implies_pair_independent (seqPopulation S n) (h n)
      (hb n).1 i j hn.1 hn.2.1 hn.2.2
  · apply linear_count_is_little_o _ (2 * m + 1 : ℝ) (by positivity)
    intro n
    constructor
    · apply sum_nonneg
      intro i _
      apply sum_nonneg
      intro j _
      split_ifs <;> norm_num
    · have hcount := graph_pair_count (h n) m (hb n).2
      have heq : (∑ i, ∑ j, (if g n i j = true then 1 else 0 : ℝ)) =
          ((∑ i, ∑ j, graphPairIndicator (h n) i j : ℕ) : ℝ) := by
        simp [g, graphPairIndicator]
      rw [heq]
      exact_mod_cast hcount

end

end AronowAudit.P013.Wave1
