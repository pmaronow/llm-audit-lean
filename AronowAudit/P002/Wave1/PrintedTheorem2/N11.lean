import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Finite counting calculus, including empty assignment sets in all but the complement law. -/
theorem n11_proof : N11 := by
  intro n P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro E
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · by_cases hcard : (assignments P).card = 0
      · simp [probability, hcard]
      · unfold probability
        apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hcard)).2
        exact_mod_cast Finset.card_filter_le (assignments P) E
  · intro E F hEF
    have hsub : (assignments P).filter E ⊆ (assignments P).filter F := by
      intro S hS
      obtain ⟨hS, hE⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨hS, hEF S hS hE⟩
    unfold probability
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Finset.card_le_card hsub
  · intro E F
    have hcard :
        (((assignments P).filter E ∪ (assignments P).filter F).card : ℝ) ≤
          (((assignments P).filter E).card : ℝ) +
            (((assignments P).filter F).card : ℝ) := by
      exact_mod_cast Finset.card_union_le ((assignments P).filter E) ((assignments P).filter F)
    unfold probability
    rw [Finset.filter_congr_decidable _ _ _, Finset.filter_or, ← add_div]
    exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
  · intro hdesign E
    have hnonempty : (assignments P).Nonempty := by
      apply Finset.powersetCard_nonempty.mpr
      simpa using Nat.le_of_lt hdesign.2.2
    have hdenom : ((assignments P).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hnonempty
    have hpartition :
        (((assignments P).filter E).card : ℝ) +
          (((assignments P).filter (fun S => ¬ E S)).card : ℝ) =
            ((assignments P).card : ℝ) := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := assignments P) E
    unfold probability
    apply (eq_sub_iff_add_eq).2
    rw [← add_div]
    have hnum :
        (((assignments P).filter (fun S => ¬ E S)).card : ℝ) +
          (((assignments P).filter E).card : ℝ) = ((assignments P).card : ℝ) := by
      linarith
    rw [Finset.filter_congr_decidable _ _ _, hnum, div_self hdenom]
  · intro f c hc hf
    have hsum :
        (((assignments P).filter (fun S => c ≤ f S)).card : ℝ) * c ≤
          ∑ S ∈ assignments P, f S := by
      calc
        _ = ∑ S ∈ assignments P, if c ≤ f S then c else 0 := by
          rw [← Finset.sum_filter]
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro S hS
          by_cases h : c ≤ f S
          · simpa only [if_pos h] using h
          · simpa only [if_neg h] using hf S hS
    apply (le_div_iff₀ hc).2
    unfold probability expectation
    calc
      _ = ((((assignments P).filter (fun S => c ≤ f S)).card : ℝ) * c) /
          ((assignments P).card : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end
end AronowAudit.P002.Wave1.PrintedTheorem2
