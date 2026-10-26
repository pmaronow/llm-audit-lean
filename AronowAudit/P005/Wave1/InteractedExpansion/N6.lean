import AronowAudit.P005.Wave1.InteractedExpansion.N2

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- The cardinalities used by N6, N9 and N10. -/
theorem balanced_cards (n : ℕ) (hn : 6 ≤ n) (S : Finset (Fin n))
    (hS : S ∈ design n (n / 2)) : 2 ≤ S.card ∧ 2 ≤ (control S).card := by
  have hs : S.card = n / 2 := (Finset.mem_powersetCard.mp hS).2
  have hc : (control S).card = n - S.card := by
    simp [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  constructor <;> omega

theorem n6_proof : N6 := by
  intro h1 h4 h5 n hn S hS
  have hcard := balanced_cards n hn S hS
  have hs : Real.sqrt (spikeQ n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (spikeQ_pos_of_S1 h1 n (by omega)))
  have hx : ∀ i k, (spikePopulation n).x i k =
      (spikeA n i - 1 / (n : ℝ)) / Real.sqrt (spikeQ n) := fun _ _ => rfl
  exact ⟨(h4 n (spikePopulation n) (spikeA n) (1 / (n : ℝ)) _ hs hx S
      (spikeV n) (ne_of_gt (h5 n hn S hcard.1))).1,
    (h4 n (spikePopulation n) (spikeA n) (1 / (n : ℝ)) _ hs hx (control S)
      (spikeV n) (ne_of_gt (h5 n hn (control S) hcard.2))).1⟩

end
end AronowAudit.P005.Wave1.InteractedExpansion
