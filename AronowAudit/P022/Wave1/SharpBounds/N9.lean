import AronowAudit.P022.Wave1.SharpBoundsBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

private theorem indicator_mean {N : ℕ} (p : Fin N → Prop) [DecidablePred p] :
    finiteMean (fun i => if p i then (1 : ℝ) else 0) =
      ((univ.filter p).card : ℝ) / N := by
  simp [finiteMean, Fintype.expect_eq_sum_div_card]

theorem n9_proof : N9 := by
  intro N s1 s0 h1 h0 c e
  classical
  by_cases hN : N = 0
  · subst N
    simp [finiteMean, Fintype.expect_eq_sum_div_card]
  have hNR : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  let A : Finset (Fin N) := univ.filter (fun i => c ≤ s1 i)
  let B : Finset (Fin N) := univ.filter (fun i => e ≤ s0 i)
  let R : Finset (Fin N) := univ.filter (fun i => e ≤ s0 i.rev)
  have hA (i : Fin N) : i ∈ A ↔ c ≤ s1 i := by simp [A]
  have hB (i : Fin N) : i ∈ B ↔ e ≤ s0 i := by simp [B]
  have hR (i : Fin N) : i ∈ R ↔ e ≤ s0 i.rev := by simp [R]
  have hpair : (univ.filter (fun i => c ≤ s1 i ∧ e ≤ s0 i)) = A ∩ B := by ext i; simp [A, B]
  have hrev : (univ.filter (fun i => c ≤ s1 i ∧ e ≤ s0 i.rev)) = A ∩ R := by ext i; simp [A, R]
  have hcardR : R.card = B.card := by
    apply Finset.card_bij (fun i _ => i.rev)
    · intro i hi
      exact (hB _).2 ((hR _).1 hi)
    · intro i _ j _ hij
      exact Fin.rev_injective hij
    · intro i hi
      refine ⟨i.rev, (hR _).2 (by simpa using (hB _).1 hi), by simp⟩
  constructor
  · simp only [indicator_mean, hpair]
    change ((A ∩ B).card : ℝ) / N = min ((A.card : ℝ) / N) ((B.card : ℝ) / N)
    have hnested : A ⊆ B ∨ B ⊆ A := by
      by_cases hab : A ⊆ B
      · exact Or.inl hab
      · right
        obtain ⟨i, hiA, hiB⟩ := Finset.not_subset.mp hab
        intro j hj
        apply (hA j).2
        have hij : i ≤ j := by
          by_contra hn
          have := (hB j).1 hj |>.trans (h0 (le_of_lt (lt_of_not_ge hn)))
          exact hiB ((hB i).2 this)
        exact ((hA i).1 hiA).trans (h1 hij)
    rcases hnested with hab | hba
    · rw [Finset.inter_eq_left.mpr hab, min_eq_left]
      exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hab) hNR.le
    · rw [Finset.inter_eq_right.mpr hba, min_eq_right]
      exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hba) hNR.le
  · simp only [indicator_mean, hrev]
    change ((A ∩ R).card : ℝ) / N = max 0 ((A.card : ℝ) / N + (B.card : ℝ) / N - 1)
    have hcount := Finset.card_union_add_card_inter A R
    have hcountR : ((A ∪ R).card : ℝ) + ((A ∩ R).card : ℝ) = (A.card : ℝ) + B.card := by
      exact_mod_cast (hcardR ▸ hcount)
    by_cases hi : (A ∩ R).Nonempty
    · obtain ⟨i, hi⟩ := hi
      have hall : A ∪ R = univ := by
        apply Finset.eq_univ_of_forall
        intro j
        rcases le_total i j with hij | hji
        · exact mem_union_left _ ((hA _).2 (((hA _).1 (mem_inter.mp hi).1).trans (h1 hij)))
        · apply mem_union_right
          apply (hR _).2
          exact ((hR _).1 (mem_inter.mp hi).2).trans (h0 (Fin.rev_le_rev.mpr hji))
      rw [hall, Finset.card_univ, Fintype.card_fin] at hcountR
      have heq : ((A.card : ℝ) / N + (B.card : ℝ) / N - 1) = ((A ∩ R).card : ℝ) / N := by
        field_simp
        nlinarith
      rw [heq, max_eq_right (by positivity)]
    · have hempty : A ∩ R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
      rw [hempty, card_empty, Nat.cast_zero, add_zero] at hcountR
      have hle : ((A ∪ R).card : ℝ) ≤ N := by
        exact_mod_cast (show (A ∪ R).card ≤ N by simpa only [Fintype.card_fin] using Finset.card_le_univ (A ∪ R))
      rw [hempty, card_empty, Nat.cast_zero, zero_div, max_eq_left]
      apply (sub_nonpos.mpr _)
      rw [← add_div]
      apply (div_le_iff₀ hNR).2
      linarith

end
end AronowAudit.P022.Wave1.SharpBounds
