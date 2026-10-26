import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint

/-!
Compare the two-draw design with uniform draws with replacement.
The only error is the diagonal, whose mass is `1 / N`.
-/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem n4_pair_eq {α : Type*} [DecidableEq α] {s : Finset α}
    (hs : s.card = 2) {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ({i, j} : Finset α) = s := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · simpa only [ha] using hi
    · simpa only [Finset.mem_singleton.mp ha] using hj
  · simpa only [hs, Finset.card_pair hij] using (le_refl (2 : ℕ))

/-- Every successful unordered pair has exactly two ordered preimages. -/
private theorem n4_ordered_count {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) (hR : ∀ i j, R i j → R j i) :
    (Finset.univ.filter (fun ij : α × α => ij.1 ≠ ij.2 ∧ R ij.1 ij.2)).card =
      2 * (((Finset.univ : Finset α).powersetCard 2).filter
        (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ R i j)).card := by
  let A := ((Finset.univ : Finset α).powersetCard 2).filter
    (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ R i j)
  let B := Finset.univ.filter (fun ij : α × α => ij.1 ≠ ij.2 ∧ R ij.1 ij.2)
  have hmap : ∀ ij ∈ B, ({ij.1, ij.2} : Finset α) ∈ A := by
    intro ij hij
    have hp : ij.1 ≠ ij.2 ∧ R ij.1 ij.2 := (Finset.mem_filter.mp hij).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hp.1⟩, ?_⟩
    exact ⟨ij.1, by simp, ij.2, by simp, hp.1, hp.2⟩

  have hfiber (s : Finset α) (hs : s ∈ A) :
      (B.filter (fun ij => ({ij.1, ij.2} : Finset α) = s)).card = 2 := by
    have hs2 : s.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
    obtain ⟨a, ha, b, hb, hab, hRab⟩ := (Finset.mem_filter.mp hs).2
    have habs : ({a, b} : Finset α) = s := n4_pair_eq hs2 ha hb hab
    have hrel (i j : α) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) : R i j := by
      have hi' : i = a ∨ i = b := by simpa only [← habs, Finset.mem_insert,
        Finset.mem_singleton] using hi
      have hj' : j = a ∨ j = b := by simpa only [← habs, Finset.mem_insert,
        Finset.mem_singleton] using hj
      rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
      · exact (hij (hi'.trans hj'.symm)).elim
      · simpa only [hi', hj'] using hRab
      · simpa only [hi', hj'] using hR a b hRab
      · exact (hij (hi'.trans hj'.symm)).elim
    have heq : B.filter (fun ij => ({ij.1, ij.2} : Finset α) = s) = s.offDiag := by
      ext ij
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
      constructor
      · rintro ⟨⟨hne, _⟩, hp⟩
        rw [← hp]
        exact ⟨by simp, by simp, hne⟩
      · rintro ⟨hi, hj, hij⟩
        exact ⟨⟨hij, hrel _ _ hi hj hij⟩, n4_pair_eq hs2 hi hj hij⟩
    rw [heq, Finset.offDiag_card, hs2]

  change B.card = 2 * A.card
  calc
    B.card = ∑ s ∈ A, (B.filter (fun ij => ({ij.1, ij.2} : Finset α) = s)).card :=
      Finset.card_eq_sum_card_fiberwise
        (f := fun ij : α × α => ({ij.1, ij.2} : Finset α)) (s := B) (t := A) hmap
    _ = ∑ _s ∈ A, 2 := Finset.sum_congr rfl hfiber
    _ = 2 * A.card := by simp [Nat.mul_comm]

theorem n4_proof : N4 := by
  intro Q R hM hR
  let U : Finset (Finset (Fin Q.N)) := Finset.univ.powersetCard 2
  let E : Finset (Fin Q.N) → Prop :=
    fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ R i j
  let A := U.filter E
  let B := Finset.univ.filter
    (fun ij : Fin Q.N × Fin Q.N => ij.1 ≠ ij.2 ∧ R ij.1 ij.2)
  let D := Finset.univ.filter
    (fun ij : Fin Q.N × Fin Q.N => ij.1 = ij.2 ∧ R ij.1 ij.2)
  let T := Finset.univ.filter (fun ij : Fin Q.N × Fin Q.N => R ij.1 ij.2)
  have hBA : B.card = 2 * A.card := by
    dsimp only [B, A, U, E]
    convert n4_ordered_count R hR using 1 <;> congr

  have hAll : (Finset.univ : Finset (Fin Q.N)).offDiag.card = 2 * U.card := by
    have h := n4_ordered_count (fun _ _ : Fin Q.N => True) (by intros; trivial)
    convert h using 1
    · congr 1
      ext ij
      simp [Finset.mem_offDiag]
    · congr 1
      apply congrArg Finset.card
      ext s
      simp only [Finset.mem_filter]
      constructor
      · intro hs
        have hs2 : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
        obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs2
        exact ⟨hs, i, by simp, j, by simp, hij, trivial⟩
      · exact And.left

  have hsplit : B.card + D.card = T.card := by
    have h := Finset.card_filter_add_card_filter_not (s := T)
      (fun ij : Fin Q.N × Fin Q.N => ij.1 ≠ ij.2)
    simpa only [T, B, D, Finset.filter_filter, not_not, and_comm] using h
  have hBsub : B ⊆ (Finset.univ : Finset (Fin Q.N)).offDiag := by
    intro ij hij
    exact Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, (Finset.mem_filter.mp hij).2.1⟩
  have hDsub : D ⊆ (Finset.univ : Finset (Fin Q.N)).diag := by
    intro ij hij
    exact Finset.mem_diag.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hij).2.1⟩
  have hDle : D.card ≤ Q.N := by
    calc
      D.card ≤ (Finset.univ : Finset (Fin Q.N)).diag.card := Finset.card_le_card hDsub
      _ = Q.N := by simp
  have hBle : B.card ≤ 2 * U.card := by
    rw [← hAll]
    exact Finset.card_le_card hBsub

  have hN4nat : 4 ≤ Q.N := (population_sizes Q).2.2.2
  have hN4 : (4 : ℝ) ≤ (Q.N : ℝ) := by exact_mod_cast hN4nat
  have hNpos : 0 < (Q.N : ℝ) := by linarith
  have hN1pos : 0 < (Q.N : ℝ) - 1 := by linarith
  have hN : (Q.N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hN1 : (Q.N : ℝ) - 1 ≠ 0 := ne_of_gt hN1pos
  have hden : 0 < (Q.N : ℝ) * ((Q.N : ℝ) - 1) := mul_pos hNpos hN1pos
  have hNN : Q.N ≤ Q.N * Q.N := by
    calc
      Q.N = Q.N * 1 := by simp
      _ ≤ Q.N * Q.N := Nat.mul_le_mul_left Q.N (by omega)
  have hUcard : 2 * (U.card : ℝ) = (Q.N : ℝ) * ((Q.N : ℝ) - 1) := by
    calc
      2 * (U.card : ℝ) =
          (((Finset.univ : Finset (Fin Q.N)).offDiag).card : ℝ) := by
        exact_mod_cast hAll.symm
      _ = (Q.N : ℝ) * ((Q.N : ℝ) - 1) := by
        rw [Finset.offDiag_card]
        simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_sub hNN, Nat.cast_mul]
        ring
  have hUpos : 0 < (U.card : ℝ) := by nlinarith [hUcard]
  have hBAR : (B.card : ℝ) = 2 * (A.card : ℝ) := by exact_mod_cast hBA
  have hsplitR : (B.card : ℝ) + (D.card : ℝ) = (T.card : ℝ) := by exact_mod_cast hsplit
  have hBbound : (B.card : ℝ) ≤ (Q.N : ℝ) * ((Q.N : ℝ) - 1) := by
    calc
      (B.card : ℝ) ≤ 2 * (U.card : ℝ) := by exact_mod_cast hBle
      _ = (Q.N : ℝ) * ((Q.N : ℝ) - 1) := hUcard
  have hDbound : (D.card : ℝ) ≤ (Q.N : ℝ) := by exact_mod_cast hDle

  have hpCount : eventProbability Q E = (A.card : ℝ) / (U.card : ℝ) := by
    unfold eventProbability expectation
    rw [hM]
    simp only [U, A, Finset.sum_boole]
    congr
  have hp : eventProbability Q E =
      (B.card : ℝ) / ((Q.N : ℝ) * ((Q.N : ℝ) - 1)) := by
    rw [hpCount]
    apply (div_eq_div_iff (ne_of_gt hUpos) (ne_of_gt hden)).mpr
    rw [← hUcard, hBAR]
    ring
  have hp0 : 0 ≤ eventProbability Q E := by rw [hp]; positivity
  have hp1 : eventProbability Q E ≤ 1 := by
    rw [hp]
    exact (div_le_one hden).mpr hBbound

  have hmix : (T.card : ℝ) / (Q.N : ℝ) ^ 2 =
      (1 - 1 / (Q.N : ℝ)) * eventProbability Q E +
        (D.card : ℝ) / (Q.N : ℝ) ^ 2 := by
    rw [hp, ← hsplitR]
    field_simp [hN, hN1] <;> ring
  have hdiff : eventProbability Q E - (T.card : ℝ) / (Q.N : ℝ) ^ 2 =
      eventProbability Q E / (Q.N : ℝ) - (D.card : ℝ) / (Q.N : ℝ) ^ 2 := by
    rw [hmix]
    ring
  have hpdiv0 : 0 ≤ eventProbability Q E / (Q.N : ℝ) := div_nonneg hp0 hNpos.le
  have hpdiv1 : eventProbability Q E / (Q.N : ℝ) ≤ 1 / (Q.N : ℝ) :=
    div_le_div_of_nonneg_right hp1 hNpos.le
  have hddiv0 : 0 ≤ (D.card : ℝ) / (Q.N : ℝ) ^ 2 := by positivity
  have hddiv1 : (D.card : ℝ) / (Q.N : ℝ) ^ 2 ≤ 1 / (Q.N : ℝ) := by
    calc
      (D.card : ℝ) / (Q.N : ℝ) ^ 2 ≤ (Q.N : ℝ) / (Q.N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hDbound (sq_nonneg _)
      _ = 1 / (Q.N : ℝ) := by field_simp [hN] <;> ring
  change |eventProbability Q E - (T.card : ℝ) / (Q.N : ℝ) ^ 2| ≤ 1 / (Q.N : ℝ)
  rw [hdiff]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
