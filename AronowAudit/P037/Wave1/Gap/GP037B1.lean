import AronowAudit.P037.P037_Sample
import AronowAudit.P037.P037_FiniteDesign
import Mathlib.Data.Fintype.Fin

namespace AronowAudit.P037.Wave1
open scoped BigOperators
open Filter
set_option autoImplicit false

noncomputable def selection_centered (z : Fin 6) : ℝ :=
  selectedWeight z * (selectedDelta z - 3/250)

theorem selection_weight_lower (z : Fin 6) : (2/3:ℝ) ≤ selectedWeight z := by
  rw [outcome_selection_finite_counterexample.2.2.2.2.1]
  fin_cases z <;> norm_num

theorem selection_centered_mean : designMean oneBlockDesign selection_centered = 0 := by
  unfold designMean oneBlockDesign selection_centered
  simp_rw [outcome_selection_finite_counterexample.2.2.2.1,
    outcome_selection_finite_counterexample.2.2.2.2.1]
  norm_num [Fin.sum_univ_succ]

theorem selection_ratio_bound (B : ℕ) (hB : 0 < B) (z : Fin B → Fin 6) :
    |selectedBlockCoefficient B z - 3/250| ≤
      (3/2:ℝ) * |(∑ b, selection_centered (z b))/(B:ℝ)| := by
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hw : (2/3:ℝ)*(B:ℝ) ≤ ∑ b, selectedWeight (z b) := by
    calc
      _ = ∑ _b : Fin B, (2/3:ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun b _ => selection_weight_lower (z b))
  have hwpos : 0 < ∑ b, selectedWeight (z b) := lt_of_lt_of_le (by positivity) hw
  have hid : selectedBlockCoefficient B z - 3/250 =
      (∑ b, selection_centered (z b))/(∑ b, selectedWeight (z b)) := by
    unfold selectedBlockCoefficient selection_centered
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    field_simp
  rw [hid, abs_div, abs_of_pos hwpos, abs_div, abs_of_pos hBr]
  calc
    _ ≤ |∑ b, selection_centered (z b)| / ((2/3:ℝ)*(B:ℝ)) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hw
    _ = _ := by ring

theorem outcome_selection_regression_limit_proof (ε : ℝ) (hε : 0<ε) :
    Filter.Tendsto (fun B : ℕ =>
      ∑ z : Fin B → Fin 6, (1/6:ℝ)^B *
        (if |selectedBlockCoefficient B z-3/250| > ε then 1 else 0))
      Filter.atTop (nhds 0) := by
  classical
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hlln := WitnessCompletion.iid_average_consistent oneBlockDesign
    selection_centered (2*ε/3) (by positivity)
  rw [selection_centered_mean] at hlln
  simp only [sub_zero] at hlln
  have hmass (n : ℕ) (z : Fin (n+1) → Fin 6) :
      (productDesign (fun _ : Fin (n+1) => oneBlockDesign)).weight z =
        (1/6:ℝ)^(n+1) := by simp [productDesign, oneBlockDesign]
  refine squeeze_zero (fun n => Finset.sum_nonneg (fun z _ =>
    mul_nonneg (by positivity) (by split_ifs <;> norm_num))) (fun n => ?_) hlln
  change _ ≤ ∑ z, (productDesign (fun _ : Fin (n+1) => oneBlockDesign)).weight z * _
  apply Finset.sum_le_sum
  intro z _
  rw [hmass]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  split_ifs with h h'
  · norm_num
  · exfalso
    have hb := selection_ratio_bound (n+1) (by omega) z
    have h' := le_of_not_gt h'
    have : |(∑ b, selection_centered (z b))/(↑(n+1):ℝ)| ≤ 2*ε/3 := by
      simpa only [Nat.cast_add, Nat.cast_one] using h'
    linarith
  · norm_num
  · norm_num

noncomputable def cutoff_draw (j : Fin 10000) : Bool × Finset (Fin 12) :=
  if j.val < 5000 then (false, {0,1,2,3,4,5})
  else if j.val < 5005 then (true, {6,7,8,9,10,11})
  else if j.val < 7500 then (true, {1,6,7,8,9,10})
  else (true, {0,6,7,8,9,10})

theorem cutoff_draw_label (j : Fin 10000) :
    (if (cutoff_draw j).1 then treatedSeedExposure ∅ {0,1,2,3,4,5} {0}
      (cutoff_draw j).2 else 0) =
    (if j.val < 5000 then 0 else if j.val < 5005 then 1
      else if j.val < 7500 then 2 else 3 : Fin 5) := by
  unfold cutoff_draw
  split_ifs <;> norm_num [treatedSeedExposure, Finset.disjoint_insert_right] at *

theorem cutoff_interval_card (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 10000) :
    (Finset.univ.filter (fun j : Fin 10000 => a ≤ j.val ∧ j.val < b)).card = b-a := by
  classical
  have he : Finset.univ.filter (fun j : Fin 10000 => a ≤ j.val ∧ j.val < b) =
      (Finset.univ.filter (fun j : Fin 10000 => j.val < b)) \
        (Finset.univ.filter (fun j : Fin 10000 => j.val < a)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  rw [he, Finset.card_sdiff_of_subset]
  · rw [Fin.card_filter_val_lt, Fin.card_filter_val_lt,
      Nat.min_eq_right hb, Nat.min_eq_right (hab.trans hb)]
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    omega

theorem cutoff_histogram (k : Fin 4) :
    (Finset.univ.filter (fun j =>
      (if (cutoff_draw j).1 then treatedSeedExposure ∅ {0,1,2,3,4,5} {0}
        (cutoff_draw j).2 else 0) = k.castSucc)).card =
      (![5000,5,2495,2500] : Fin 4 → ℕ) k := by
  classical
  simp_rw [cutoff_draw_label]
  fin_cases k
  · have he : (Finset.univ.filter (fun j : Fin 10000 =>
        (if j.val < 5000 then 0 else if j.val < 5005 then 1
          else if j.val < 7500 then 2 else 3 : Fin 5) = 0)) =
        Finset.univ.filter (fun j => 0 ≤ j.val ∧ j.val < 5000) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> norm_num <;> omega
    change (Finset.univ.filter (fun j : Fin 10000 =>
      (if j.val < 5000 then 0 else if j.val < 5005 then 1
        else if j.val < 7500 then 2 else 3 : Fin 5) = 0)).card = 5000
    rw [he, cutoff_interval_card 0 5000 (by omega) (by omega)]
  · have he : (Finset.univ.filter (fun j : Fin 10000 =>
        (if j.val < 5000 then 0 else if j.val < 5005 then 1
          else if j.val < 7500 then 2 else 3 : Fin 5) = 1)) =
        Finset.univ.filter (fun j => 5000 ≤ j.val ∧ j.val < 5005) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> norm_num <;> omega
    change (Finset.univ.filter (fun j : Fin 10000 =>
      (if j.val < 5000 then 0 else if j.val < 5005 then 1
        else if j.val < 7500 then 2 else 3 : Fin 5) = 1)).card = 5
    rw [he, cutoff_interval_card 5000 5005 (by omega) (by omega)]
  · have he : (Finset.univ.filter (fun j : Fin 10000 =>
        (if j.val < 5000 then 0 else if j.val < 5005 then 1
          else if j.val < 7500 then 2 else 3 : Fin 5) = 2)) =
        Finset.univ.filter (fun j => 5005 ≤ j.val ∧ j.val < 7500) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> norm_num <;> omega
    change (Finset.univ.filter (fun j : Fin 10000 =>
      (if j.val < 5000 then 0 else if j.val < 5005 then 1
        else if j.val < 7500 then 2 else 3 : Fin 5) = 2)).card = 2495
    rw [he, cutoff_interval_card 5005 7500 (by omega) (by omega)]
  · have he : (Finset.univ.filter (fun j : Fin 10000 =>
        (if j.val < 5000 then 0 else if j.val < 5005 then 1
          else if j.val < 7500 then 2 else 3 : Fin 5) = 3)) =
        Finset.univ.filter (fun j => 7500 ≤ j.val ∧ j.val < 10000) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> norm_num <;> omega
    change (Finset.univ.filter (fun j : Fin 10000 =>
      (if j.val < 5000 then 0 else if j.val < 5005 then 1
        else if j.val < 7500 then 2 else 3 : Fin 5) = 3)).card = 2500
    rw [he, cutoff_interval_card 7500 10000 (by omega) (by omega)]

theorem cutoff_simulated_sequence_proof :
    ∃ z : Fin 10000 → Bool × Finset (Fin 12),
      (∀ j, (z j).2∈seedChoices 12 6) ∧
      (∀ k : Fin 4, ((Finset.univ.filter (fun j =>
        (if (z j).1 then treatedSeedExposure ∅ {0,1,2,3,4,5} {0} (z j).2
          else 0)=k.castSucc)).card:ℝ)/10000=
        (![1/2,1/2000,499/2000,1/4] : Fin 4 → ℝ) k) := by
  classical
  refine ⟨cutoff_draw, ?_, ?_⟩
  · intro j
    unfold cutoff_draw
    split_ifs <;> norm_num [seedChoices, Finset.mem_powersetCard]
  · intro k
    rw [cutoff_histogram]
    fin_cases k <;> norm_num

noncomputable def positivity_avoid (F : Finset (Fin 12)) : Finset (Finset (Fin 12)) :=
  (seedChoices 12 6).filter (fun s => Disjoint s F)

theorem positivity_avoid_card (F : Finset (Fin 12)) :
    (positivity_avoid F).card = Nat.choose (12-F.card) 6 :=
  count_avoiding_seeds 12 6 F

theorem positivity_avoid_subset {A B : Finset (Fin 12)} (h : A ⊆ B) :
    positivity_avoid B ⊆ positivity_avoid A := by
  intro s hs
  obtain ⟨hs, hd⟩ := Finset.mem_filter.mp hs
  apply Finset.mem_filter.mpr
  refine ⟨hs, Finset.disjoint_left.mpr ?_⟩
  intro i hi ha
  exact Finset.disjoint_left.mp hd hi (h ha)

theorem positivity_w1_counts (k : Fin 5) :
    ((seedChoices 12 6).filter
      (fun s => treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = k)).card =
      (![0,1,461,462,0] : Fin 5 → ℕ) k := by
  classical
  have hsub : positivity_avoid {0,1,2,3,4,5} ⊆ positivity_avoid {0} :=
    positivity_avoid_subset (by simp)
  fin_cases k
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 0) =
        ∅ := by
      ext t
      by_cases hp : Disjoint t ({0,1,2,3,4,5} : Finset (Fin 12)) <;>
        by_cases h0 : (0 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 0)).card = 0
    rw [he]
    simp
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 1) =
        positivity_avoid {0,1,2,3,4,5} := by
      ext t
      by_cases hp : Disjoint t ({0,1,2,3,4,5} : Finset (Fin 12)) <;>
        by_cases h0 : (0 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 1)).card = 1
    rw [he]
    rw [positivity_avoid_card]; norm_num [Nat.choose]
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 2) =
        positivity_avoid {0} \ positivity_avoid {0,1,2,3,4,5} := by
      ext t
      by_cases hp : Disjoint t ({0,1,2,3,4,5} : Finset (Fin 12)) <;>
        by_cases h0 : (0 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 2)).card = 461
    rw [he]
    rw [Finset.card_sdiff_of_subset hsub, positivity_avoid_card, positivity_avoid_card]; norm_num [Nat.choose]
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 3) =
        seedChoices 12 6 \ positivity_avoid {0} := by
      ext t
      by_cases hp : Disjoint t ({0,1,2,3,4,5} : Finset (Fin 12)) <;>
        by_cases h0 : (0 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 3)).card = 462
    rw [he]
    rw [Finset.card_sdiff_of_subset (show positivity_avoid {0} ⊆ seedChoices 12 6 from
      Finset.filter_subset _ _), positivity_avoid_card]; norm_num [seedChoices, Finset.card_powersetCard, Nat.choose]
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 4) =
        ∅ := by
      ext t
      by_cases hp : Disjoint t ({0,1,2,3,4,5} : Finset (Fin 12)) <;>
        by_cases h0 : (0 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure ∅ {0,1,2,3,4,5} {0} s = 4)).card = 0
    rw [he]
    simp

theorem positivity_w2_counts (k : Fin 5) :
    ((seedChoices 12 6).filter
      (fun s => treatedSeedExposure {2} {0,1} {0} s = k)).card =
      (![0,84,126,252,462] : Fin 5 → ℕ) k := by
  classical
  have hsub1 : positivity_avoid {0,1,2} ⊆ positivity_avoid {0,2} :=
    positivity_avoid_subset (by simp)
  have hsub2 : positivity_avoid {0,2} ⊆ positivity_avoid {2} :=
    positivity_avoid_subset (by simp)
  fin_cases k
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure {2} {0,1} {0} s = 0) =
        ∅ := by
      ext t
      by_cases h0 : (0 : Fin 12) ∈ t <;> by_cases h1 : (1 : Fin 12) ∈ t <;>
        by_cases h2 : (2 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure {2} {0,1} {0} s = 0)).card = 0
    rw [he]
    simp
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure {2} {0,1} {0} s = 1) =
        positivity_avoid {0,1,2} := by
      ext t
      by_cases h0 : (0 : Fin 12) ∈ t <;> by_cases h1 : (1 : Fin 12) ∈ t <;>
        by_cases h2 : (2 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure {2} {0,1} {0} s = 1)).card = 84
    rw [he]
    rw [positivity_avoid_card]; norm_num [Nat.choose]
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure {2} {0,1} {0} s = 2) =
        positivity_avoid {0,2} \ positivity_avoid {0,1,2} := by
      ext t
      by_cases h0 : (0 : Fin 12) ∈ t <;> by_cases h1 : (1 : Fin 12) ∈ t <;>
        by_cases h2 : (2 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure {2} {0,1} {0} s = 2)).card = 126
    rw [he]
    rw [Finset.card_sdiff_of_subset hsub1, positivity_avoid_card, positivity_avoid_card]; norm_num [Nat.choose]
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure {2} {0,1} {0} s = 3) =
        positivity_avoid {2} \ positivity_avoid {0,2} := by
      ext t
      by_cases h0 : (0 : Fin 12) ∈ t <;> by_cases h1 : (1 : Fin 12) ∈ t <;>
        by_cases h2 : (2 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure {2} {0,1} {0} s = 3)).card = 252
    rw [he]
    rw [Finset.card_sdiff_of_subset hsub2, positivity_avoid_card, positivity_avoid_card]; norm_num [Nat.choose]
  · have he : (seedChoices 12 6).filter
        (fun s => treatedSeedExposure {2} {0,1} {0} s = 4) =
        seedChoices 12 6 \ positivity_avoid {2} := by
      ext t
      by_cases h0 : (0 : Fin 12) ∈ t <;> by_cases h1 : (1 : Fin 12) ∈ t <;>
        by_cases h2 : (2 : Fin 12) ∈ t <;>
        simp_all [positivity_avoid, treatedSeedExposure, Finset.disjoint_insert_right] <;>
        split_ifs <;> simp_all
    change ((seedChoices 12 6).filter (fun s =>
      treatedSeedExposure {2} {0,1} {0} s = 4)).card = 462
    rw [he]
    rw [Finset.card_sdiff_of_subset (show positivity_avoid {2} ⊆ seedChoices 12 6 from
      Finset.filter_subset _ _), positivity_avoid_card]; norm_num [seedChoices, Finset.card_powersetCard, Nat.choose]

theorem positivity_cutoff_counterexamples_proof :
    (seedChoices 12 6).card=924 ∧
    (∀ k : Fin 5, localExposureProbability 12 6 ∅ {0,1,2,3,4,5} {0} k=
      (![1/2,1/1848,461/1848,1/4,0] : Fin 5 → ℝ) k) ∧
    (∀ k : Fin 4, 0<(![1/2,1/1848,461/1848,1/4] : Fin 4 → ℝ) k ∧
      (![1/2,1/1848,461/1848,1/4] : Fin 4 → ℝ) k<1) ∧
    (0:ℝ)<1/1848 ∧ (1/1848:ℝ)<1/100 ∧
    (∀ k : Fin 5, localExposureProbability 12 6 {2} {0,1} {0} k=
      (![1/2,1/22,3/44,3/22,1/4] : Fin 5 → ℝ) k) ∧
    (∀ k : Fin 4, (1/100:ℝ)<(![1/2,1/22,3/44,3/22] : Fin 4 → ℝ) k) ∧
    ({2,3,4,5,6,7} : Finset (Fin 12))∈seedChoices 12 6 ∧
    ({3,4,5,6,7,8} : Finset (Fin 12))∈seedChoices 12 6 ∧
    treatedSeedExposure (n := 12) {2} {0,1} {0} {2,3,4,5,6,7}=4 ∧
    treatedSeedExposure (n := 12) {2} {0,1} {0} {3,4,5,6,7,8}=1 := by
  classical
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [seedChoices, Finset.card_powersetCard, Nat.choose]
  · intro k
    unfold localExposureProbability
    rw [positivity_w1_counts]
    fin_cases k <;> norm_num [Nat.choose]
  · intro k
    fin_cases k <;> norm_num
  · intro k
    unfold localExposureProbability
    rw [positivity_w2_counts]
    fin_cases k <;> norm_num [Nat.choose]
  · intro k
    fin_cases k <;> norm_num
  · norm_num [seedChoices, Finset.mem_powersetCard]
  · norm_num [seedChoices, Finset.mem_powersetCard]
  · norm_num [treatedSeedExposure, Finset.disjoint_insert_right]
  · norm_num [treatedSeedExposure, Finset.disjoint_insert_right]

theorem analysis_prob_positive_iff {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E : Ω → Prop) :
    0 < sampleProb P E ↔ ∃ w, E w := by
  classical
  constructor
  · intro hp
    by_contra hn
    have he : ∀ w, ¬ E w := fun w hw => hn ⟨w, hw⟩
    simp [sampleProb, he] at hp
  · rintro ⟨w, hw⟩
    calc
      0 < P.mass w := P.positive w
      _ = P.mass w * (if E w then 1 else 0) := by simp [hw]
      _ ≤ sampleProb P E := by
        unfold sampleProb
        exact Finset.single_le_sum
          (f := fun v => P.mass v * (if E v then 1 else 0))
          (fun v _ => mul_nonneg (P.positive v).le (by split_ifs <;> norm_num))
          (Finset.mem_univ w)

theorem analysis_disjoint_bound {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (E F : Ω → Prop) (h : ∀ w, E w → ¬F w) :
    sampleProb P E + sampleProb P F ≤ 1 := by
  classical
  unfold sampleProb
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ w, P.mass w := by
      apply Finset.sum_le_sum
      intro w _
      by_cases he : E w <;> by_cases hf : F w <;> simp [he, hf]
      · exact (h w he hf).elim
      · exact (P.positive w).le
    _ = 1 := P.total

theorem analysis_label_lt_one {Ω I : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (D : Ω → I → Fin 5) (i : I)
    (hp : ∀ k : Fin 4, 0 < sampleProb P (fun w => D w i = k.castSucc))
    (k : Fin 4) : sampleProb P (fun w => D w i = k.castSucc) < 1 := by
  obtain ⟨l, hl⟩ : ∃ l : Fin 4, l ≠ k := by
    by_cases hk : k = 0
    · exact ⟨1, by simp [hk]⟩
    · exact ⟨0, Ne.symm hk⟩
  have hb := analysis_disjoint_bound P (fun w => D w i = k.castSucc)
    (fun w => D w i = l.castSucc) (by
      intro w hk hlw
      exact hl (Fin.castSucc_injective 4 (hlw.symm.trans hk)))
  have hpl := hp l
  linarith

theorem analysis_set_inclusions_proof {Ω I : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (D : Ω → I → Fin 5) (J : ℕ) (hJ : 0<J)
    (draws : Fin J → Ω) (seed outcome baseline screen : Ω → I → Prop) (z : Ω) :
    let π := fun i k => sampleProb P (fun w => D w i=k.castSucc)
    let phat := fun i k => ((Finset.univ.filter
      (fun j => D (draws j) i=k.castSucc)).card:ℝ)/J
    positivityPopulation π=probabilityScreen π 0 ∧
    probabilityScreen π (1/100)⊆positivityPopulation π ∧
    probabilityScreen phat (1/100)⊆probabilityScreen phat 0 ∧
    probabilityScreen phat 0⊆positivityPopulation π ∧
    codeAnalysisSet phat seed outcome baseline screen z⊆positivityPopulation π ∧
    codeAnalysisSet phat seed outcome baseline screen z⊆{i | ¬seed z i} := by
  classical
  let π := fun (i : I) (k : Fin 4) => sampleProb P (fun w => D w i=k.castSucc)
  let phat := fun (i : I) (k : Fin 4) => ((Finset.univ.filter
    (fun j : Fin J => D (draws j) i=k.castSucc)).card:ℝ)/J
  change positivityPopulation π=probabilityScreen π 0 ∧
    probabilityScreen π (1/100)⊆positivityPopulation π ∧
    probabilityScreen phat (1/100)⊆probabilityScreen phat 0 ∧
    probabilityScreen phat 0⊆positivityPopulation π ∧
    codeAnalysisSet phat seed outcome baseline screen z⊆positivityPopulation π ∧
    codeAnalysisSet phat seed outcome baseline screen z⊆{i | ¬seed z i}
  have heq : positivityPopulation π=probabilityScreen π 0 := by
    ext i
    constructor
    · intro hi k
      exact (hi k).1
    · intro hi k
      exact ⟨hi k, analysis_label_lt_one P D i hi k⟩
  have htrue : probabilityScreen π (1/100) ⊆ positivityPopulation π := by
    rw [heq]
    intro i hi k
    have hk := hi k
    linarith
  have hcut : probabilityScreen phat (1/100) ⊆ probabilityScreen phat 0 := by
    intro i hi k
    have hk := hi k
    linarith
  have hfreq (i : I) (k : Fin 4) (hp : 0 < phat i k) : 0 < π i k := by
    have hj : (0:ℝ)<J := by exact_mod_cast hJ
    have hc : 0 < (Finset.univ.filter
        (fun j : Fin J => D (draws j) i=k.castSucc)).card := by
      have hr := (div_pos_iff_of_pos_right hj).mp hp
      exact_mod_cast hr
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hc
    exact (analysis_prob_positive_iff P _).mpr ⟨draws j, (Finset.mem_filter.mp hj).2⟩
  have hest : probabilityScreen phat 0 ⊆ positivityPopulation π := by
    rw [heq]
    intro i hi k
    exact hfreq i k (hi k)
  refine ⟨heq, htrue, hcut, hest, ?_, ?_⟩
  · intro i hi
    exact hest (hcut hi.1)
  · intro i hi
    exact hi.2.1

end AronowAudit.P037.Wave1
