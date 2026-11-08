import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T14_L1

open SAP.P002a

def upperHalf (m : ℕ) : Finset (Fin (2 * m)) :=
  Finset.univ.filter fun i => m ≤ i.val

lemma upperHalf_card (m : ℕ) : (upperHalf m).card = m := by
  classical
  calc
    (upperHalf m).card = (Finset.univ : Finset (Fin m)).card := by
      change (Finset.univ.filter (fun i : Fin (2 * m) => m ≤ i.val)).card =
        (Finset.univ : Finset (Fin m)).card
      apply Finset.card_bij (fun i hi =>
        (⟨i.val - m, by
          have hhi : m ≤ i.val := (Finset.mem_filter.mp hi).2
          have hilt := i.isLt
          omega⟩ : Fin m))
      · intro i hi
        simp
      · intro i hi j hj hij
        apply Fin.ext
        have hij' := congrArg Fin.val hij
        have hii : m ≤ i.val := (Finset.mem_filter.mp hi).2
        have hjj : m ≤ j.val := (Finset.mem_filter.mp hj).2
        change i.val - m = j.val - m at hij'
        omega
      · intro j hj
        refine ⟨⟨m + j.val, by have := j.isLt; omega⟩, ?_, ?_⟩
        · simp [upperHalf]
        · apply Fin.ext
          simp only [Fin.val_mk]
          omega
    _ = m := by simp

lemma lowerHalf_card (m : ℕ) :
    (Finset.univ \ upperHalf m).card = m := by
  have hs : upperHalf m ⊆ (Finset.univ : Finset (Fin (2 * m))) := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hs, Finset.card_univ, Fintype.card_fin, upperHalf_card]
  omega

lemma split_count (m l : ℕ) (s : Finset (Fin (2 * m)))
    (hs : s.card = m) (hcomp : (Finset.univ \ s).card = m) (hl : l ≤ m) :
    (((Finset.univ : Finset (Fin (2 * m))).powersetCard m).filter
      (fun a => (a ∩ s).card = l)).card = Nat.choose m l * Nat.choose m (m - l) := by
  classical
  calc
    _ = (s.powersetCard l).card * ((Finset.univ \ s).powersetCard (m - l)).card := by
      rw [← Finset.card_product]
      apply Finset.card_bij (fun a _ => (a ∩ s, a \ s))
      · intro a ha
        rcases Finset.mem_filter.mp ha with ⟨ha, hal⟩
        have ham := (Finset.mem_powersetCard.mp ha).2
        simp only [Finset.mem_product, Finset.mem_powersetCard]
        refine ⟨⟨Finset.inter_subset_right, hal⟩, ⟨?_, ?_⟩⟩
        · intro x hx
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
        · rw [Finset.card_sdiff, ham, Finset.inter_comm s a, hal]
      · intro a ha b hb hab
        have h₁ := congrArg Prod.fst hab
        have h₂ := congrArg Prod.snd hab
        change a ∩ s = b ∩ s at h₁
        change a \ s = b \ s at h₂
        calc
          a = (a \ s) ∪ (a ∩ s) := (Finset.sdiff_union_inter a s).symm
          _ = (b \ s) ∪ (b ∩ s) := by rw [h₁, h₂]
          _ = b := Finset.sdiff_union_inter b s
      · rintro ⟨u, v⟩ huv
        rcases Finset.mem_product.mp huv with ⟨hu, hv⟩
        rcases Finset.mem_powersetCard.mp hu with ⟨hus, huk⟩
        rcases Finset.mem_powersetCard.mp hv with ⟨hvs, hvk⟩
        have hdis : Disjoint u v := by
          apply Finset.disjoint_left.mpr
          intro x hxu hxv
          exact (Finset.mem_sdiff.mp (hvs hxv)).2 (hus hxu)
        have hinter : (u ∪ v) ∩ s = u := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hxu | hxv, hxs⟩
            · exact hxu
            · exact False.elim ((Finset.mem_sdiff.mp (hvs hxv)).2 hxs)
          · intro hxu
            exact ⟨Or.inl hxu, hus hxu⟩
        have hdiff : (u ∪ v) \ s = v := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hxu | hxv, hxs⟩
            · exact False.elim (hxs (hus hxu))
            · exact hxv
          · intro hxv
            exact ⟨Or.inr hxv, (Finset.mem_sdiff.mp (hvs hxv)).2⟩
        refine ⟨u ∪ v, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
          · rw [Finset.card_union_of_disjoint hdis, huk, hvk]
            omega
          · rw [hinter, huk]
        · exact Prod.ext hinter hdiff
    _ = Nat.choose m l * Nat.choose m (m - l) := by
      simp only [Finset.card_powersetCard, hs, hcomp]

lemma W2K_eq_inter_card (m : ℕ) (T : Finset (Fin (2 * m))) :
    W2K m T = (T ∩ upperHalf m).card := by
  unfold W2K upperHalf
  congr 1
  ext i
  simp

end SAP.P002a.WH.W2.P.T14_L1

open SAP.P002a
open SAP.P002a.WH.W2.P.T14_L1

theorem SAP.P002a.WH.W2.T14_L1_proof : SAP.P002a.WH.W2.T14_L1 := by
  classical
  intro m hm l
  let s := upperHalf m
  have hs : s.card = m := upperHalf_card m
  have hcomp : (Finset.univ \ s).card = m := lowerHalf_card m
  have hassignment : assignments (signModel m) =
      (Finset.univ : Finset (Fin (2 * m))).powersetCard m := rfl
  have hden : (assignments (signModel m)).card = Nat.choose (2 * m) m := by
    rw [hassignment, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hdenR : ((assignments (signModel m)).card : ℝ) =
      (Nat.choose (2 * m) m : ℝ) := by
    exact congrArg (fun n : ℕ => (n : ℝ)) hden
  have hdenne : (Nat.choose (2 * m) m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega)))
  by_cases hl : l ≤ m
  · have hcount := split_count m l s hs hcomp hl
    have hprob : probability (signModel m) (fun T => W2K m T = l) =
        ((Nat.choose m l * Nat.choose m (m - l) : ℕ) : ℝ) /
          (Nat.choose (2 * m) m : ℕ) := by
      unfold probability
      rw [hdenR]
      apply (div_left_inj' hdenne).2
      norm_cast
      convert hcount using 1
      apply congrArg Finset.card
      ext T
      simp only [Finset.mem_filter, hassignment]
      rw [W2K_eq_inter_card]
    rw [if_pos hl, hprob]
  · rw [if_neg hl]
    unfold probability
    rw [hdenR, div_eq_zero_iff]
    left
    norm_cast
    apply Finset.card_eq_zero.mpr
    ext T
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨hT, hk⟩
    have hTcard : T.card = m := by simpa [hassignment] using hT
    rw [W2K_eq_inter_card] at hk
    have hle : (T ∩ upperHalf m).card ≤ T.card :=
      Finset.card_le_card Finset.inter_subset_left
    omega

