import SAP.P027a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W2.P.T13_L1

open SAP.P027a
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma certainty_prob_sum : (∑ k : Fin 8, certaintyProb8 k) = 2 := by
  norm_num [certaintyProb8, invalidSize8, Fin.sum_univ_succ]

lemma certainty_prob_zero : certaintyProb8 (0 : Fin 8) = 1 := by
  norm_num [certaintyProb8, invalidSize8]

lemma certainty_prob_succ (i : Fin 7) : certaintyProb8 i.succ = 1/7 := by
  norm_num [certaintyProb8, invalidSize8]

lemma certainty_left_succ (i : Fin 7) :
    cumulativeLeft certaintyProb8 i.succ = 1 + (i : ℝ)/7 := by
  fin_cases i <;>
    norm_num [cumulativeLeft, certaintyProb8, invalidSize8, Fin.sum_univ_succ]

lemma exists_fin_two {P : Fin 2 → Prop} :
    (∃ j, P j) ↔ P 0 ∨ P 1 := by
  constructor
  · rintro ⟨j, hj⟩
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

lemma selected_zero (u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u < 1) :
    systematicSelected certaintyProb8 2 u (0 : Fin 8) := by
  unfold systematicSelected
  refine ⟨0, ?_, ?_⟩ <;> simp [cumulativeLeft, certainty_prob_zero] <;> assumption

lemma cell_subset_unit (g : Fin 7) (u : ℝ) (hu : u ∈ certaintyCell8 g) :
    0 ≤ u ∧ u < 1 := by
  rcases hu with ⟨hu₀, hu₁⟩
  constructor
  · exact le_trans (by positivity) hu₀
  · apply lt_of_lt_of_le hu₁
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 7)).2
    have hgv : (g : ℝ) + 1 ≤ 7 := by exact_mod_cast (Nat.succ_le_of_lt g.isLt)
    nlinarith [hgv]

lemma selected_succ_iff_cell (i : Fin 7) (u : ℝ) (hu₁ : u < 1) :
    systematicSelected certaintyProb8 2 u i.succ ↔
      u ∈ Set.Ico ((i : ℝ)/7) (((i : ℝ)+1)/7) := by
  classical
  unfold systematicSelected
  simp only [certainty_prob_sum]
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul]
  rw [certainty_left_succ, certainty_prob_succ, exists_fin_two]
  constructor
  · rintro (hzero | hone)
    · norm_num at hzero
      have hi : 0 ≤ (i : ℝ)/7 := by positivity
      have hleft : 1 ≤ 1 + (i : ℝ)/7 := by linarith
      linarith
    · norm_num at hone
      rcases hone with ⟨hlo, hhi⟩
      exact ⟨by linarith, by linarith⟩
  · intro hcell
    rcases hcell with ⟨hlo, hhi⟩
    right
    norm_num
    exact ⟨by linarith, by linarith⟩

lemma cell_index_iff (g i : Fin 7) (u : ℝ) (hu : u ∈ certaintyCell8 g) :
    u ∈ Set.Ico ((i : ℝ)/7) (((i : ℝ)+1)/7) ↔ i = g := by
  change (i : ℝ)/7 ≤ u ∧ u < ((i : ℝ)+1)/7 ↔ i = g
  change (g : ℝ)/7 ≤ u ∧ u < ((g : ℝ)+1)/7 at hu
  constructor
  · intro hi
    have hval : i.val = g.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hstep : (i : ℝ) + 1 ≤ (g : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hlt
        nlinarith [hi.2, hu.1, hstep]
      · have hstep : (g : ℝ) + 1 ≤ (i : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hgt
        nlinarith [hu.2, hi.1, hstep]
    exact Fin.ext hval
  · intro h
    subst i
    exact hu

lemma selection_cell_iff (g : Fin 7) (u : ℝ) (hu : u ∈ certaintyCell8 g) (k : Fin 8) :
    systematicSelected certaintyProb8 2 u k ↔ k = 0 ∨ k.val = g.val + 1 := by
  refine Fin.cases ?_ ?_ k
  · have hb := cell_subset_unit g u hu
    simp [selected_zero u hb.1 hb.2]
  · intro i
    have hb := cell_subset_unit g u hu
    rw [selected_succ_iff_cell i u hb.2, cell_index_iff g i u hu]
    constructor
    · intro h
      subst i
      simp
    · intro h
      rcases h with hzero | hval
      · exact (Fin.succ_ne_zero i hzero).elim
      · apply Fin.ext
        simp only [Fin.val_succ] at hval
        omega

end SAP.P027a.WH.W2.P.T13_L1

theorem SAP.P027a.WH.W2.T13_L1_proof : SAP.P027a.WH.W2.T13_L1 := by
  classical
  intro g u hu
  have hsel := fun k =>
    SAP.P027a.WH.W2.P.T13_L1.selection_cell_iff g u hu k
  funext k
  change decide (systematicSelected certaintyProb8 2 u k) =
    decide (k = 0 ∨ k.val = g.val + 1)
  by_cases hs : systematicSelected certaintyProb8 2 u k
  · have ht := (hsel k).mp hs
    simp [hs, ht]
  · have ht : ¬ (k = 0 ∨ k.val = g.val + 1) := fun ht => hs ((hsel k).mpr ht)
    simp [hs, ht]
