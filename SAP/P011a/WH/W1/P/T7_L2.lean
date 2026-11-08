import SAP.P011a.WH.W1.Leaves
import AronowAudit.P011.Wave1.Gap.GP011B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W1.P.T7_L2

open Finset
open scoped BigOperators Classical

lemma average_strict_bounds {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hplus : average y ≠ 1) (hminus : average y ≠ -1) :
    -1 < average y ∧ average y < 1 := by
  have habs := AronowAudit.P011.Wave1.unbounded_caps_average_bound hn y hy
  have habs' := abs_le.mp habs
  constructor
  · by_contra h
    have heq : average y = -1 := le_antisymm (le_of_not_gt h) habs'.1
    exact hminus heq
  · by_contra h
    have heq : average y = 1 := le_antisymm habs'.2 (le_of_not_gt h)
    exact hplus heq

lemma residual_product_sign {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hmean : -1 < average y ∧ average y < 1) (i j : Fin n) :
    (y i = y j → 0 < centered y i * centered y j) ∧
    (y i ≠ y j → centered y i * centered y j < 0) := by
  have hpos (k : Fin n) (hk : y k = 1) : 0 < centered y k := by
    rw [centered, hk]
    linarith [hmean.2]
  have hneg (k : Fin n) (hk : y k = -1) : centered y k < 0 := by
    rw [centered, hk]
    linarith [hmean.1]
  constructor
  · intro he
    rcases hy i with hi | hi <;> rcases hy j with hj | hj
    · exact mul_pos (hpos i hi) (hpos j hj)
    · have : False := by rw [hi, hj] at he; norm_num at he
      exact this.elim
    · have : False := by rw [hi, hj] at he; norm_num at he
      exact this.elim
    · have hh := mul_pos (neg_pos.mpr (hneg i hi)) (neg_pos.mpr (hneg j hj))
      simpa using hh
  · intro he
    rcases hy i with hi | hi <;> rcases hy j with hj | hj
    · have : False := he (hi.trans hj.symm)
      exact this.elim
    · exact mul_neg_of_pos_of_neg (hpos i hi) (hneg j hj)
    · exact mul_neg_of_neg_of_pos (hneg i hi) (hpos j hj)
    · have : False := he (hi.trans hj.symm)
      exact this.elim

lemma maximizing_pair_eq {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (A : Graph n)
    (hm : Maximizes (emptyGraph n) (fun _ => n - 1) (fun B => V1 B y) A) :
    ∀ i j, adjacency A i j * centered y i * centered y j =
      adjacency (AronowAudit.P011.Wave1.unbounded_caps_equalGraph y) i j *
        centered y i * centered y j := by
  let W := AronowAudit.P011.Wave1.unbounded_caps_equalGraph y
  have hval : V1 A y = V1 W y := le_antisymm
    (AronowAudit.P011.Wave1.unbounded_caps_witness_max hn y hy A)
    (hm.2 W (AronowAudit.P011.Wave1.unbounded_caps_all_compatible W))
  have hquad : quadratic (adjacency A) (centered y) =
      quadratic (adjacency W) (centered y) := by
    unfold V1 at hval
    have hn2 : (n : ℝ) ^ 2 ≠ 0 := by
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      exact pow_ne_zero 2 hnR
    field_simp [hn2] at hval
    nlinarith [hval]
  have houter : (∑ i, ∑ j, adjacency A i j * centered y i * centered y j) =
      ∑ i, ∑ j, adjacency W i j * centered y i * centered y j := by
    simpa [quadratic] using hquad
  have hinner_le (i : Fin n) :
      (∑ j, adjacency A i j * centered y i * centered y j) ≤
        ∑ j, adjacency W i j * centered y i * centered y j := by
    apply Finset.sum_le_sum
    intro j _
    exact AronowAudit.P011.Wave1.unbounded_caps_pair_domination hn y hy A i j
  have hinner_eq (i : Fin n) :
      (∑ j, adjacency A i j * centered y i * centered y j) =
        ∑ j, adjacency W i j * centered y i * centered y j := by
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hinner_le i)).mp houter i
      (Finset.mem_univ i)
  intro i j
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ =>
    AronowAudit.P011.Wave1.unbounded_caps_pair_domination hn y hy A i j)).mp
      (hinner_eq i) j (Finset.mem_univ j)

end SAP.P011a.WH.W1.P.T7_L2

open SAP.P011a.WH.W1.P.T7_L2

theorem SAP.P011a.WH.W1.T7_L2_proof : SAP.P011a.WH.W1.T7_L2 := by
  intro n hn y hy hplus hminus A hm i j
  have hmean := average_strict_bounds hn y hy hplus hminus
  have hsign := residual_product_sign y hy hmean i j
  have hp := maximizing_pair_eq hn y hy A hm i j
  by_cases hij : i = j
  · subst j
    constructor
    · intro hA
      have hf := A.property.2 i
      rw [hA] at hf
      simp at hf
    · rintro ⟨hne, _⟩
      exact (hne rfl).elim
  · constructor
    · intro hA
      have he : y i = y j := by
        by_contra hne
        have hprod := hsign.2 hne
        have hAadj : adjacency A i j = 1 := by simp [adjacency, hA]
        have hWadj :
            adjacency (AronowAudit.P011.Wave1.unbounded_caps_equalGraph y) i j = 0 := by
          simp [adjacency, AronowAudit.P011.Wave1.unbounded_caps_equalGraph, hne]
        rw [hAadj, hWadj] at hp
        nlinarith
      exact ⟨hij, hsign.1 he⟩
    · rintro ⟨_, hprodpos⟩
      have he : y i = y j := by
        by_contra hne
        have hprodneg := hsign.2 hne
        linarith
      by_contra hA
      have hAadj : adjacency A i j = 0 := by simp [adjacency, hA]
      have hWadj :
          adjacency (AronowAudit.P011.Wave1.unbounded_caps_equalGraph y) i j = 1 := by
        simp [adjacency, AronowAudit.P011.Wave1.unbounded_caps_equalGraph, hij, he]
      rw [hAadj, hWadj] at hp
      have hprod := hsign.1 he
      nlinarith

