import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T2_L2

open scoped BigOperators Classical

private lemma source_monotone {n : ℕ} (P : Population n)
    (hm : MonotoneReceipt P) :
    AronowAudit.P002.MonotoneReceipt (SAP.P002a.Bridge.toPopulation P) := by
  intro i hi
  change P.d i false = true at hi
  change P.d i true = true
  exact hm i hi

private lemma source_compliers_nonempty {n : ℕ} (P : Population n)
    (hc : (compliers P).Nonempty) :
    (AronowAudit.P002.compliers (SAP.P002a.Bridge.toPopulation P)).Nonempty := by
  rw [← SAP.P002a.Bridge.compliers_eq P]
  exact hc

private lemma mean_w_equal_at_late {n : ℕ} (P : Population n)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty) :
    mean (w P true (late P)) = mean (w P false (late P)) := by
  have h := AronowAudit.P002.mean_w_equal_at_late (SAP.P002a.Bridge.toPopulation P)
    (source_monotone P hm) (source_compliers_nonempty P hc)
  simpa only [SAP.P002a.Bridge.mean_eq, SAP.P002a.Bridge.w_eq,
    SAP.P002a.Bridge.late_eq] using h

private lemma w_difference_compliers {n : ℕ} (P : Population n)
    (hm : MonotoneReceipt P) (β : ℝ) (i : Fin n) :
    w P true β i - w P false β i =
      if i ∈ compliers P then P.y i true - P.y i false - β else 0 := by
  cases h0 : P.d i false <;> cases h1 : P.d i true
  · simp [w, binary, compliers, h0, h1]
  · simp [w, binary, compliers, h0, h1]
    ring
  · have hh := hm i h0
    simp [h1] at hh
  · simp [w, binary, compliers, h0, h1]

private lemma v_difference_zero_off_compliers {n : ℕ} (P : Population n)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty) {i : Fin n}
    (hi : i ∉ compliers P) :
    v P true (late P) i - v P false (late P) i = 0 := by
  have hmeans := mean_w_equal_at_late P hm hc
  have hw := w_difference_compliers P hm (late P) i
  have hwzero : w P true (late P) i - w P false (late P) i = 0 := by
    rw [hw]
    simp [hi]
  simp only [v]
  rw [hmeans]
  calc
    (w P true (late P) i - mean (w P false (late P))) -
        (w P false (late P) i - mean (w P false (late P))) =
        w P true (late P) i - w P false (late P) i := by ring
    _ = 0 := hwzero

end SAP.P002a.WH.W2.P.T2_L2

namespace SAP.P002a.WH.W2

open SAP.P002a.WH.W2.P.T2_L2

theorem T2_L2_proof : SAP.P002a.WH.W2.T2_L2 := by
  intro hchain
  intro n P δ r A hδ hr hA hP
  let C := compliers P
  let B := W2b1 P δ * (∑ i, v P true (late P) i ^ 2) +
    W2b0 P δ * (∑ i, v P false (late P) i ^ 2)
  have hm : MonotoneReceipt P := hP.2.1
  have hc : C.Nonempty := hP.2.2.1
  have hmeans : mean (w P true (late P)) = mean (w P false (late P)) :=
    mean_w_equal_at_late P hm hc
  have hzeroOff (i : Fin n) (hi : i ∉ C) :
      v P true (late P) i - v P false (late P) i = 0 := by
    exact v_difference_zero_off_compliers P hm hc hi
  have hscale : 0 ≤ (fraction P) ^ 2 * (1 - fraction P) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hP.1.1
  have hnDen : 0 < (n : ℝ) - 1 := by linarith
  have ht : (0 : ℝ) < (P.n1 : ℝ) := by exact_mod_cast hP.1.2.1
  have htn : (P.n1 : ℝ) < n := by exact_mod_cast hP.1.2.2
  have hcontrol : 0 < controlSize P := by
    unfold controlSize
    linarith
  have hb1 : 0 ≤ W2b1 P δ := by
    unfold W2b1
    positivity
  have hb0 : 0 ≤ W2b0 P δ := by
    unfold W2b0
    positivity
  have hsum1 : 0 ≤ ∑ i, v P true (late P) i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum0 : 0 ≤ ∑ i, v P false (late P) i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg hb1 hsum1) (mul_nonneg hb0 hsum0)
  have hcore :
      (∑ i, (v P true (late P) i - v P false (late P) i) ^ 2) /
          ((n : ℝ) - 1) ≤ B / ((n : ℝ) - 1) := by
    by_cases hbig : 2 ≤ C.card
    · have hgroup := hchain P δ r A hδ hr hA hP hbig
      have hlast := hgroup.2.1.trans (hgroup.2.2.1.trans hgroup.2.2.2)
      have hrestrict :
          (∑ i, (v P true (late P) i - v P false (late P) i) ^ 2) =
            ∑ i ∈ C, (v P true (late P) i - v P false (late P) i) ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ C)
        intro i hi hin
        rw [hzeroOff i hin]
        norm_num
      have hsub (a : Bool) :
          (∑ i ∈ C, v P a (late P) i ^ 2) ≤ ∑ i, v P a (late P) i ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        intro i hi hin
        exact sq_nonneg _
      have hBcomp :
          W2b1 P δ * (∑ i ∈ C, v P true (late P) i ^ 2) +
              W2b0 P δ * (∑ i ∈ C, v P false (late P) i ^ 2) ≤ B := by
        dsimp [B]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hsub true) hb1)
          (mul_le_mul_of_nonneg_left (hsub false) hb0)
      have hCden : 0 < (C.card : ℝ) - 1 := by
        have hcard : 1 < C.card := by omega
        have hcardR : (1 : ℝ) < (C.card : ℝ) := by exact_mod_cast hcard
        linarith
      have hratio :
          (∑ i ∈ C, (v P true (late P) i - v P false (late P) i) ^ 2) /
              ((C.card : ℝ) - 1) ≤ B / ((C.card : ℝ) - 1) := by
        calc
          _ ≤ (W2b1 P δ * (∑ i ∈ C, v P true (late P) i ^ 2) +
                W2b0 P δ * (∑ i ∈ C, v P false (late P) i ^ 2)) /
                ((C.card : ℝ) - 1) := hlast
          _ ≤ B / ((C.card : ℝ) - 1) :=
            div_le_div_of_nonneg_right hBcomp hCden.le
      have hscaled := mul_le_mul_of_nonneg_right hratio hCden.le
      have hleft :
          ((∑ i ∈ C, (v P true (late P) i - v P false (late P) i) ^ 2) /
            ((C.card : ℝ) - 1)) * ((C.card : ℝ) - 1) =
              ∑ i ∈ C, (v P true (late P) i - v P false (late P) i) ^ 2 := by
        field_simp [ne_of_gt hCden]
      have hright : (B / ((C.card : ℝ) - 1)) * ((C.card : ℝ) - 1) = B := by
        field_simp [ne_of_gt hCden]
      rw [hleft, hright] at hscaled
      rw [hrestrict]
      exact div_le_div_of_nonneg_right hscaled hnDen.le
    · have hcard : C.card = 1 := by
        have hpos : 0 < C.card := Finset.card_pos.mpr hc
        omega
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
      have hlate : late P = P.y j true - P.y j false := by
        unfold late groupMean
        have hj' : compliers P = {j} := by simpa [C] using hj
        rw [hj']
        simp
      have hwzero (i : Fin n) : w P true (late P) i - w P false (late P) i = 0 := by
        rw [w_difference_compliers P hm (late P) i]
        by_cases hi : i ∈ compliers P
        · rw [if_pos hi]
          have hj' : compliers P = {j} := by simpa [C] using hj
          have hij : i = j := by simpa [hj'] using hi
          subst i
          rw [hlate]
          ring
        · simp [hi]
      have hvzero (i : Fin n) : v P true (late P) i - v P false (late P) i = 0 := by
        simp only [v]
        rw [hmeans]
        calc
          (w P true (late P) i - mean (w P false (late P))) -
              (w P false (late P) i - mean (w P false (late P))) =
              w P true (late P) i - w P false (late P) i := by ring
          _ = 0 := hwzero i
      have hsumzero :
          (∑ i, (v P true (late P) i - v P false (late P) i) ^ 2) = 0 := by
        simp_rw [hvzero]
        simp
      rw [hsumzero]
      exact div_le_div_of_nonneg_right hB hnDen.le
  calc
    Sdiff2 P (late P) =
        ((fraction P) ^ 2 * (1 - fraction P) ^ 2) *
          ((∑ i, (v P true (late P) i - v P false (late P) i) ^ 2) /
            ((n : ℝ) - 1)) := by
      simp [Sdiff2]
      ring
    _ ≤ ((fraction P) ^ 2 * (1 - fraction P) ^ 2) * (B / ((n : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hcore hscale
    _ = (fraction P) ^ 2 * (1 - fraction P) ^ 2 / ((n : ℝ) - 1) * B := by ring

end SAP.P002a.WH.W2
