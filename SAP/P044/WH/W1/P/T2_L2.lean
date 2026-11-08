import SAP.P044.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.WH.W1.P.T2_L2

open Finset
open scoped BigOperators

private lemma sum_pair_first (m : ℕ) (c : ℚ) :
    (∑ p : Fin 2 × Fin m, if p.1 = 1 then c else 0) = (m : ℚ) * c := by
  rw [Fintype.sum_prod_type]
  simp

private lemma sum_pair_second (m : ℕ) (t : Fin m) (c : ℚ) :
    (∑ p : Fin 2 × Fin m, if p.2 = t then c else 0) = 2 * c := by
  rw [Fintype.sum_prod_type]
  simp

private theorem treated_marginal (n : ℕ) (hg : W1MatchingGeometry n)
    (i : Fin (w1MatchingN n)) :
    marginal w1Uniform (w1MatchingF n) i .d11 =
      if i.val < 2 then (1/2 : ℚ) else 1 / ((n : ℚ) + 2) := by
  have hgeom := hg.2.2.2.1
  have hmass (s : Fin (w1MatchingR n)) :
      w1Uniform s = 1 / (2 * ((n + 2 : ℕ) : ℚ)) := by
    unfold w1Uniform
    rw [show w1MatchingR n = 2 * (n + 2) by rfl, Fintype.card_fin]
    push_cast
    rfl
  have hmarginal :
      marginal w1Uniform (w1MatchingF n) i .d11 =
        ∑ s : Fin (w1MatchingR n),
          if w1MatchingAssignments n s i then w1Uniform s else 0 := by
    unfold marginal
    apply Finset.sum_congr rfl
    intro s hs
    rw [hgeom]
    cases w1MatchingAssignments n s i <;> rfl
  let c : ℚ := 1 / (2 * ((n + 2 : ℕ) : ℚ))
  have hReindex :
      (∑ s : Fin (w1MatchingR n),
          if w1MatchingAssignments n s i then c else 0) =
        ∑ p : Fin 2 × Fin (n + 2),
          if w1MatchingAssignments n (finProdFinEquiv p) i then c else 0 := by
    change (∑ s : Fin (2 * (n + 2)),
        if w1MatchingAssignments n s i then c else 0) = _
    exact (Equiv.sum_comp finProdFinEquiv
      (fun s : Fin (2 * (n + 2)) =>
        if w1MatchingAssignments n s i then c else 0)).symm
  by_cases hi : i.val < 2
  · have hdiv : i.val / 2 = 0 := by omega
    have hsmall : i.val ≤ 1 := by omega
    rw [hmarginal]
    simp_rw [hmass]
    rw [show (∑ s : Fin (w1MatchingR n),
        if w1MatchingAssignments n s i then c else 0) =
        (∑ p : Fin 2 × Fin (n + 2),
          if w1MatchingAssignments n (finProdFinEquiv p) i then c else 0) from hReindex]
    have hsum :
        (∑ p : Fin 2 × Fin (n + 2),
          if w1MatchingAssignments n (finProdFinEquiv p) i then c else 0) =
          (n + 2 : ℚ) * c := by
      simpa [w1MatchingAssignments, hdiv, hsmall, c] using
        (sum_pair_first (n + 2) c)
    rw [hsum]
    rw [if_pos hi]
    dsimp [c]
    have hn : (0 : ℚ) < (n : ℚ) + 2 := by positivity
    push_cast
    field_simp
  · have hk : 0 < i.val / 2 := by omega
    have hdivne : i.val / 2 ≠ 0 := by omega
    have hbig : 2 ≤ i.val := by omega
    have hnotSmall : ¬ i.val ≤ 1 := by omega
    have htbound : i.val / 2 - 1 < n + 2 := by
      have hN : i.val < 2 * (n + 3) := i.isLt
      omega
    let t : Fin (n + 2) := ⟨i.val / 2 - 1, htbound⟩
    have hcond (p : Fin 2 × Fin (n + 2)) :
        (i.val / 2 = p.2.val + 1) ↔ p.2 = t := by
      constructor
      · intro h
        apply Fin.ext
        simp [t]
        omega
      · intro h
        have hv := congrArg Fin.val h
        simp [t] at hv
        omega
    rw [hmarginal]
    simp_rw [hmass]
    rw [show (∑ s : Fin (w1MatchingR n),
        if w1MatchingAssignments n s i then c else 0) =
        (∑ p : Fin 2 × Fin (n + 2),
          if w1MatchingAssignments n (finProdFinEquiv p) i then c else 0) from hReindex]
    have hsum :
        (∑ p : Fin 2 × Fin (n + 2),
          if w1MatchingAssignments n (finProdFinEquiv p) i then c else 0) = 2 * c := by
      simpa [w1MatchingAssignments, hdivne, hbig, hnotSmall, hcond, c] using
        (sum_pair_second (n + 2) t c)
    rw [hsum]
    rw [if_neg hi]
    dsimp [c]
    have hn : (0 : ℚ) < (n : ℚ) + 2 := by positivity
    push_cast
    field_simp

private theorem total_uniform (n : ℕ) :
    (∑ s : Fin (w1MatchingR n), w1Uniform s) = 1 := by
  have hn : 0 < w1MatchingR n := by simp [w1MatchingR]
  letI : Nonempty (Fin (w1MatchingR n)) := ⟨⟨0, hn⟩⟩
  simp [w1Uniform, Fintype.card_ne_zero]
  have hR : (w1MatchingR n : ℚ) ≠ 0 := by positivity
  field_simp

private theorem complementary_marginal (n : ℕ) (hg : W1MatchingGeometry n)
    (i : Fin (w1MatchingN n)) :
    marginal w1Uniform (w1MatchingF n) i .d00 =
      1 - marginal w1Uniform (w1MatchingF n) i .d11 := by
  have hgeom := hg.2.2.2.1
  have hsplit : ∀ s : Fin (w1MatchingR n),
      (if w1MatchingF n s i = .d11 then w1Uniform s else 0) +
      (if w1MatchingF n s i = .d00 then w1Uniform s else 0) = w1Uniform s := by
    intro s
    rw [hgeom]
    cases w1MatchingAssignments n s i <;> simp
  have hsum : marginal w1Uniform (w1MatchingF n) i .d11 +
      marginal w1Uniform (w1MatchingF n) i .d00 = 1 := by
    calc
      _ = ∑ s : Fin (w1MatchingR n),
            ((if w1MatchingF n s i = .d11 then w1Uniform s else 0) +
             (if w1MatchingF n s i = .d00 then w1Uniform s else 0)) := by
               simp [marginal, Finset.sum_add_distrib]
      _ = ∑ s : Fin (w1MatchingR n), w1Uniform s := by
            apply Finset.sum_congr rfl
            intro s hs
            exact hsplit s
      _ = 1 := total_uniform n
  linarith

end SAP.P044.WH.W1.P.T2_L2

theorem SAP.P044.WH.W1.T2_L2_proof : SAP.P044.WH.W1.T2_L2 := by
  intro n hg
  refine ⟨?_, ?_⟩
  · intro i a
    cases a with
    | d11 => simpa using SAP.P044.WH.W1.P.T2_L2.treated_marginal n hg i
    | d00 =>
        rw [SAP.P044.WH.W1.P.T2_L2.complementary_marginal n hg i,
          SAP.P044.WH.W1.P.T2_L2.treated_marginal n hg i]
        split_ifs with hi
        · norm_num
        · have hn : (0 : ℚ) < (n : ℚ) + 2 := by positivity
          field_simp
          ring
    | d10 | d01 =>
        have hgeom := hg.2.2.2.1
        unfold marginal
        apply Finset.sum_eq_zero
        intro s hs
        rw [hgeom]
        cases w1MatchingAssignments n s i <;> simp
  · intro i
    constructor
    · rw [SAP.P044.WH.W1.P.T2_L2.treated_marginal n hg i]
      split_ifs <;> positivity
    · rw [SAP.P044.WH.W1.P.T2_L2.complementary_marginal n hg i,
        SAP.P044.WH.W1.P.T2_L2.treated_marginal n hg i]
      split_ifs with hi
      · norm_num
      · have hn : (0 : ℚ) < (n : ℚ) + 2 := by positivity
        have hn1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
        rw [show 1 - 1 / ((n : ℚ) + 2) = ((n : ℚ) + 1) / ((n : ℚ) + 2) by
          field_simp
          ring]
        positivity
