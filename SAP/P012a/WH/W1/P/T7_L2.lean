import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T7_L2

open Finset
open scoped Classical
open SAP.P012a
open SAP.P012a.WH.W1

noncomputable section

private def pairCond (D : Data) (k j : ℕ) : Prop :=
  D.parent k = D.parent j ∧ D.time k ≤ D.time j

private lemma sum_pair_swap (D : Data) (f g : ℕ → ℚ) :
    (∑ j ∈ nonseeds D,
      ∑ k ∈ nonseeds D,
        g j * (if pairCond D k j then f k else 0)) =
    (∑ k ∈ nonseeds D,
      ∑ j ∈ nonseeds D,
        g j * (if pairCond D k j then f k else 0)) := by
  classical
  rw [Finset.sum_comm]

private lemma past_eq_pair_sum (D : Data) (j : ℕ) :
    pWholePastReciprocal D j =
      ∑ k ∈ nonseeds D,
        if pairCond D k j then 1 / (pWholeDenom D k : ℚ) else 0 := by
  simp [pWholePastReciprocal, pairCond, Finset.sum_filter]

private lemma sum_if_filter_card (S : Finset ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (c : ℚ) :
    (∑ j ∈ S, if P j then if Q j then c else 0 else 0) =
      ((S.filter P).filter Q).card * c := by
  classical
  calc
    _ = ∑ j ∈ S.filter P, if Q j then c else 0 := by
      rw [← Finset.sum_filter]
    _ = ∑ j ∈ (S.filter P).filter Q, c := by
      rw [← Finset.sum_filter]
    _ = _ := by simp [Finset.sum_const, mul_comm]

private lemma sum_indicator_if_filter_card (S : Finset ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (c : ℚ) :
    (∑ j ∈ S, (if Q j then (1 : ℚ) else 0) *
      (if P j then c else 0)) = ((S.filter P).filter Q).card * c := by
  have hs :
      (∑ j ∈ S, (if Q j then (1 : ℚ) else 0) *
        (if P j then c else 0)) =
        ∑ j ∈ S, if P j then if Q j then c else 0 else 0 := by
    apply sum_congr rfl
    intro j hj
    by_cases hp : P j <;> by_cases hq : Q j <;> simp [hp, hq]
  rw [hs]
  exact sum_if_filter_card S P Q c

private lemma triangular_indicator (D : Data) (F : ℕ → Prop)
    [DecidablePred F] :
    (∑ j ∈ nonseeds D, (if F j then (1 : ℚ) else 0) *
      pWholePastReciprocal D j) =
      ∑ k ∈ nonseeds D,
        (((laterChildren D k).filter F).card : ℚ) /
          (pWholeDenom D k : ℚ) := by
  classical
  calc
    _ = ∑ j ∈ nonseeds D,
        ∑ k ∈ nonseeds D,
          if pairCond D k j then (if F j then (1 : ℚ) else 0) *
            (1 / (pWholeDenom D k : ℚ)) else 0 := by
      simp_rw [past_eq_pair_sum, Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ k ∈ nonseeds D,
        ∑ j ∈ nonseeds D,
          if pairCond D k j then (if F j then (1 : ℚ) else 0) *
            (1 / (pWholeDenom D k : ℚ)) else 0 := by
      simpa [mul_comm] using
        (sum_pair_swap D (fun k => 1 / (pWholeDenom D k : ℚ))
          (fun j => (if F j then (1 : ℚ) else 0)))
    _ = ∑ k ∈ nonseeds D,
        (((nonseeds D).filter (fun j => pairCond D k j)).filter F).card *
          (1 / (pWholeDenom D k : ℚ)) := by
      apply sum_congr rfl
      intro k hk
      simpa using
        (sum_indicator_if_filter_card (nonseeds D) (pairCond D k) F
          (1 / (pWholeDenom D k : ℚ)))
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      have hset :
          ((nonseeds D).filter (fun j => pairCond D k j)).filter F =
            (laterChildren D k).filter F := by
        ext j
        simp only [Finset.mem_filter, laterChildren]
        simp [pairCond, eq_comm, and_assoc, and_comm]
      rw [hset]
      simp [Finset.sum_const, div_eq_mul_inv]

private def isMatch (D : Data) (j : ℕ) : Prop :=
  D.trait j = D.trait (D.parent j)

private def matchQ (D : Data) (j : ℕ) : ℚ :=
  if D.trait j = D.trait (D.parent j) then 1 else 0

private def nonmatchCount (D : Data) (j : ℕ) : ℕ :=
  ((laterChildren D j).filter
    (fun k => D.trait k ≠ D.trait (D.parent k))).card

private lemma later_filter_match_eq (D : Data) (j : ℕ) :
    (laterChildren D j).filter (fun k => D.trait k = D.trait (D.parent k)) =
      (laterChildren D j).filter (fun k => D.trait k = D.trait (D.parent j)) := by
  ext k
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hk, hm⟩
    have hp : D.parent k = D.parent j := by
      have htmp : k ∈ nonseeds D ∧ D.parent k = D.parent j ∧ D.time j ≤ D.time k :=
        (by simpa [laterChildren] using hk)
      exact htmp.2.1
    exact ⟨hk, by simpa [isMatch, hp] using hm⟩
  · rintro ⟨hk, hm⟩
    have hp : D.parent k = D.parent j := by
      have htmp : k ∈ nonseeds D ∧ D.parent k = D.parent j ∧ D.time j ≤ D.time k :=
        (by simpa [laterChildren] using hk)
      exact htmp.2.1
    exact ⟨hk, by simpa [isMatch, hp] using hm⟩

private lemma later_filter_nonmatch_eq (D : Data) (j : ℕ) :
    (laterChildren D j).filter (fun k => D.trait k ≠ D.trait (D.parent k)) =
      (laterChildren D j).filter (fun k => D.trait k ≠ D.trait (D.parent j)) := by
  ext k
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hk, hm⟩
    have hp : D.parent k = D.parent j := by
      have htmp : k ∈ nonseeds D ∧ D.parent k = D.parent j ∧ D.time j ≤ D.time k :=
        (by simpa [laterChildren] using hk)
      exact htmp.2.1
    exact ⟨hk, by simpa [isMatch, hp] using hm⟩
  · rintro ⟨hk, hm⟩
    have hp : D.parent k = D.parent j := by
      have htmp : k ∈ nonseeds D ∧ D.parent k = D.parent j ∧ D.time j ≤ D.time k :=
        (by simpa [laterChildren] using hk)
      exact htmp.2.1
    exact ⟨hk, by simpa [isMatch, hp] using hm⟩

private lemma match_past_identity (D : Data) :
    (∑ j ∈ nonseeds D, matchQ D j * pWholePastReciprocal D j) =
      ∑ j ∈ nonseeds D,
        (childMatches D j : ℚ) / (pWholeDenom D j : ℚ) := by
  calc
    _ = ∑ j ∈ nonseeds D,
        (if D.trait j = D.trait (D.parent j) then (1 : ℚ) else 0) *
          pWholePastReciprocal D j := by
      apply sum_congr rfl
      intro j hj
      by_cases hm : D.trait j = D.trait (D.parent j) <;>
        simp [matchQ, hm]
    _ = ∑ j ∈ nonseeds D,
        (((laterChildren D j).filter
          (fun k => D.trait k = D.trait (D.parent k))).card : ℚ) /
          (pWholeDenom D j : ℚ) := by
      exact triangular_indicator D
        (fun k => D.trait k = D.trait (D.parent k))
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [later_filter_match_eq]
      rfl

private lemma nonmatch_past_identity (D : Data) :
    (∑ j ∈ nonseeds D, (1 - matchQ D j) * pWholePastReciprocal D j) =
      ∑ j ∈ nonseeds D,
        (nonmatchCount D j : ℚ) / (pWholeDenom D j : ℚ) := by
  calc
    _ = ∑ j ∈ nonseeds D,
        ((if D.trait j ≠ D.trait (D.parent j) then (1 : ℚ) else 0) *
          pWholePastReciprocal D j) := by
      apply sum_congr rfl
      intro j hj
      have hterm : 1 - matchQ D j =
          (if D.trait j ≠ D.trait (D.parent j) then (1 : ℚ) else 0) := by
        by_cases hm : D.trait j = D.trait (D.parent j) <;>
          simp [matchQ, hm]
      rw [hterm]
    _ = ∑ j ∈ nonseeds D,
        (((laterChildren D j).filter
          (fun k => D.trait k ≠ D.trait (D.parent k))).card : ℚ) /
          (pWholeDenom D j : ℚ) :=
      triangular_indicator D
        (fun k => D.trait k ≠ D.trait (D.parent k))
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rfl

private lemma match_partition (D : Data) (j : ℕ) :
    childMatches D j + nonmatchCount D j = (laterChildren D j).card := by
  have hcard := Finset.card_filter_add_card_filter_not (s := laterChildren D j)
    (fun k => D.trait k = D.trait (D.parent k))
  have hmatch : childMatches D j =
      ((laterChildren D j).filter
        (fun k => D.trait k = D.trait (D.parent k))).card := by
    exact congrArg Finset.card (later_filter_match_eq D j).symm
  have hnon : nonmatchCount D j =
      ((laterChildren D j).filter
        (fun k => D.trait k ≠ D.trait (D.parent k))).card := rfl
  rw [hmatch, hnon]
  exact hcard

end

end SAP.P012a.WH.W1.P.T7_L2

open SAP.P012a.WH.W1.P.T7_L2
open Finset
open SAP.P012a
open SAP.P012a.WH.W1

theorem SAP.P012a.WH.W1.T7_L2_proof : SAP.P012a.WH.W1.T7_L2 := by
  intro D hD hN order horder
  have hNpos : 0 < (nonseeds D).card := by
    change 0 < (D.sampled \ D.seeds).card
    rw [Finset.card_sdiff_of_subset hD.1]
    exact Nat.sub_pos_of_lt hN
  have hdenom : ∀ j ∈ nonseeds D, 0 < pWholeDenom D j := by
    intro j hj
    unfold pWholeDenom
    have hjlater : j ∈ laterChildren D j := by
      simp [laterChildren, hj]
    have hcard : 0 < (laterChildren D j).card :=
      Finset.card_pos.mpr ⟨j, hjlater⟩
    omega
  have hdenomQ : ∀ j ∈ nonseeds D, (pWholeDenom D j : ℚ) ≠ 0 := by
    intro j hj
    exact_mod_cast (ne_of_gt (hdenom j hj))
  have horderSet : order.toFinset = D.sampled := horder.2.1
  have hlowRat : pWholeForwardLow D order =
      ∑ j ∈ nonseeds D,
        (matchQ D j - 1 +
          (nonmatchCount D j : ℚ) / (pWholeDenom D j : ℚ)) := by
    classical
    unfold pWholeForwardLow
    have hset : order.toFinset.filter (fun j => j ∈ nonseeds D) = nonseeds D := by
      rw [horderSet]
      ext j
      simp [nonseeds]
    rw [hset]
    change (∑ j ∈ nonseeds D,
        (1 - matchQ D j) * (pWholePastReciprocal D j - 1)) = _
    calc
      _ = (∑ j ∈ nonseeds D,
            (1 - matchQ D j) * pWholePastReciprocal D j) -
          (∑ j ∈ nonseeds D, (1 - matchQ D j)) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        simp
      _ = ∑ j ∈ nonseeds D,
          (matchQ D j - 1 +
            (nonmatchCount D j : ℚ) / (pWholeDenom D j : ℚ)) := by
        rw [nonmatch_past_identity]
        rw [← Finset.sum_sub_distrib]
        apply sum_congr rfl
        intro j hj
        ring
  have hhighRat : pWholeForwardHigh D order =
      ∑ j ∈ nonseeds D,
        (matchQ D j -
          (childMatches D j : ℚ) / (pWholeDenom D j : ℚ)) := by
    classical
    unfold pWholeForwardHigh
    have hset : order.toFinset.filter (fun j => j ∈ nonseeds D) = nonseeds D := by
      rw [horderSet]
      ext j
      simp [nonseeds]
    rw [hset]
    change (∑ j ∈ nonseeds D,
        matchQ D j * (1 - pWholePastReciprocal D j)) = _
    calc
      _ = (∑ j ∈ nonseeds D, matchQ D j) -
          (∑ j ∈ nonseeds D, matchQ D j * pWholePastReciprocal D j) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        simp
      _ = ∑ j ∈ nonseeds D,
          (matchQ D j -
            (childMatches D j : ℚ) / (pWholeDenom D j : ℚ)) := by
        rw [match_past_identity]
        rw [← Finset.sum_sub_distrib]
  have hfinalLow :
      (((pWholeForwardLow D order / ((nonseeds D).card : ℚ) : ℚ) : ℝ) = pLower D) := by
    calc
      ((pWholeForwardLow D order / ((nonseeds D).card : ℚ) : ℚ) : ℝ) =
          (((∑ j ∈ nonseeds D,
            (matchQ D j - 1 + (nonmatchCount D j : ℚ) /
              (pWholeDenom D j : ℚ))) / ((nonseeds D).card : ℚ) : ℚ) : ℝ) := by
        exact congrArg (fun x : ℚ => (x : ℝ))
          (congrArg (fun x : ℚ => x / ((nonseeds D).card : ℚ)) hlowRat)
      _ = pLower D := by
        unfold pLower observedMatch
        push_cast
        congr 1
        apply sum_congr rfl
        intro j hj
        have hnat : childMatches D j + nonmatchCount D j + spare D (D.parent j) =
            pWholeDenom D j := by
          unfold pWholeDenom
          rw [match_partition]
        have hdR : (pWholeDenom D j : ℝ) ≠ 0 := by
          exact_mod_cast ne_of_gt (hdenom j hj)
        have hdenEq : (pWholeDenom D j : ℝ) =
            (childMatches D j : ℝ) + (nonmatchCount D j : ℝ) +
              (spare D (D.parent j) : ℝ) := by
          exact_mod_cast hnat.symm
        have hpartR : (childMatches D j : ℝ) + (nonmatchCount D j : ℝ) =
            (laterChildren D j).card := by
          exact_mod_cast match_partition D j
        have hdSum : (childMatches D j : ℝ) + (nonmatchCount D j : ℝ) +
            (spare D (D.parent j) : ℝ) ≠ 0 := by
          rw [← hdenEq]
          exact hdR
        rw [hdenEq, ← hpartR]
        by_cases hm : D.trait j = D.trait (D.parent j) <;>
          simp [matchQ, hm] <;> field_simp [hdSum] <;> ring
  have hfinalHigh :
      (((pWholeForwardHigh D order / ((nonseeds D).card : ℚ) : ℚ) : ℝ) = pUpper D) := by
    calc
      ((pWholeForwardHigh D order / ((nonseeds D).card : ℚ) : ℚ) : ℝ) =
          (((∑ j ∈ nonseeds D,
            (matchQ D j - (childMatches D j : ℚ) /
              (pWholeDenom D j : ℚ))) / ((nonseeds D).card : ℚ) : ℚ) : ℝ) := by
        exact congrArg (fun x : ℚ => (x : ℝ))
          (congrArg (fun x : ℚ => x / ((nonseeds D).card : ℚ)) hhighRat)
      _ = pUpper D := by
        unfold pUpper observedMatch
        push_cast
        congr 1
        apply sum_congr rfl
        intro j hj
        have hdR : (pWholeDenom D j : ℝ) ≠ 0 := by
          exact_mod_cast ne_of_gt (hdenom j hj)
        have hdenEq : (pWholeDenom D j : ℝ) =
            (laterChildren D j).card + (spare D (D.parent j) : ℝ) := by
          simp [pWholeDenom]
        have hdSum : (laterChildren D j).card +
            (spare D (D.parent j) : ℝ) ≠ 0 := by
          rw [← hdenEq]
          exact hdR
        rw [hdenEq]
        by_cases hm : D.trait j = D.trait (D.parent j) <;>
          simp [matchQ, hm] <;> field_simp [hdSum] <;> ring
  exact ⟨hfinalLow, hfinalHigh⟩

