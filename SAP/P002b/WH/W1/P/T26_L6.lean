import SAP.P002b.WH.W1.P.T26_L6.Part1
import SAP.P002b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace SAP.P002b.WH.W1.P.T26_L6

open SAP.P002b SAP.P002b.WH.W1
open scoped BigOperators ENNReal Matrix
attribute [local instance] Classical.propDecidable
noncomputable section

private def wAssigns : Finset (Finset (Fin 8)) :=
  SAP.P002b.assignments intervalWitnessPopulation.pop

private def allList : List (Finset (Fin 8)) := [({0,1,2,3} : Finset (Fin 8)),  ({0,1,2,4} : Finset (Fin 8)),  ({0,1,2,5} : Finset (Fin 8)),  ({0,1,2,6} : Finset (Fin 8)),  ({0,1,2,7} : Finset (Fin 8)),  ({0,1,3,4} : Finset (Fin 8)),  ({0,1,3,5} : Finset (Fin 8)),  ({0,1,3,6} : Finset (Fin 8)),  ({0,1,3,7} : Finset (Fin 8)),  ({0,1,4,5} : Finset (Fin 8)),  ({0,1,4,6} : Finset (Fin 8)),  ({0,1,4,7} : Finset (Fin 8)),  ({0,1,5,6} : Finset (Fin 8)),  ({0,1,5,7} : Finset (Fin 8)),  ({0,1,6,7} : Finset (Fin 8)),  ({0,2,3,4} : Finset (Fin 8)),  ({0,2,3,5} : Finset (Fin 8)),  ({0,2,3,6} : Finset (Fin 8)),  ({0,2,3,7} : Finset (Fin 8)),  ({0,2,4,5} : Finset (Fin 8)),  ({0,2,4,6} : Finset (Fin 8)),  ({0,2,4,7} : Finset (Fin 8)),  ({0,2,5,6} : Finset (Fin 8)),  ({0,2,5,7} : Finset (Fin 8)),  ({0,2,6,7} : Finset (Fin 8)),  ({0,3,4,5} : Finset (Fin 8)),  ({0,3,4,6} : Finset (Fin 8)),  ({0,3,4,7} : Finset (Fin 8)),  ({0,3,5,6} : Finset (Fin 8)),  ({0,3,5,7} : Finset (Fin 8)),  ({0,3,6,7} : Finset (Fin 8)),  ({0,4,5,6} : Finset (Fin 8)),  ({0,4,5,7} : Finset (Fin 8)),  ({0,4,6,7} : Finset (Fin 8)),  ({0,5,6,7} : Finset (Fin 8)),  ({1,2,3,4} : Finset (Fin 8)),  ({1,2,3,5} : Finset (Fin 8)),  ({1,2,3,6} : Finset (Fin 8)),  ({1,2,3,7} : Finset (Fin 8)),  ({1,2,4,5} : Finset (Fin 8)),  ({1,2,4,6} : Finset (Fin 8)),  ({1,2,4,7} : Finset (Fin 8)),  ({1,2,5,6} : Finset (Fin 8)),  ({1,2,5,7} : Finset (Fin 8)),  ({1,2,6,7} : Finset (Fin 8)),  ({1,3,4,5} : Finset (Fin 8)),  ({1,3,4,6} : Finset (Fin 8)),  ({1,3,4,7} : Finset (Fin 8)),  ({1,3,5,6} : Finset (Fin 8)),  ({1,3,5,7} : Finset (Fin 8)),  ({1,3,6,7} : Finset (Fin 8)),  ({1,4,5,6} : Finset (Fin 8)),  ({1,4,5,7} : Finset (Fin 8)),  ({1,4,6,7} : Finset (Fin 8)),  ({1,5,6,7} : Finset (Fin 8)),  ({2,3,4,5} : Finset (Fin 8)),  ({2,3,4,6} : Finset (Fin 8)),  ({2,3,4,7} : Finset (Fin 8)),  ({2,3,5,6} : Finset (Fin 8)),  ({2,3,5,7} : Finset (Fin 8)),  ({2,3,6,7} : Finset (Fin 8)),  ({2,4,5,6} : Finset (Fin 8)),  ({2,4,5,7} : Finset (Fin 8)),  ({2,4,6,7} : Finset (Fin 8)),  ({2,5,6,7} : Finset (Fin 8)),  ({3,4,5,6} : Finset (Fin 8)),  ({3,4,5,7} : Finset (Fin 8)),  ({3,4,6,7} : Finset (Fin 8)),  ({3,5,6,7} : Finset (Fin 8)),  ({4,5,6,7} : Finset (Fin 8))]  

lemma assignment_card_four (R : Finset (Fin 8))
    (hR : R ∈ SAP.P002b.assignments intervalWitnessPopulation.pop) : R.card = 4 := by
  have hm : R ∈ Finset.univ.powersetCard 4 := by
    simpa [SAP.P002b.assignments, intervalWitnessPopulation] using hR
  exact (Finset.mem_powersetCard.mp hm).2
lemma assignment_rank (R : Finset (Fin 8))
    (hR : R ∈ SAP.P002b.assignments intervalWitnessPopulation.pop) :
    (gram intervalWitnessPopulation.x R).det ≠ 0 ∧
    (gram intervalWitnessPopulation.x Rᶜ).det ≠ 0 := by
  have h4 := assignment_card_four R hR
  have h4c : Rᶜ.card = 4 := by
    rw [Finset.card_compl, h4]
    norm_num
  have hn : R.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    simp [he] at h4
  have hnc : Rᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    simp [he] at h4c
  constructor
  · have hp : 0 < (gram intervalWitnessPopulation.x R).det := by
      simpa only [witness_x_eq] using det_pos R h4
    exact ne_of_gt hp
  · have hp : 0 < (gram intervalWitnessPopulation.x Rᶜ).det := by
      simpa only [witness_x_eq] using det_pos Rᶜ h4c
    exact ne_of_gt hp
private theorem allVarPos_m12 : allList.all (fun A => decide (0 < rVariance A (fun i => qY i-(-12:ℚ)*qD i))) = true := by
  norm_num [allList, rVariance, rrss, rintercept, rslope, rmean, rsum, rcard, qX, qY, qD, Fin.sum_univ_succ]
private theorem allVarPos_10 : allList.all (fun A => decide (0 < rVariance A (fun i => qY i-(10:ℚ)*qD i))) = true := by
  norm_num [allList, rVariance, rrss, rintercept, rslope, rmean, rsum, rcard, qX, qY, qD, Fin.sum_univ_succ]
private theorem allVarPos_m7 : allList.all (fun A => decide (0 < rVariance A (fun i => qY i-(-7:ℚ)*qD i))) = true := by
  norm_num [allList, rVariance, rrss, rintercept, rslope, rmean, rsum, rcard, qX, qY, qD, Fin.sum_univ_succ]
private theorem allList_to_assigns : allList.toFinset = SAP.P002b.assignments intervalWitnessPopulation.pop := by decide
private theorem list_mem_of_assign (R : Finset (Fin 8))
    (hR : R ∈ SAP.P002b.assignments intervalWitnessPopulation.pop) : R ∈ allList := by
  have hm : R ∈ allList.toFinset := by rw [allList_to_assigns]; exact hR
  exact List.mem_toFinset.mp hm
lemma variance_pos_assign (R : Finset (Fin 8))
    (hR : R ∈ SAP.P002b.assignments intervalWitnessPopulation.pop)
    (b : ℚ) (hb : b = -12 ∨ b = 10 ∨ b = -7) :
    0 < rVariance R (fun i => qY i-b*qD i) := by
  have hmem := list_mem_of_assign R hR
  rcases hb with hb | hb | hb
  · subst b
    exact of_decide_eq_true (List.all_eq_true.mp allVarPos_m12 R hmem)
  · subst b
    exact of_decide_eq_true (List.all_eq_true.mp allVarPos_10 R hmem)
  · subst b
    exact of_decide_eq_true (List.all_eq_true.mp allVarPos_m7 R hmem)
lemma score_order_assign (R : Finset (Fin 8))
    (hR : R ∈ SAP.P002b.assignments intervalWitnessPopulation.pop)
    (b : ℚ) (hb : b = -12 ∨ b = 10 ∨ b = -7) :
    (rScore R (fun i => qY i-b*qD i) <
      rScore intervalWitnessAssignment (fun i => qY i-b*qD i)) ↔
    (adjustedAR intervalWitnessPopulation
      (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment) R <
     adjustedAR intervalWitnessPopulation
      (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment) intervalWitnessAssignment) := by
  have hrankR := assignment_rank R hR
  have hS : intervalWitnessAssignment ∈ SAP.P002b.assignments intervalWitnessPopulation.pop := by decide
  have hrankS := assignment_rank intervalWitnessAssignment hS
  have h4R := assignment_card_four R hR
  have h4S := assignment_card_four intervalWitnessAssignment hS
  have h4cR : Rᶜ.card = 4 := by rw [Finset.card_compl, h4R]; norm_num
  have h4cS : intervalWitnessAssignmentᶜ.card = 4 := by rw [Finset.card_compl, h4S]; norm_num
  have hAcR : Rᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he; rw [he] at h4cR; norm_num at h4cR
  have hAcS : intervalWitnessAssignmentᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he; rw [he] at h4cS; norm_num at h4cS
  have hAR : R.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he; rw [he] at h4R; norm_num at h4R
  have hAS : intervalWitnessAssignment.Nonempty := by decide
  have hvR := variance_pos_assign R hR b hb
  have hvS := variance_pos_assign intervalWitnessAssignment hS b hb
  rw [observedW_cast]
  exact stat_order R intervalWitnessAssignment (fun i => qY i-b*qD i)
    hAR hAcR hAS hAcS hrankR.1 hrankR.2 hrankS.1 hrankS.2 hvR hvS

private def rscore (A : Finset (Fin 8)) (b : ℚ) : ℚ :=
  let q := fun i => qY i-b*qD i
  (rintercept A false q-rintercept A true q)^2 /
    ((rrss A false q+rrss A true q)/16)
private def lowerAssignments (b : ℚ) : Finset (Finset (Fin 8)) :=
  wAssigns.filter fun A => rscore A b < rscore intervalWitnessAssignment b
private def lessList (b : ℚ) : List (Finset (Fin 8)) :=
  allList.filter fun A => rscore A b < rscore intervalWitnessAssignment b

private theorem allList_nodup : allList.Nodup := by decide

private theorem filter_card_eq_length (p : Finset (Fin 8) → Prop) [DecidablePred p] :
    (wAssigns.filter p).card = (allList.filter p).length := by
  change ((SAP.P002b.assignments intervalWitnessPopulation.pop).filter p).card = _
  have heq : SAP.P002b.assignments intervalWitnessPopulation.pop = allList.toFinset :=
    allList_to_assigns.symm
  rw [heq, List.filter_toFinset]
  rw [List.toFinset_card_of_nodup (allList_nodup.filter p)]

private theorem count_m12 : (lowerAssignments (-12)).card = 24 := by
  unfold lowerAssignments
  rw [filter_card_eq_length]
  change (lessList (-12)).length = 24
  norm_num [lessList, allList, rscore, rintercept, rslope, rmean, rrss, rsum, rcard, qX, qY, qD, intervalWitnessAssignment, Fin.sum_univ_succ]

private theorem count_p10 : (lowerAssignments (10)).card = 34 := by
  unfold lowerAssignments
  rw [filter_card_eq_length]
  change (lessList (10)).length = 34
  norm_num [lessList, allList, rscore, rintercept, rslope, rmean, rrss, rsum, rcard, qX, qY, qD, intervalWitnessAssignment, Fin.sum_univ_succ]

private theorem count_m7 : (lowerAssignments (-7)).card = 38 := by
  unfold lowerAssignments
  rw [filter_card_eq_length]
  change (lessList (-7)).length = 38
  norm_num [lessList, allList, rscore, rintercept, rslope, rmean, rrss, rsum, rcard, qX, qY, qD, intervalWitnessAssignment, Fin.sum_univ_succ]

private theorem wAssigns_card : wAssigns.card = 70 := by
  change (SAP.P002b.assignments intervalWitnessPopulation.pop).card = 70
  rw [← allList_to_assigns, List.toFinset_card_of_nodup allList_nodup]
  norm_num [allList]

private theorem actual_filter_eq (b : ℚ) (hb : b = -12 ∨ b = 10 ∨ b = -7) :
    wAssigns.filter (fun R =>
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment) R <
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment)
        intervalWitnessAssignment) = lowerAssignments b := by
  unfold lowerAssignments
  apply Finset.filter_congr
  intro R hR
  have hR' : R ∈ SAP.P002b.assignments intervalWitnessPopulation.pop := by
    simpa [wAssigns] using hR
  have ho := score_order_assign R hR' b hb
  simpa [rscore, rScore, rTau, rVariance] using ho.symm


private theorem probability_lt_half (b : ℚ) (hb : b = -12 ∨ b = 10 ∨ b = -7)
    {n : ℕ} (count : (lowerAssignments b).card = n) (hn : n < 35) :
    SAP.P002b.probability intervalWitnessPopulation.pop (fun R =>
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment) R <
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment)
        intervalWitnessAssignment) < 1/2 := by
  change (((wAssigns.filter (fun R =>
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment) R <
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment)
        intervalWitnessAssignment)).card : ℝ) / (wAssigns.card:ℝ)) < 1/2
  rw [actual_filter_eq b hb, count, wAssigns_card]
  have hnR : (n:ℝ) < 35 := by exact_mod_cast hn
  calc
    (n:ℝ) / 70 < 35 / 70 := div_lt_div_of_pos_right hnR (by norm_num)
    _ = (1:ℝ) / 2 := by norm_num

private theorem probability_not_lt_half (b : ℚ) (hb : b = -12 ∨ b = 10 ∨ b = -7)
    {n : ℕ} (count : (lowerAssignments b).card = n) (hn : 35 < n) :
    ¬ SAP.P002b.probability intervalWitnessPopulation.pop (fun R =>
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment) R <
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment)
        intervalWitnessAssignment) < 1/2 := by
  intro hp
  change (((wAssigns.filter (fun R =>
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment) R <
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (b:ℝ) intervalWitnessAssignment)
        intervalWitnessAssignment)).card : ℝ) / (wAssigns.card:ℝ)) < 1/2 at hp
  rw [actual_filter_eq b hb, count, wAssigns_card] at hp
  have hmul : (n:ℝ) < (1/2:ℝ) * 70 :=
    (div_lt_iff₀ (by norm_num : (0:ℝ) < 70)).mp hp
  norm_num at hmul
  have hnR : (35:ℝ) < n := by exact_mod_cast hn
  linarith

end
end SAP.P002b.WH.W1.P.T26_L6

open SAP.P002b.WH.W1.P.T26_L6

theorem SAP.P002b.WH.W1.T26_L6_proof : SAP.P002b.WH.W1.T26_L6 := by
  intro h3
  have hvalid : ValidDesign intervalWitnessPopulation.pop := by
    norm_num [ValidDesign, intervalWitnessPopulation]
  have hS : intervalWitnessAssignment ∈ SAP.P002b.assignments intervalWitnessPopulation.pop := by decide
  have hlevel : (0 < (1/2:ℝ) ∧ (1/2:ℝ) < 1) := by norm_num
  have hrank := h3 intervalWitnessPopulation.pop intervalWitnessAssignment (1/2:ℝ) hvalid hS hlevel
  refine ⟨?_, ?_, ?_⟩
  · change adjustedAR intervalWitnessPopulation
      (observedW intervalWitnessPopulation.pop (-12:ℝ) intervalWitnessAssignment)
      intervalWitnessAssignment ≤
      quantile intervalWitnessPopulation.pop
        (adjustedAR intervalWitnessPopulation
          (observedW intervalWitnessPopulation.pop (-12:ℝ) intervalWitnessAssignment)) (1/2)
    apply (hrank (fun R => adjustedAR intervalWitnessPopulation
      (observedW intervalWitnessPopulation.pop (-12:ℝ) intervalWitnessAssignment) R)).1.mpr
    have hp := probability_lt_half (-12) (Or.inl rfl) (n := 24) count_m12 (by norm_num)
    have halpha : (1:ℝ) - (1/2:ℝ) = 1/2 := by norm_num
    rw [halpha]
    convert hp using 1 <;> norm_num
  · change adjustedAR intervalWitnessPopulation
      (observedW intervalWitnessPopulation.pop (10:ℝ) intervalWitnessAssignment)
      intervalWitnessAssignment ≤
      quantile intervalWitnessPopulation.pop
        (adjustedAR intervalWitnessPopulation
          (observedW intervalWitnessPopulation.pop (10:ℝ) intervalWitnessAssignment)) (1/2)
    apply (hrank (fun R => adjustedAR intervalWitnessPopulation
      (observedW intervalWitnessPopulation.pop (10:ℝ) intervalWitnessAssignment) R)).1.mpr
    have hp := probability_lt_half 10 (Or.inr (Or.inl rfl)) (n := 34) count_p10 (by norm_num)
    have halpha : (1:ℝ) - (1/2:ℝ) = 1/2 := by norm_num
    rw [halpha]
    convert hp using 1 <;> norm_num
  · intro hmem
    have hacc : adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (-7:ℝ) intervalWitnessAssignment)
        intervalWitnessAssignment ≤
      quantile intervalWitnessPopulation.pop
        (adjustedAR intervalWitnessPopulation
          (observedW intervalWitnessPopulation.pop (-7:ℝ) intervalWitnessAssignment)) (1/2) := by
      change adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (-7:ℝ) intervalWitnessAssignment)
        intervalWitnessAssignment ≤
        quantile intervalWitnessPopulation.pop
          (adjustedAR intervalWitnessPopulation
            (observedW intervalWitnessPopulation.pop (-7:ℝ) intervalWitnessAssignment)) (1/2) at hmem
      exact hmem
    have hp := (hrank (fun R => adjustedAR intervalWitnessPopulation
      (observedW intervalWitnessPopulation.pop (-7:ℝ) intervalWitnessAssignment) R)).1.mp hacc
    have hnot := probability_not_lt_half (-7) (Or.inr (Or.inr rfl)) (n := 38) count_m7 (by norm_num)
    have halpha : (1:ℝ) - (1/2:ℝ) = 1/2 := by norm_num
    rw [halpha] at hp
    have hprob : SAP.P002b.probability intervalWitnessPopulation.pop (fun R =>
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (-7:ℝ) intervalWitnessAssignment) R <
      adjustedAR intervalWitnessPopulation
        (observedW intervalWitnessPopulation.pop (-7:ℝ) intervalWitnessAssignment)
        intervalWitnessAssignment) < 1/2 := by
      convert hp using 1 <;> norm_num
    exact hnot (by convert hprob using 1 <;> norm_num)
