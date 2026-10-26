import AronowAudit.P003.P003_Audit

/-! Finite counterexamples for adaptive testing and confidence-set inversion. -/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

/-! ## Finite candidates, tails, and chronological test traces -/

/-- The common complete-randomization denominator; no assignment-pool enumeration. -/
theorem atr_denominator : binomial 30 15 = 155117520 := by
  decide +kernel

theorem atr_candidates_9 : candidates adaptiveData 9 =
    [⟨1,9,0,20⟩, ⟨2,9,0,19⟩, ⟨3,9,0,18⟩, ⟨3,10,1,16⟩, ⟨3,11,2,14⟩, ⟨3,12,3,12⟩, ⟨3,13,4,10⟩, ⟨3,14,5,8⟩] := by
  decide +kernel

theorem atr_candidates_10 : candidates adaptiveData 10 =
    [⟨1,10,0,19⟩, ⟨2,10,0,18⟩, ⟨3,10,0,17⟩, ⟨3,11,1,15⟩, ⟨3,12,2,13⟩, ⟨3,13,3,11⟩, ⟨3,14,4,9⟩] := by
  decide +kernel

theorem atr_candidates_11 : candidates adaptiveData 11 =
    [⟨1,11,0,18⟩, ⟨2,11,0,17⟩, ⟨3,11,0,16⟩, ⟨3,12,1,14⟩, ⟨3,13,2,12⟩, ⟨3,14,3,10⟩] := by
  decide +kernel

theorem atr_candidates_12 : candidates adaptiveData 12 =
    [⟨1,12,0,17⟩, ⟨2,12,0,16⟩, ⟨3,12,0,15⟩, ⟨3,13,1,13⟩, ⟨3,14,2,11⟩] := by
  decide +kernel

theorem atr_candidates_14 : candidates adaptiveData 14 =
    [⟨1,14,0,15⟩, ⟨2,14,0,14⟩, ⟨3,14,0,13⟩] := by
  decide +kernel

theorem atr_candidates_15 : candidates adaptiveData 15 =
    [⟨1,15,0,14⟩, ⟨2,15,0,13⟩] := by
  decide +kernel

theorem atr_candidates_16 : candidates adaptiveData 16 =
    [⟨1,16,0,13⟩] := by
  decide +kernel

theorem atr_tail_00 : tailCount ⟨1,9,0,20⟩ adaptiveData = 6387648 := by
  decide +kernel

theorem atr_p_00 : pValue ⟨1,9,0,20⟩ adaptiveData = 412/10005 := by
  change (tailCount ⟨1,9,0,20⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_00, atr_denominator]
  norm_num

theorem atr_tail_01 : tailCount ⟨2,9,0,19⟩ adaptiveData = 11659008 := by
  decide +kernel

theorem atr_p_01 : pValue ⟨2,9,0,19⟩ adaptiveData = 752/10005 := by
  change (tailCount ⟨2,9,0,19⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_01, atr_denominator]
  norm_num

theorem atr_tail_02 : tailCount ⟨3,9,0,18⟩ adaptiveData = 16354272 := by
  decide +kernel

theorem atr_p_02 : pValue ⟨3,9,0,18⟩ adaptiveData = 20042/190095 := by
  change (tailCount ⟨3,9,0,18⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_02, atr_denominator]
  norm_num

theorem atr_tail_03 : tailCount ⟨1,10,0,19⟩ adaptiveData = 2705448 := by
  decide +kernel

theorem atr_p_03 : pValue ⟨1,10,0,19⟩ adaptiveData = 349/20010 := by
  change (tailCount ⟨1,10,0,19⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_03, atr_denominator]
  norm_num

theorem atr_tail_04 : tailCount ⟨2,10,0,18⟩ adaptiveData = 5644272 := by
  decide +kernel

theorem atr_p_04 : pValue ⟨2,10,0,18⟩ adaptiveData = 6917/190095 := by
  change (tailCount ⟨2,10,0,18⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_04, atr_denominator]
  norm_num

theorem atr_tail_05 : tailCount ⟨3,10,0,17⟩ adaptiveData = 8743032 := by
  decide +kernel

theorem atr_p_05 : pValue ⟨3,10,0,17⟩ adaptiveData = 7143/126730 := by
  change (tailCount ⟨3,10,0,17⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_05, atr_denominator]
  norm_num

theorem atr_tail_06 : tailCount ⟨3,11,1,15⟩ adaptiveData = 8345544 := by
  decide +kernel

theorem atr_p_06 : pValue ⟨3,11,1,15⟩ adaptiveData = 347731/6463230 := by
  change (tailCount ⟨3,11,1,15⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_06, atr_denominator]
  norm_num

theorem atr_tail_07 : tailCount ⟨3,12,2,13⟩ adaptiveData = 7544198 := by
  decide +kernel

theorem atr_p_07 : pValue ⟨3,12,2,13⟩ adaptiveData = 3772099/77558760 := by
  change (tailCount ⟨3,12,2,13⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_07, atr_denominator]
  norm_num

theorem atr_tail_08 : tailCount ⟨3,13,3,11⟩ adaptiveData = 6358448 := by
  decide +kernel

theorem atr_p_08 : pValue ⟨3,13,3,11⟩ adaptiveData = 397403/9694845 := by
  change (tailCount ⟨3,13,3,11⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_08, atr_denominator]
  norm_num

theorem atr_tail_09 : tailCount ⟨3,14,4,9⟩ adaptiveData = 4832760 := by
  decide +kernel

theorem atr_p_09 : pValue ⟨3,14,4,9⟩ adaptiveData = 103/3306 := by
  change (tailCount ⟨3,14,4,9⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_09, atr_denominator]
  norm_num

theorem atr_tail_10 : tailCount ⟨1,11,0,18⟩ adaptiveData = 1017552 := by
  decide +kernel

theorem atr_p_10 : pValue ⟨1,11,0,18⟩ adaptiveData = 43/6555 := by
  change (tailCount ⟨1,11,0,18⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_10, atr_denominator]
  norm_num

theorem atr_tail_11 : tailCount ⟨2,11,0,17⟩ adaptiveData = 2426512 := by
  decide +kernel

theorem atr_p_11 : pValue ⟨2,11,0,17⟩ adaptiveData = 8921/570285 := by
  change (tailCount ⟨2,11,0,17⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_11, atr_denominator]
  norm_num

theorem atr_tail_12 : tailCount ⟨3,11,0,16⟩ adaptiveData = 4189392 := by
  decide +kernel

theorem atr_p_12 : pValue ⟨3,11,0,16⟩ adaptiveData = 29093/1077205 := by
  change (tailCount ⟨3,11,0,16⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_12, atr_denominator]
  norm_num

theorem atr_tail_13 : tailCount ⟨3,12,1,14⟩ adaptiveData = 3826848 := by
  decide +kernel

theorem atr_p_13 : pValue ⟨3,12,1,14⟩ adaptiveData = 79726/3231615 := by
  change (tailCount ⟨3,12,1,14⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_13, atr_denominator]
  norm_num

theorem atr_tail_14 : tailCount ⟨3,13,2,12⟩ adaptiveData = 3213848 := by
  decide +kernel

theorem atr_p_14 : pValue ⟨3,13,2,12⟩ adaptiveData = 401731/19389690 := by
  change (tailCount ⟨3,13,2,12⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_14, atr_denominator]
  norm_num

theorem atr_tail_15 : tailCount ⟨3,14,3,10⟩ adaptiveData = 2399856 := by
  decide +kernel

theorem atr_p_15 : pValue ⟨3,14,3,10⟩ adaptiveData = 2941/190095 := by
  change (tailCount ⟨3,14,3,10⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_15, atr_denominator]
  norm_num

theorem atr_tail_16 : tailCount ⟨1,12,0,17⟩ adaptiveData = 332112 := by
  decide +kernel

theorem atr_p_16 : pValue ⟨1,12,0,17⟩ adaptiveData = 407/190095 := by
  change (tailCount ⟨1,12,0,17⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_16, atr_denominator]
  norm_num

theorem atr_tail_17 : tailCount ⟨2,12,0,16⟩ adaptiveData = 904992 := by
  decide +kernel

theorem atr_p_17 : pValue ⟨2,12,0,16⟩ adaptiveData = 18854/3231615 := by
  change (tailCount ⟨2,12,0,16⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_17, atr_denominator]
  norm_num

theorem atr_tail_18 : tailCount ⟨3,12,0,15⟩ adaptiveData = 1754232 := by
  decide +kernel

theorem atr_p_18 : pValue ⟨3,12,0,15⟩ adaptiveData = 3847/340170 := by
  change (tailCount ⟨3,12,0,15⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_18, atr_denominator]
  norm_num

theorem atr_tail_19 : tailCount ⟨3,13,1,13⟩ adaptiveData = 1489578 := by
  decide +kernel

theorem atr_p_19 : pValue ⟨3,13,1,13⟩ adaptiveData = 248263/25852920 := by
  change (tailCount ⟨3,13,1,13⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_19, atr_denominator]
  norm_num

theorem atr_tail_20 : tailCount ⟨3,14,2,11⟩ adaptiveData = 1104816 := by
  decide +kernel

theorem atr_p_20 : pValue ⟨3,14,2,11⟩ adaptiveData = 23017/3231615 := by
  change (tailCount ⟨3,14,2,11⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_20, atr_denominator]
  norm_num

theorem atr_tail_21 : tailCount ⟨1,14,0,15⟩ adaptiveData = 19562 := by
  decide +kernel

theorem atr_p_21 : pValue ⟨1,14,0,15⟩ adaptiveData = 9781/77558760 := by
  change (tailCount ⟨1,14,0,15⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_21, atr_denominator]
  norm_num

theorem atr_tail_22 : tailCount ⟨1,15,0,14⟩ adaptiveData = 2972 := by
  decide +kernel

theorem atr_p_22 : pValue ⟨1,15,0,14⟩ adaptiveData = 743/38779380 := by
  change (tailCount ⟨1,15,0,14⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_22, atr_denominator]
  norm_num

theorem atr_tail_23 : tailCount ⟨1,16,0,13⟩ adaptiveData = 240 := by
  decide +kernel

theorem atr_p_23 : pValue ⟨1,16,0,13⟩ adaptiveData = 1/646323 := by
  change (tailCount ⟨1,16,0,13⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [atr_tail_23, atr_denominator]
  norm_num

/-- Rewrite the computational integer acceptance test through its already
proved specification, so the search reduction uses the cached scalar p-values. -/
theorem atr_exactReject_eq (α : ℚ) (v : Counts) (i : ℕ) :
    exactRejectQ α adaptiveData v i = decide (pValue v adaptiveData < α) := by
  unfold exactRejectQ
  by_cases h : α ≤ pValue v adaptiveData
  · rw [(level_accepted_spec α v adaptiveData).mpr h]
    simp only [Bool.not_true, not_lt.mpr h, decide_false]
  · have hf : levelAccepted α v adaptiveData = false := by
      cases he : levelAccepted α v adaptiveData with
      | false => rfl
      | true => exact False.elim (h ((level_accepted_spec α v adaptiveData).mp he))
    rw [hf]
    simp only [Bool.not_false, lt_of_not_ge h, decide_true]

def atr_trace_exact : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,true),
    (⟨2,9,0,19⟩,false),
    (⟨1,12,0,17⟩,true),
    (⟨2,12,0,16⟩,true),
    (⟨3,12,0,15⟩,true),
    (⟨3,13,1,13⟩,true),
    (⟨3,14,2,11⟩,true),
    (⟨1,10,0,19⟩,true),
    (⟨2,10,0,18⟩,true),
    (⟨3,10,0,17⟩,false),
    (⟨1,11,0,18⟩,true),
    (⟨2,11,0,17⟩,true),
    (⟨3,11,0,16⟩,true),
    (⟨3,12,1,14⟩,true),
    (⟨3,13,2,12⟩,true),
    (⟨3,14,3,10⟩,true)]

def atr_trace_low : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,false),
    (⟨1,12,0,17⟩,true),
    (⟨2,12,0,16⟩,true),
    (⟨3,12,0,15⟩,true),
    (⟨3,13,1,13⟩,true),
    (⟨3,14,2,11⟩,true),
    (⟨1,10,0,19⟩,true),
    (⟨2,10,0,18⟩,true),
    (⟨3,10,0,17⟩,false),
    (⟨1,11,0,18⟩,true),
    (⟨2,11,0,17⟩,true),
    (⟨3,11,0,16⟩,true),
    (⟨3,12,1,14⟩,true),
    (⟨3,13,2,12⟩,true),
    (⟨3,14,3,10⟩,true)]

def atr_trace_A : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,false),
    (⟨1,12,0,17⟩,true),
    (⟨2,12,0,16⟩,true),
    (⟨3,12,0,15⟩,true),
    (⟨3,13,1,13⟩,true),
    (⟨3,14,2,11⟩,true),
    (⟨1,10,0,19⟩,true),
    (⟨2,10,0,18⟩,true),
    (⟨3,10,0,17⟩,true),
    (⟨3,11,1,15⟩,true),
    (⟨3,12,2,13⟩,true),
    (⟨3,13,3,11⟩,true),
    (⟨3,14,4,9⟩,true)]

def atr_trace_B : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,true),
    (⟨2,9,0,19⟩,false),
    (⟨1,12,0,17⟩,false),
    (⟨1,14,0,15⟩,false),
    (⟨1,15,0,14⟩,false),
    (⟨1,16,0,13⟩,false)]

def atr_trace_D : List (Counts × Bool) :=
  [
    (⟨1,9,0,20⟩,true),
    (⟨2,9,0,19⟩,true),
    (⟨3,9,0,18⟩,false),
    (⟨1,12,0,17⟩,false),
    (⟨1,14,0,15⟩,false),
    (⟨1,15,0,14⟩,false),
    (⟨1,16,0,13⟩,false)]

theorem atr_run_exact : upperRun false adaptiveData (exactRejectQ (1/20) adaptiveData) =
    ⟨some 10, atr_trace_exact⟩ := by
  change adaptiveSearch 33 false adaptiveData 2 16 (exactRejectQ (1/20) adaptiveData) 2 16 0 = _
  norm_num [adaptiveSearch, runTests, atr_trace_exact, atr_candidates_9, atr_candidates_10,
    atr_candidates_11, atr_candidates_12, atr_candidates_14, atr_candidates_15, atr_candidates_16,
    atr_exactReject_eq, atr_p_00, atr_p_01, atr_p_02, atr_p_03, atr_p_04, atr_p_05, atr_p_06, atr_p_07,
    atr_p_08, atr_p_09, atr_p_10, atr_p_11, atr_p_12, atr_p_13, atr_p_14, atr_p_15, atr_p_16, atr_p_17,
    atr_p_18, atr_p_19, atr_p_20, atr_p_21, atr_p_22, atr_p_23]

theorem atr_run_low : upperRun false adaptiveData (exactRejectQ (1/25) adaptiveData) =
    ⟨some 10, atr_trace_low⟩ := by
  change adaptiveSearch 33 false adaptiveData 2 16 (exactRejectQ (1/25) adaptiveData) 2 16 0 = _
  norm_num [adaptiveSearch, runTests, atr_trace_low, atr_candidates_9, atr_candidates_10, atr_candidates_11,
    atr_candidates_12, atr_candidates_14, atr_candidates_15, atr_candidates_16, atr_exactReject_eq,
    atr_p_00, atr_p_01, atr_p_02, atr_p_03, atr_p_04, atr_p_05, atr_p_06, atr_p_07, atr_p_08, atr_p_09,
    atr_p_10, atr_p_11, atr_p_12, atr_p_13, atr_p_14, atr_p_15, atr_p_16, atr_p_17, atr_p_18, atr_p_19,
    atr_p_20, atr_p_21, atr_p_22, atr_p_23]

theorem atr_run_A : upperRun false adaptiveData (fun _ i => decide (i ≠ 0)) =
    ⟨some 9, atr_trace_A⟩ := by
  change adaptiveSearch 33 false adaptiveData 2 16 (fun _ i => decide (i ≠ 0)) 2 16 0 = _
  norm_num [adaptiveSearch, runTests, atr_trace_A, atr_candidates_9, atr_candidates_10, atr_candidates_11,
    atr_candidates_12, atr_candidates_14, atr_candidates_15, atr_candidates_16]

theorem atr_run_B : upperRun false adaptiveData (fun _ i => decide (i = 0)) =
    ⟨some 16, atr_trace_B⟩ := by
  change adaptiveSearch 33 false adaptiveData 2 16 (fun _ i => decide (i = 0)) 2 16 0 = _
  norm_num [adaptiveSearch, runTests, atr_trace_B, atr_candidates_9, atr_candidates_10, atr_candidates_11,
    atr_candidates_12, atr_candidates_14, atr_candidates_15, atr_candidates_16]

theorem atr_run_D : upperRun false adaptiveData (fun _ i => decide (i < 2)) =
    ⟨some 16, atr_trace_D⟩ := by
  change adaptiveSearch 33 false adaptiveData 2 16 (fun _ i => decide (i < 2)) 2 16 0 = _
  norm_num [adaptiveSearch, runTests, atr_trace_D, atr_candidates_9, atr_candidates_10, atr_candidates_11,
    atr_candidates_12, atr_candidates_14, atr_candidates_15, atr_candidates_16]

theorem atr_traceProbability_pos (ts : List (Counts × Bool))
    (h : ∀ t ∈ ts, (0 : ℚ) <
      (if t.2 then 1-pValue t.1 adaptiveData else pValue t.1 adaptiveData)) :
    0 < traceProbabilityQ adaptiveData ts := by
  unfold traceProbabilityQ
  apply List.prod_pos
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact h t ht

theorem atr_positive_A : 0 < traceProbabilityQ adaptiveData atr_trace_A := by
  apply atr_traceProbability_pos
  intro t ht
  simp only [atr_trace_A, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [atr_p_00, atr_p_01, atr_p_02, atr_p_03, atr_p_04, atr_p_05, atr_p_06, atr_p_07,
    atr_p_08, atr_p_09, atr_p_10, atr_p_11, atr_p_12, atr_p_13, atr_p_14, atr_p_15, atr_p_16, atr_p_17,
    atr_p_18, atr_p_19, atr_p_20, atr_p_21, atr_p_22, atr_p_23]

theorem atr_positive_B : 0 < traceProbabilityQ adaptiveData atr_trace_B := by
  apply atr_traceProbability_pos
  intro t ht
  simp only [atr_trace_B, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [atr_p_00, atr_p_01, atr_p_02, atr_p_03, atr_p_04, atr_p_05, atr_p_06, atr_p_07,
    atr_p_08, atr_p_09, atr_p_10, atr_p_11, atr_p_12, atr_p_13, atr_p_14, atr_p_15, atr_p_16, atr_p_17,
    atr_p_18, atr_p_19, atr_p_20, atr_p_21, atr_p_22, atr_p_23]

theorem atr_positive_D : 0 < traceProbabilityQ adaptiveData atr_trace_D := by
  apply atr_traceProbability_pos
  intro t ht
  simp only [atr_trace_D, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [atr_p_00, atr_p_01, atr_p_02, atr_p_03, atr_p_04, atr_p_05, atr_p_06, atr_p_07,
    atr_p_08, atr_p_09, atr_p_10, atr_p_11, atr_p_12, atr_p_13, atr_p_14, atr_p_15, atr_p_16, atr_p_17,
    atr_p_18, atr_p_19, atr_p_20, atr_p_21, atr_p_22, atr_p_23]

theorem adaptive_trace_counterexample_proof :
    let a := upperRun false adaptiveData (exactRejectQ (1/20) adaptiveData)
    let a' := upperRun false adaptiveData (exactRejectQ (1/25) adaptiveData)
    let bA := upperRun false adaptiveData (fun _ i => decide (i ≠ 0))
    let bB := upperRun false adaptiveData (fun _ i => decide (i = 0))
    let bD := upperRun false adaptiveData (fun _ i => decide (i < 2))
    a.value = some 10 ∧ a'.value = some 10 ∧ a.trace.length = 16 ∧
    bA.value = some 9 ∧ bA.trace[0]!.2 = false ∧ a.trace[0]!.2 = true ∧
    0 < traceProbabilityQ adaptiveData bA.trace ∧
    bB.value = some 16 ∧ bB.trace[0]!.2 = true ∧ a'.trace[0]!.2 = false ∧
    0 < traceProbabilityQ adaptiveData bB.trace ∧
    bD.value = some 16 ∧ bD.trace[0]!.2 = a.trace[0]!.2 ∧
    bD.trace[1]!.2 = true ∧ a.trace[1]!.2 = false ∧
    0 < traceProbabilityQ adaptiveData bD.trace := by
  dsimp only
  rw [atr_run_exact, atr_run_low, atr_run_A, atr_run_B, atr_run_D]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, atr_positive_A,
    rfl, rfl, rfl, atr_positive_B, rfl, rfl, rfl, rfl, atr_positive_D⟩

/-! ## Full inversion independently of the fast search -/

theorem ac_outside_neg14 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (-14 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_neg13 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (-13 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_neg12 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (-12 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_neg11 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (-11 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_neg10 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (-10 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_neg9 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (-9 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_neg8 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (-8 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_neg7 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (-7 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_11 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (11 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_12 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (12 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_13 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (13 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_14 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (14 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_15 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (15 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_outside_16 :
    ((possibleTables adaptiveData).filter (fun v => decide (v.effect = (16 : ℤ)))).all
      (fun v => !(levelAccepted (1/25) v adaptiveData)) = true := by
  decide +kernel

theorem ac_effect_range (v : Counts) (hv : Possible adaptiveData v) :
    -14 ≤ v.effect ∧ v.effect ≤ 16 := by
  have hc := (possible_table_facts adaptiveData v hv).2
  simp only [candidateNumerators, List.mem_map, List.mem_range] at hc
  obtain ⟨k, hk, he⟩ := hc
  norm_num [adaptiveData, Counts.total] at hk he
  omega

theorem ac_bounds_small : endpointBoundsCheck (1/25) adaptiveData (-6) 10 = true := by
  unfold endpointBoundsCheck
  apply List.all_eq_true.mpr
  intro v hv
  by_cases hin : (-6 : ℤ) ≤ v.effect ∧ v.effect ≤ 10
  · simp [hin]
  · have hrange := ac_effect_range v hv
    have hx : v.effect = (-14 : ℤ) ∨ v.effect = (-13 : ℤ) ∨ v.effect = (-12 : ℤ) ∨ v.effect = (-11 : ℤ) ∨ v.effect = (-10 : ℤ) ∨ v.effect = (-9 : ℤ) ∨ v.effect = (-8 : ℤ) ∨ v.effect = (-7 : ℤ) ∨ v.effect = (11 : ℤ) ∨ v.effect = (12 : ℤ) ∨ v.effect = (13 : ℤ) ∨ v.effect = (14 : ℤ) ∨ v.effect = (15 : ℤ) ∨ v.effect = (16 : ℤ) := by omega
    have reject_at (x : ℤ) (he : v.effect = x)
        (hc : ((possibleTables adaptiveData).filter (fun w => decide (w.effect = x))).all
          (fun w => !(levelAccepted (1/25) w adaptiveData)) = true) :
        (!levelAccepted (1/25) v adaptiveData : Bool) = true := by
      apply List.all_eq_true.mp hc v
      exact List.mem_filter.mpr ⟨hv, by simpa only [decide_eq_true_eq] using he⟩
    have hrej : (!levelAccepted (1/25) v adaptiveData : Bool) = true := by
      rcases hx with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
      · exact reject_at (-14) h0 ac_outside_neg14
      · exact reject_at (-13) h1 ac_outside_neg13
      · exact reject_at (-12) h2 ac_outside_neg12
      · exact reject_at (-11) h3 ac_outside_neg11
      · exact reject_at (-10) h4 ac_outside_neg10
      · exact reject_at (-9) h5 ac_outside_neg9
      · exact reject_at (-8) h6 ac_outside_neg8
      · exact reject_at (-7) h7 ac_outside_neg7
      · exact reject_at 11 h8 ac_outside_11
      · exact reject_at 12 h9 ac_outside_12
      · exact reject_at 13 h10 ac_outside_13
      · exact reject_at 14 h11 ac_outside_14
      · exact reject_at 15 h12 ac_outside_15
      · exact reject_at 16 h13 ac_outside_16
    simp only [hrej, Bool.or_true]

/-- Raise the level of an out-of-range rejection certificate. -/
theorem ac_bounds_mono (α β : ℚ) (o : Counts) (lo hi : ℤ) (hαβ : α ≤ β)
    (hc : endpointBoundsCheck α o lo hi = true) :
    endpointBoundsCheck β o lo hi = true := by
  unfold endpointBoundsCheck at hc ⊢
  apply List.all_eq_true.mpr
  intro v hv
  have h := List.all_eq_true.mp hc v hv
  by_cases hin : lo ≤ v.effect ∧ v.effect ≤ hi
  · simp [hin]
  · have hn : (!levelAccepted α v o : Bool) = true := by
      simpa only [hin, decide_false, Bool.false_or] using h
    have hb : levelAccepted β v o = false := by
      cases he : levelAccepted β v o with
      | false => rfl
      | true =>
        have hp : β ≤ pValue v o := (level_accepted_spec β v o).mp he
        have ha : levelAccepted α v o = true :=
          (level_accepted_spec α v o).mpr (le_trans hαβ hp)
        simp only [ha, Bool.not_true, Bool.false_eq_true] at hn
    simp only [hb, Bool.not_false, Bool.or_true]

theorem ac_bounds_large : endpointBoundsCheck (1/20) adaptiveData (-6) 10 = true := by
  exact ac_bounds_mono (1/25) (1/20) adaptiveData (-6) 10 (by norm_num) ac_bounds_small

theorem ac_possible_lower : Possible adaptiveData ⟨3,2,8,17⟩ := by
  decide +kernel

theorem ac_possible_upper : Possible adaptiveData ⟨3,10,0,17⟩ := by
  decide +kernel

theorem ac_tail_lower : tailCount ⟨3,2,8,17⟩ adaptiveData = 8743032 := by
  decide +kernel

theorem ac_p_lower : pValue ⟨3,2,8,17⟩ adaptiveData = 7143/126730 := by
  change (tailCount ⟨3,2,8,17⟩ adaptiveData : ℚ)/(binomial 30 15 : ℚ) = _
  rw [ac_tail_lower, atr_denominator]
  norm_num

theorem ac_endpoint_witnesses (α : ℚ) (hα : α ≤ 1/20) :
    (∃ v, Possible adaptiveData v ∧ α ≤ pValue v adaptiveData ∧ v.effect = -6) ∧
    (∃ v, Possible adaptiveData v ∧ α ≤ pValue v adaptiveData ∧ v.effect = 10) := by
  constructor
  · refine ⟨⟨3,2,8,17⟩, ac_possible_lower, ?_, ?_⟩
    · rw [ac_p_lower]
      exact le_trans hα (by norm_num)
    · norm_num [Counts.effect]
  · refine ⟨⟨3,10,0,17⟩, ac_possible_upper, ?_, ?_⟩
    · rw [atr_p_05]
      exact le_trans hα (by norm_num)
    · norm_num [Counts.effect]

theorem ac_interval_large : intervalQ (1/20) adaptiveData = some (-1/5,1/3) := by
  have hw := ac_endpoint_witnesses (1/20) le_rfl
  have hc := intervalQ_eq_of_endpoint_certificate (1/20) adaptiveData (-6) 10
    ac_bounds_large hw.1 hw.2
  convert hc using 1 <;> norm_num [adaptiveData, Counts.total]

theorem ac_interval_small : intervalQ (1/25) adaptiveData = some (-1/5,1/3) := by
  have hw := ac_endpoint_witnesses (1/25) (by norm_num)
  have hc := intervalQ_eq_of_endpoint_certificate (1/25) adaptiveData (-6) 10
    ac_bounds_small hw.1 hw.2
  convert hc using 1 <;> norm_num [adaptiveData, Counts.total]

theorem adaptivity_counterexample_proof :
    intervalQ (1/20) adaptiveData = some (-1/5,1/3) ∧
    intervalQ (1/25) adaptiveData = some (-1/5,1/3) ∧
    (let a := upperRun false adaptiveData (exactRejectQ (1/20) adaptiveData)
    let a' := upperRun false adaptiveData (exactRejectQ (1/25) adaptiveData)
    let bA := upperRun false adaptiveData (fun _ i => decide (i ≠ 0))
    let bB := upperRun false adaptiveData (fun _ i => decide (i = 0))
    let bD := upperRun false adaptiveData (fun _ i => decide (i < 2))
    a.value = some 10 ∧ a'.value = some 10 ∧ a.trace.length = 16 ∧
    bA.value = some 9 ∧ bA.trace[0]!.2 = false ∧ a.trace[0]!.2 = true ∧
    0 < traceProbabilityQ adaptiveData bA.trace ∧
    bB.value = some 16 ∧ bB.trace[0]!.2 = true ∧ a'.trace[0]!.2 = false ∧
    0 < traceProbabilityQ adaptiveData bB.trace ∧
    bD.value = some 16 ∧ bD.trace[0]!.2 = a.trace[0]!.2 ∧
    bD.trace[1]!.2 = true ∧ a.trace[1]!.2 = false ∧
    0 < traceProbabilityQ adaptiveData bD.trace) := by
  exact ⟨ac_interval_large, ac_interval_small, adaptive_trace_counterexample_proof⟩

end AronowAudit.P003.Wave1
