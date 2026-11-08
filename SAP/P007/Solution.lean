import SAP.P007.Defs
import SAP.P007.Bridge
import AronowAudit.P007.P007_StateFailure
import AronowAudit.P007.P007_Probability
import SAP.P007.WH.W1.Proofs.T10
import SAP.P007.WH.W2.Proofs.T10

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

open SAP.P007 SAP.P007.Bridge AronowAudit.P007
open Filter Topology
open scoped BigOperators

theorem SAP.P007.T1 : SAP.P007.T1Statement := by
  refine ⟨?_, supportingLine, supportingLine_equality, denominatorValue, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    refine ⟨uniform_retention_counting_identity m (by norm_num) (by norm_num), ?_⟩
    intro h
    exact ⟨numeratorLowerBound (stateFailureRowCounts m) h,
      fourVariablesCannotLoseMoreThan99Percent m h⟩
  · rw [supportingLine_equality.1, supportingLine_equality.2.2]; norm_num
  all_goals norm_num [supportingLine_equality.1, supportingLine_equality.2.2]

theorem SAP.P007.T2 : SAP.P007.T2Statement := by
  refine ⟨logged_missing_count_unique, stateFailure_corrected_average, ?_, ?_, archived_simulation_threshold⟩
  · intro m hfull hlog
    rcases logged_mask_correction m hfull hlog with ⟨hA, hafter, hobs, hmean, hlo, hhi, hloss, hlt⟩
    refine ⟨hA, hafter, hobs, ?_, hmean, hlo, hhi, ?_, hloss, hlt⟩
    · rw [missingAverage_eq, columnAverage_count_identity, hA]; norm_num
    · rw [missingAverage_eq, hmean]; norm_num
  · intro m h
    exact (fourVariablesCannotLoseMoreThan99Percent m h).2.2

theorem SAP.P007.T3 : SAP.P007.T3Statement := by
  have hz := zero_bound_counterexample
  exact ⟨⟨fromAudit nullFirstLaw, nullFirst_weights, hz.1, hz.2.1, nullFirst_prefixes.1,
    nullFirst_prefixes.2.1, hz.2.2⟩,
    ⟨fromAudit fullyMissingLaw, fullyMissing_weights, fun _ h0 h1 => fully_missing_all_bounds h0 h1⟩⟩

theorem SAP.P007.T4 : SAP.P007.T4Statement := by
  rcases null_prefix_counterexample with ⟨hi, hb, h1, h2, hv, hlt, hpow, hp⟩
  rcases later_null_counterexample with ⟨hi', hb', hs, hp', h49⟩
  refine ⟨⟨fromAudit nullFirstLaw, nullFirst_weights, hi, hb, h1, h2, hv, hlt, hpow,
    zero_bound_counterexample.2.2.2.2.1, hp⟩,
    ⟨fromAudit laterNullLaw, laterNull_weights, hi', hb', ?_, hp', h49⟩⟩
  intro i
  refine ⟨(hs i).1, (hs i).2.1, (hs i).2.2, ?_, ?_, ?_⟩ <;>
    norm_num [survival_eq, to_from, (hs i).1, (hs i).2.1, (hs i).2.2]

theorem SAP.P007.T5 : SAP.P007.T5Statement := by
  intro n h hn hh L q hb
  let A := toAudit L
  refine ⟨?_, fun i => prefix_zero A i, fun i j hj => prefix_step A hb i hj, ?_, ?_, ?_⟩
  · intro hz; subst q
    exact ⟨fun i => zero_bound_first_missing A hh hb i,
      zero_bound_all_deleted A hh hb⟩
  · intro i j hj hz
    have hu : survival L i (j + 1) ≤ survival L i j * q := prefix_step A hb i hj
    rw [hz, zero_mul] at hu
    exact le_antisymm hu (probability_nonneg A _)
  · intro i
    have hs : survival L i h ≤ q^h := prefix_survival_bound A hb i le_rfl
    refine ⟨?_, repaired_chain_product A i h, fun j hj => repairedConditional_bounds A hb i hj,
      hs, sub_le_sub_left hs 1⟩
    change repairedConditional A i 0 = prefixSurvival A i 1
    simp [repairedConditional, prefix_zero]
  · intro hi
    exact ⟨independent_rows_product A hi, lemma3 A hn hh hi hb⟩

theorem SAP.P007.T6 : SAP.P007.T6Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n h _ hh q h0 h1
    exact bernoulli_sandwich h0 h1 hh
  · intro n h hn hh L q hi hb
    refine ⟨deletion_probability_sandwich (toAudit L) hn hh hi hb, ?_, ?_⟩
    · intro hz; subst q
      exact (zero_bound_all_deleted (toAudit L) hh hb).1
    · intro hq
      exact logarithm_decay_identity hq hn h
  · intro n hn
    exact ⟨(groups_are_not_variables hn).1, (groups_are_not_variables hn).2,
      by simp [mul_comm]⟩

theorem SAP.P007.T7 : SAP.P007.T7Statement := by
  rcases floor_is_not_first_crossing with ⟨h2, h3, hl, hu, hr2, hr3, hf, hc, hne, _, _, he⟩
  rcases figure4_printed_worked_counterexamples with ⟨_, _, he33, hl33, hu34, _, _, he952, hl952, hu953⟩
  rcases lower_bound_is_not_upper_guarantee with ⟨_, _, hb2, hb2le, ha2, ha2gt,
    _, _, hb16, hb16lt, hb17gt, ha16, ha16gt⟩
  have hw := figure4_corrected_worked_values
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1⟩
  · apply equalModel_of_audit 1 2 (3/4) (by norm_num) (by norm_num)
    refine ⟨h2, h3, hl, hu, hr2, hr3, hf, hc, hne, he, ?_, ?_, ?_⟩
    · intro k
      simpa only [lowerBound_eq, hf] using (threshold_floor_ceiling (n:=1) (by norm_num)
        (by norm_num : (0 : ℝ)<3/4) (by norm_num) (by norm_num : (0 : ℝ)<1/2) (by norm_num)).1 k
    · intro k
      simpa only [lowerBound_eq, hc] using (threshold_floor_ceiling (n:=1) (by norm_num)
        (by norm_num : (0 : ℝ)<3/4) (by norm_num) (by norm_num : (0 : ℝ)<1/2) (by norm_num)).2.1 k
    · exact (threshold_unique_solution (n:=1) (by norm_num) (by norm_num : (0 : ℝ)<3/4)
        (by norm_num) (by norm_num : (0 : ℝ)<1/2) (by norm_num)).2.1
  · apply equalModel_of_audit 10000 33 (3/4) (by norm_num) (by norm_num)
    exact ⟨he33, hl33, hu34⟩
  · apply equalModel_of_audit 10000 952 (99/100) (by norm_num) (by norm_num)
    exact ⟨he952, hl952, hu953⟩
  · exact unequalModel_of_audit 1 2 _ ⟨hb2, hb2le, ha2, ha2gt⟩
  · have hr := adjacent_bracket_rounding (n:=1) (by norm_num) (q:=3/4) (a:=99/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) 16 hb16lt hb17gt
    exact unequalModel_of_audit 1 16 _ ⟨hb16, hb16lt, hb17gt, ha16, ha16gt, hr⟩
  · exact unequalModel_of_audit 10000 33 _
      ⟨unequalProbability_all 10000 33 (by norm_num), printed_parameters_actual_deletion_high.2.2.1,
        by norm_num,
        printed_parameters_actual_deletion_high.2.2.2, figure4_printed_lower_bound_not_upper.2.2.1⟩

theorem SAP.P007.T8 : SAP.P007.T8Statement := by
  refine ⟨?_, figure4_corrected_worked_values,
    ⟨figure4_numeric_33.2.2, figure4_numeric_34, figure4_numeric_952.2.2, figure4_numeric_953⟩, ?_⟩
  · intro n hn q a hq0 hq1 ha0 ha1
    refine ⟨bestCase_increasing hn hq0 hq1, threshold_unique_solution hn hq0 hq1 ha0 ha1,
      threshold_integer_inversion hn hq0 hq1 ha0 ha1, threshold_floor_ceiling hn hq0 hq1 ha0 ha1,
      threshold_rounding_gap hn hq0 hq1 ha0 ha1, ?_, ?_, ?_⟩
    · intro k hk L hi hb
      have hl : lowerBound n q k ≤ allDeleted L := lemma3 (toAudit L) hn hk hi hb
      refine ⟨hl, ?_⟩
      intro hc
      have ha : a ≤ lowerBound n q k := ((threshold_floor_ceiling hn hq0 hq1 ha0 ha1).2.1 k).mpr hc
      exact ⟨ha, ha.trans hl⟩
    · intro k hk hr
      have he := (threshold_probability_guarantee hn hq0 hq1 ha0 ha1).2 k hk hr
      exact equalModel_of_audit n k q hq0.le hq1 _ he.2.2
    · intro k _
      exact equalModel_of_audit n k q hq0.le hq1 _ (bestCase_attained n k q hq0.le hq1).2.2
  · have h := lower_bound_is_not_upper_guarantee
    exact unequalModel_of_audit 1 2 _ ⟨h.2.2.2.1, h.2.2.2.2.2.1⟩

theorem SAP.P007.T9 : SAP.P007.T9Statement := by
  rcases figure5_upper_bound_counterexample with ⟨hi, hb, hmin, hd, hf, he, hlt, hbe, hbne, hp⟩
  refine ⟨fromAudit figure5Witness, rfl, hi, hb, hmin, ?_, hd, hf, he, hlt, hbe, hbne, hp⟩
  intro i
  have hs := figure5Witness_prefixes i
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [survival_eq, to_from, hs.1, hs.2]

theorem SAP.P007.T10 : SAP.P007.T10WholeStatement_W2 := SAP.P007.WH.W2.T10_whole

theorem SAP.P007.T11 : SAP.P007.T11Statement := by
  refine ⟨?_, fromAudit nonidenticalRowsWitness, rfl, mutually_independent_need_not_be_iid⟩
  intro n k _ _ L hi
  exact independent_rows_product (toAudit L) hi

theorem SAP.P007.T12 : SAP.P007.T12Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n K d hn hK m hfull
    exact removing_fully_missing_columns hn hK m hfull
  · intro m hfull hlo hhi
    have hp := removing_fully_missing_columns (by norm_num : 0<8580) (by norm_num : 0<1205) m hfull
    have hb := printed_average_cannot_be_retained hlo hhi hp.2.2.2.1
    exact ⟨hb.1, by norm_num, hb.2⟩
  · intro m hfull hA
    have hp := removing_fully_missing_columns (by norm_num : 0<8580) (by norm_num : 0<1205) m hfull
    have hA' : missingCells m = 7019387 := hA
    have hb : missingAverage m = (7019387 : ℝ)/10501920 := by
      convert hp.2.1 using 1 <;> norm_num [hA', missingAverage_eq]
    have ha : missingAverage (fun i j => m i (Sum.inl j)) = (6856367 : ℝ)/10338900 := by
      convert hp.2.2.1 using 1 <;> norm_num [hA', missingAverage_eq]
    rcases stateFailure_corrected_average with ⟨_, _, _, _, _, hlo, hhi, _, _, _⟩
    refine ⟨hb, ha, ?_, ?_, ?_⟩
    · rw [ha]; exact hlo
    · rw [ha]; exact hhi
    · rw [hb, ha]; exact stateFailure_average_overstatement

theorem SAP.P007.T14 : SAP.P007.T14Statement := by
  intro n k hn hk L q hi hb
  exact lemma3 (toAudit L) hn hk hi hb

theorem SAP.P007.T15 : SAP.P007.T15Statement := by
  intro n g hn hg L q hi hb
  exact lemma8 (toAudit L) hn hg hi hb

theorem SAP.P007.T16 : SAP.P007.T16Statement := by
  intro k L hk q h0 h1 hi hb hs
  exact proposition5 (fun n => toAudit (L n)) hk h0 h1 hi hb hs

theorem SAP.P007.T17 : SAP.P007.T17Statement := by
  intro g L hg q h0 h1 hi hb hs
  exact proposition10 (fun n => toAudit (L n)) hg h0 h1 hi hb hs
