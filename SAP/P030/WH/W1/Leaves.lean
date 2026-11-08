import SAP.P030.Defs.WholeW1
import SAP.P030.Bridge
import AronowAudit.P030.P030_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030.WH.W1

universe u

open scoped BigOperators
noncomputable section

/- All missing steps in this group are short finite calculations. They are
proved below, so the assemblies require no unproved leaf propositions. -/

/-- The existing rank-weight formula in the package's definition vocabulary. -/
theorem average_rank_sum_form {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    averageRank a i = 1/2 + ∑ j : Fin n,
      ((if a j < a i then 1 else 0) + (if a j = a i then 1/2 else 0)) :=
  AronowAudit.P030.average_rank_weight a i

/-- Evaluate the four-coordinate ranks and the six-row rational certificates.
The distance and outcome vectors come from the existing geometric calculation;
finite rank counts and rational normalization supply the missing details. -/
theorem table_rank_details : TableRankDetails := by
  classical
  have hy : tableY = ![1,3,2,1] := AronowAudit.P030.table_y_vector
  have hd : tableDistances =
      ![![1,6,7,8], ![2,5,6,7], ![3,4,5,6], ![4,3,4,5], ![5,2,3,4], ![6,1,2,3]] :=
    AronowAudit.P030.table_distances
  have hr : tableRho = tableValues := AronowAudit.P030.table_correlations.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [hy]
    funext i
    fin_cases i <;> norm_num [average_rank_sum_form, Fin.sum_univ_succ]
  · rw [hy]
    funext i
    fin_cases i <;> norm_num [centeredRanks, average_rank_sum_form, Fin.sum_univ_succ]
  · intro r
    rw [hd]
    funext i
    fin_cases r <;> fin_cases i <;> norm_num [averageRank, Fin.card_filter_univ_succ]
  · intro r
    rw [hd]
    funext i
    fin_cases r <;> fin_cases i <;>
      norm_num [centeredRanks, averageRank, Fin.card_filter_univ_succ]
  · intro r
    rw [hd, hy]
    fin_cases r <;> norm_num [rankCross, centeredRanks, averageRank,
      Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  · intro r
    rw [hd]
    fin_cases r <;> norm_num [rankSquares, centeredRanks, averageRank,
      Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  · intro r
    rw [hr]
    fin_cases r <;> norm_num [tableValues, div_pow, Real.sq_sqrt]

/-- Transport both tails from the bijective table enumeration to actual
assignments, and count the three strictly ordered statistic values. -/
theorem null_reference_details : NullReferenceDetails := by
  classical
  have hs : ∀ r : Fin 6,
      statistic tenS tenYnull tenG (tenAssignment (tableTreatment r)) = tableRho r :=
    AronowAudit.P030.ten_null_statistic_value
  have href : ∀ r s : Fin 6,
      referenceStatistic tenS tenYnull tenG (tenAssignment (tableTreatment r))
        (tenAssignment (tableTreatment s)) = tableRho s :=
    AronowAudit.P030.ten_null_reference_value
  have he (P : Assignment 10 → Prop) : uniformProbability tableΩ P =
      uniformProbability Finset.univ (fun r : Fin 6 => P (tenAssignment (tableTreatment r))) :=
    AronowAudit.P030.table_enumeration_probability P
  refine ⟨by intros; rfl, by intros; rfl, ?_, ?_, ?_⟩
  · intro r
    rw [tenNullLowerP, he]
    simp only [href, hs]
    exact AronowAudit.P030.table_tail_probabilities.1 r
  · intro r
    rw [tenNullUpperP, he]
    simp only [href, hs]
    exact AronowAudit.P030.table_tail_probabilities.2 r
  · simp only [hs]
    have hu : (Finset.univ : Finset (Fin 6)) = {0,1,2,3,4,5} := by decide
    have hr : tableRho = tableValues := AronowAudit.P030.table_correlations.1
    have ho := AronowAudit.P030.table_value_order
    have hac := ho.1.trans ho.2.1
    have hab : -1 / Real.sqrt 90 ≠ -(5/6 : ℝ) := by
      intro h
      have hlt := ho.2.1
      rw [h] at hlt
      linarith
    have hbc : -(5/6 : ℝ) ≠ -3 / Real.sqrt 10 := by
      intro h
      have hlt := ho.1
      rw [← h] at hlt
      linarith
    norm_num [hu, hr, tableValues, hab, hbc, ne_of_gt hac]

/-- The observed formula example is the last row of the shared rank certificate. -/
theorem observed_rank_details : ObservedRankDetails := by
  rcases table_rank_details with ⟨hy, hcy, hd, hcd, hc, hq, _, _⟩
  exact ⟨hy, hcy, by simpa using hd 5, by simpa using hcd 5,
    by simpa using hc 5, by simpa using hq 5, AronowAudit.P030.table_correlations.2.2⟩

/-- Divide the observed rational products by 4 and 3; the existing
positive-divisor cancellation theorem proves the corrected formula's invariance. -/
theorem observed_moment_details : ObservedMomentDetails := by
  rcases observed_rank_details with ⟨_, _, _, _, hc, hd, hy⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [rankCov, hc]
  · norm_num [hd]
  · norm_num [hy]
  · norm_num [rankCov, hc]
  · norm_num [hd]
  · norm_num [hy]
  · intro r m hm
    have hp : 0 < rankSquares tableY := by rw [hy]; norm_num
    exact (AronowAudit.P030.spearman_divisor (tableDistances r) tableY
      (AronowAudit.P030.table_correlations.2.1 r) hp m hm).symm

/-- Count the two ordering examples' tied ranks and square their already
certified correlations; all remaining comparisons are rational. -/
theorem ordering_rank_details : OrderingRankDetails := by
  rcases AronowAudit.P030.printed_ordering_counterexample with ⟨ha, hb, _, _, _, _⟩
  have ha' : spearman (![1,2,1,1] : Fin 4 → ℝ) tableY = Real.sqrt 6 / 3 := ha
  have hb' : spearman (![0,2,1,1] : Fin 4 → ℝ) tableY = 5/6 := hb
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · funext i
    fin_cases i <;> norm_num [average_rank_sum_form, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;> norm_num [average_rank_sum_form, Fin.sum_univ_succ]
  · rw [ha']
    norm_num [div_pow, Real.sq_sqrt]
  · rw [hb']
    norm_num

/-- Direct three-coordinate rank counts, witnesses of nonconstancy, and a
rational interval for sqrt(3)/2 obtained by squaring its nonnegative root. -/
theorem weak_rank_details : WeakRankDetails := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨0, 2, by norm_num⟩, ⟨0, 2, by norm_num⟩, ?_⟩
  · funext i
    fin_cases i <;> norm_num [average_rank_sum_form, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;> norm_num [average_rank_sum_form, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;> norm_num [centeredRanks, average_rank_sum_form, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;> norm_num [centeredRanks, average_rank_sum_form, Fin.sum_univ_succ]
  · norm_num [rankCross, centeredRanks, averageRank,
      Fin.sum_univ_succ, Fin.card_filter_univ_succ]
  · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hp := Real.sqrt_nonneg (3 : ℝ)
    rw [abs_lt]
    constructor <;> nlinarith

/-- The whole ten-unit size counterexample; all omitted finite certificates
are proved above, and the exact rejection events follow by linear arithmetic. -/
theorem T2_assembly : T2WholeStatement := by
  classical
  have hbase : T2Statement := by
    refine ⟨by intros; rfl, AronowAudit.P030.statistic_invariance_counterexample.1,
      AronowAudit.P030.statistic_invariance_counterexample.2.1,
      Bridge.tableDesign, Bridge.tableNumerics,
      AronowAudit.P030.ten_null_statistic_value, AronowAudit.P030.ten_null_reference_value,
      AronowAudit.P030.table_tail_probabilities.1, AronowAudit.P030.table_tail_probabilities.2,
      AronowAudit.P030.ten_actual_conditional_size, by norm_num⟩
  refine ⟨hbase, table_rank_details, null_reference_details, ?_, ?_⟩
  · intro α h0 h2 r
    rcases null_reference_details with ⟨_, _, hl, hu, _⟩
    have hp1 : printedReject α 1 := Or.inr (by linarith)
    have hp2 : ¬ printedReject α (1/2) := by
      rintro (h | h) <;> linarith
    have hp3 : ¬ printedReject α (1/3) := by
      rintro (h | h) <;> linarith
    have hc1 : ¬ correctedReject α 1 (1/2) := by
      rintro (h | h) <;> linarith
    have hc2 : ¬ correctedReject α (1/2) (2/3) := by
      rintro (h | h) <;> linarith
    have hc3 : ¬ correctedReject α (1/3) 1 := by
      rintro (h | h) <;> linarith
    rw [hl, hu]
    fin_cases r <;> norm_num [hp1, hp2, hp3, hc1, hc2, hc3]
  · intro α h0 hhalf
    have h2 : α ≤ 2/3 := by linarith
    have hsize : uniformProbability tableΩ (fun z => printedReject α (tenNullLowerP z)) = 1/2 :=
      (AronowAudit.P030.ten_actual_conditional_size α h0 h2).1
    rw [hsize]
    exact hhalf

/-- The whole statistic-invariance counterexample, including actual p = 1/3
and the general point-mass consequence of a constant statistic. -/
theorem T5_assembly : T5WholeStatement.{u} := by
  classical
  have hbase : T5Statement.{u} := by
    rcases AronowAudit.P030.statistic_invariance_counterexample with ⟨_, _, _, _, _, _, hp⟩
    refine ⟨by intros; rfl, Bridge.tableDesign, Bridge.tableNumerics,
      Bridge.outcomeNullNonconstant, AronowAudit.P030.ten_null_statistic_value, hp, ?_⟩
    intro A Ω hΩ t ht
    exact AronowAudit.P030.constant_statistic_p_one Ω hΩ t ht
  refine ⟨hbase, table_rank_details, null_reference_details, ?_, by norm_num, ?_⟩
  · simpa [tableTreatment] using null_reference_details.2.2.1 5
  · intro A Ω hΩ t ht z hz
    have he : Ω.filter (fun w => t w = t z) = Ω := by
      apply Finset.filter_eq_self.mpr
      intro w hw
      exact ht w hw z hz
    have hn : (Ω.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hΩ
    change ((Ω.filter (fun w => t w = t z)).card : ℝ) / (Ω.card : ℝ) = 1
    rw [he, div_self hn]

/-- The whole three-part formula and weak-monotonicity counterexample. -/
theorem T8_assembly : T8WholeStatement := by
  rcases AronowAudit.P030.printed_formula_counterexample with ⟨h4, h3, hn, hs, hd⟩
  have h4' : ∀ r : Fin 6, printedRho 4 (tableDistances r) tableY =
      (![-4/45,-4/45,-4/45,-20/27,-4/5,-4/5] : Fin 6 → ℝ) r := h4
  have h3' : ∀ r : Fin 6, printedRho 3 (tableDistances r) tableY =
      (![-1/15,-1/15,-1/15,-5/9,-3/5,-3/5] : Fin 6 → ℝ) r := h3
  have hbase : T8Statement := by
    rcases AronowAudit.P030.printed_ordering_counterexample with ⟨ha, hb, hpa, hpb, hlt, hrev⟩
    exact ⟨Bridge.tableNumerics, h4, h3, hn, hs, hd, Bridge.ordering_variances,
      ha, hb, hpa, hpb, hlt, hrev, Bridge.weakMonotoneExample⟩
  refine ⟨hbase, observed_rank_details, observed_moment_details, ?_,
    ordering_rank_details, weak_rank_details⟩
  rcases table_rank_details with ⟨_, _, _, _, _, _, hsq, _⟩
  exact ⟨by rw [h4']; norm_num, by rw [h3']; norm_num,
    by simpa using hsq 5, by norm_num, by norm_num⟩

/-- The whole actual worked example, including its explicit lower-tail set
and uniqueness of each reference correlation with positive denominators. -/
theorem T14_assembly : T14WholeStatement := by
  classical
  rcases AronowAudit.P030.example_observed_outcomes with ⟨hΨ, hΘ, hY, hF⟩
  rcases AronowAudit.P030.example_observed_statistic_and_p with ⟨hT, hp⟩
  have hbase : T14Statement :=
    ⟨hΨ, hΘ, hY, hF, congrFun AronowAudit.P030.table_distances 5,
      Bridge.tableDesign, Bridge.tableNumerics, AronowAudit.P030.example_reference_rho,
      hT, AronowAudit.P030.worked_table_result.2.2.2.1, hp, by norm_num⟩
  have hy : exampleFixedY = tableY := by
    exact (show exampleFixedY = ![1,3,2,1] from hF).trans
      (show tableY = ![1,3,2,1] from AronowAudit.P030.table_y_vector).symm
  have href : ∀ r : Fin 6, referenceStatistic tenS tenYexample tenG (tenAssignment 6)
      (tenAssignment (tableTreatment r)) = tableRho r := AronowAudit.P030.example_reference_rho
  have ht : statistic tenS tenYexample tenG (tenAssignment 6) = tableRho 5 := href 5
  refine ⟨hbase, ?_, ?_, ?_⟩
  · rw [hy]
    exact table_rank_details.1
  · have htail : ∀ r : Fin 6,
        referenceStatistic tenS tenYexample tenG (tenAssignment 6)
          (tenAssignment (tableTreatment r)) ≤ statistic tenS tenYexample tenG (tenAssignment 6) ↔
            r = 4 ∨ r = 5 := by
      intro r
      rw [href, ht]
      have hr : tableRho = tableValues := AronowAudit.P030.table_correlations.1
      have ho := AronowAudit.P030.table_value_order
      have hac := ho.1.trans ho.2.1
      rw [hr]
      fin_cases r <;> norm_num [tableValues, not_le.mpr hac, not_le.mpr ho.1]
      linarith [ho.1]
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hzle⟩
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hz
      rcases (htail r).mp hzle with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨by simp [tableΩ], (htail 4).mpr (Or.inl rfl)⟩
      · exact ⟨by simp [tableΩ], (htail 5).mpr (Or.inr rfl)⟩
  · intro r
    have hd : 0 < rankSquares (tableDistances r) := AronowAudit.P030.table_correlations.2.1 r
    have hqy : 0 < rankSquares exampleFixedY := by
      rw [hy, show rankSquares tableY = 9/2 from AronowAudit.P030.table_correlations.2.2]
      norm_num
    have hden : Real.sqrt (rankSquares (tableDistances r) * rankSquares exampleFixedY) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hd hqy)).ne'
    have hval : referenceStatistic tenS tenYexample tenG (tenAssignment 6)
        (tenAssignment (tableTreatment r)) = spearman (tableDistances r) exampleFixedY := by
      rw [href, hy]
      rfl
    refine ⟨hd, hqy, ?_, ?_⟩
    · rw [hval]
      exact div_mul_cancel₀ _ hden
    · refine ⟨spearman (tableDistances r) exampleFixedY, div_mul_cancel₀ _ hden, ?_⟩
      intro v hv
      exact (eq_div_iff hden).mpr hv

end
end SAP.P030.WH.W1
