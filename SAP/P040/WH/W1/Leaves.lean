import SAP.P040.Defs.WholeW1
import SAP.P040.Bridge
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B2
import AronowAudit.P053.P053_NormalQuantiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040.WH.W1

open scoped BigOperators

noncomputable section

/-- No new mathematical leaves are required. The P040 bridge supplies the finite
binomial results. Transport the P033 Gaussian quantile certificate using
`ProbabilityTheory.cdf_eq_real`; strict monotonicity supplies uniqueness and
identifies its defining set with an upper ray. Short square-root comparisons
certify the actual-quantile endpoints. All remaining steps are finite-sum,
rounding, complement, or coverage glue. -/
theorem T1_assembly : T1WholeStatement := by
  have hbase : T1Statement := by
    refine ⟨Bridge.observed_count_mass.1, Bridge.observed_count_mass.2,
      ⟨Bridge.method_free_counterexample, Bridge.lower_bound_counterexample⟩,
      Bridge.printed_endpoint_excludes_witness.1, Bridge.printed_endpoint_excludes_witness.2,
      Bridge.printed_wald_arithmetic, ?_⟩
    intro z hlo hhi
    have hc := Bridge.wald_coverage_counterexample z hlo hhi
    have hf := Bridge.wald_lower_failure_probability z hlo hhi
    refine ⟨?_, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hf.1, hf.2.1, hf.2.2⟩
    intro k
    exact ⟨Bridge.wald_witness_membership z hlo hhi k,
      Bridge.wald_membership_sq z (by linarith) (4 / 5) k,
      Bridge.wald_lower_membership z hlo hhi k⟩
  have hqeq : T1NormalQuantile = AronowAudit.P033.normalCritical := by
    simp only [T1NormalQuantile, T1NormalCDF, AronowAudit.P033.normalCritical,
      AronowAudit.P033.normalQuantile, AronowAudit.P033.normalCDF,
      ProbabilityTheory.cdf_eq_real]
  have hqvalue : T1NormalCDF T1NormalQuantile = (39 / 40 : ℝ) := by
    rw [hqeq]
    simpa only [T1NormalCDF, AronowAudit.P033.normalCDF,
      ProbabilityTheory.cdf_eq_real] using
        AronowAudit.P033.Wave1.native_power_correction_critical_cdf
  have hqtight :
      (195996398454005 / 10 ^ 14 : ℝ) < T1NormalQuantile ∧
      T1NormalQuantile < (195996398454006 / 10 ^ 14 : ℝ) := by
    rw [hqeq]
    exact AronowAudit.P033.Wave1.binary_standardization.critical_bounds
  have hqrange : T1NormalQuantile ∈
      Set.Icc (19599 / 10000 : ℝ) (19601 / 10000) := by
    constructor <;> linarith [hqtight.1, hqtight.2]
  have hmono : StrictMono T1NormalCDF :=
    AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
  have hset : {t : ℝ | (39 / 40 : ℝ) ≤ T1NormalCDF t} =
      Set.Ici T1NormalQuantile := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, ← hqvalue]
    exact hmono.le_iff_le
  have hqspec : T1NormalQuantileSpecification := by
    refine ⟨?_, ?_, hqvalue, ?_, hqrange, hqtight.1, hqtight.2⟩
    · rw [hset]; exact Set.nonempty_Ici
    · rw [hset]; exact bddBelow_Ici
    · intro t ht
      exact hmono.injective (ht.trans hqvalue.symm)
  have hqpos : 0 < T1NormalQuantile := by linarith [hqrange.1]
  have hslo : (64406118871 / 10 ^ 12 : ℝ) < Real.sqrt (14 / 3375) := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  have hshi : Real.sqrt (14 / 3375) < (64406118872 / 10 ^ 12 : ℝ) := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).mpr
    norm_num
  have hrdef : waldRadius T1NormalQuantile 14 =
      T1NormalQuantile * Real.sqrt (14 / 3375) := by
    norm_num [waldRadius, detectionProportion]
  have hrlo : (12623367 / 10 ^ 8 : ℝ) < waldRadius T1NormalQuantile 14 := by
    rw [hrdef]
    calc
      (12623367 / 10 ^ 8 : ℝ) <
          (195996398454005 / 10 ^ 14) * (64406118871 / 10 ^ 12) := by norm_num
      _ < T1NormalQuantile * (64406118871 / 10 ^ 12) :=
        mul_lt_mul_of_pos_right hqtight.1 (by norm_num)
      _ < T1NormalQuantile * Real.sqrt (14 / 3375) :=
        mul_lt_mul_of_pos_left hslo hqpos
  have hrhi : waldRadius T1NormalQuantile 14 < (12623368 / 10 ^ 8 : ℝ) := by
    rw [hrdef]
    calc
      T1NormalQuantile * Real.sqrt (14 / 3375) <
          T1NormalQuantile * (64406118872 / 10 ^ 12) :=
        mul_lt_mul_of_pos_left hshi hqpos
      _ < (195996398454006 / 10 ^ 14) * (64406118872 / 10 ^ 12) :=
        mul_lt_mul_of_pos_right hqtight.2 (by norm_num)
      _ < (12623368 / 10 ^ 8 : ℝ) := by norm_num
  have hc14 : detectionProportion 14 = (14 : ℝ) / 15 := by
    norm_num [detectionProportion]
  have hqendpoints : T1ExactQuantileEndpoints := by
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, ?_,
      by linarith, ?_⟩
    · unfold roundsTwo
      constructor <;> linarith
    · unfold roundsTwo
      constructor <;> linarith
    · rw [Bridge.wald_witness_membership _ hqrange.1 hqrange.2]
      norm_num
  have hmethod : T1MethodFreeConsequences := by
    constructor
    · intro I hI
      have hbad := (Bridge.method_free_counterexample I hI).2
      constructor
      · intro hgood
        have := hgood (4 / 5) (by norm_num)
        linarith
      · intro hgood
        have := hgood (4 / 5) (by norm_num)
        linarith
    · intro ell hell
      have hbad := (Bridge.lower_bound_counterexample ell hell).2
      constructor
      · intro hgood
        have := hgood (4 / 5) (by norm_num)
        linarith
      · intro hgood
        have := hgood (4 / 5) (by norm_num)
        linarith
  refine ⟨hbase, ?_, ?_, ?_, hqspec, hqendpoints, ?_, hmethod⟩
  · unfold T1DisplayedIdentities
    rw [Bridge.observed_count_mass.1]
    norm_num
  · intro l hl
    have hlower : (161 / 200 : ℝ) ≤ l := by
      unfold roundsTwo at hl
      linarith [hl.1]
    refine ⟨hlower, ?_⟩
    intro J hJ hmem
    have hle := hJ hmem
    change l ≤ (4 / 5 : ℝ) at hle
    linarith
  · intro z k
    exact AronowAudit.P040.waldRadius_sq z k
  · intro z hlo hhi
    have hc := Bridge.wald_coverage_counterexample z hlo hhi
    have hu := Bridge.exact_interval_contains_eighty_percent.1
    refine ⟨?_, ?_, hu, ?_, ?_, ?_⟩
    · have hcounts : Finset.Icc (9 : DetectionCount) 13 =
          Finset.univ.filter (fun k : DetectionCount => 9 ≤ k.val ∧ k.val ≤ 13) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.le_def]
        rfl
      rw [hcounts, Finset.sum_filter]
      unfold intervalCoverage countProbability
      simp_rw [Bridge.wald_witness_membership z hlo hhi]
    · rw [hc.2.2.1, hu]
      norm_num
    · intro k
      rw [← not_le, Bridge.wald_lower_membership z hlo hhi k]
      omega
    · intro hgood
      have := hgood (4 / 5) (by norm_num)
      linarith [hc.2.2.2]
    · intro hgood
      have := hgood (4 / 5) (by norm_num)
      linarith [hc.2.2.2]

end

end SAP.P040.WH.W1
