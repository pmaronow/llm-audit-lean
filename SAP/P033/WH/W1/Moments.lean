import SAP.P033.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P033.WH.W1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

noncomputable section

/-- Finite Gaussian linear combinations have ordinary finite second moments. -/
theorem gaussian_sum_memLp {ι : Type*} [Fintype ι] (mean a : ι → ℝ) :
    MemLp (fun Y : ι → ℝ => ∑ i, a i * Y i) 2
      (Measure.pi (fun i => gaussianReal (mean i) 1)) := by
  apply memLp_finsetSum
  intro i _
  exact ((memLp_id_gaussianReal (μ := mean i) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun j => gaussianReal (mean j) 1) i)).const_mul (a i)

theorem side_sum_memLp (s : Fin 2) (a : Fin 4 → ℝ) :
    MemLp (wholeSideSum s a) 2 (rdConditionalLaw m1Treated m1Control) := by
  unfold wholeSideSum rdConditionalLaw
  apply memLp_finsetSum
  intro i _
  exact ((memLp_id_gaussianReal (μ := if s = 0 then m1Control (-m1Distance i)
    else m1Treated (m1Distance i)) (v := 1) 2).comp_measurePreserving
      (measurePreserving_eval _ (s,i))).const_mul (a i)

theorem rd_estimator_memLp (a : Fin 4 → ℝ) :
    MemLp (rdEstimator a) 2 (rdConditionalLaw m1Treated m1Control) := by
  have he : rdEstimator a = fun Y => wholeSideSum 1 a Y - wholeSideSum 0 a Y := by
    funext Y
    simp [rdEstimator, wholeSideSum, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  exact (side_sum_memLp 1 a).sub (side_sum_memLp 0 a)

/-- Zero-embedding one side in the eight-coordinate product supplies its actual variance. -/
theorem side_sum_variance (s : Fin 2) (a : Fin 4 → ℝ) :
    variance (wholeSideSum s a) (rdConditionalLaw m1Treated m1Control) = ∑ i, a i ^ 2 := by
  let mean : (Fin 2 × Fin 4) → ℝ := fun si =>
    if si.1 = 0 then m1Control (-m1Distance si.2) else m1Treated (m1Distance si.2)
  let w : (Fin 2 × Fin 4) → ℝ := fun si => if si.1 = s then a si.2 else 0
  have he : wholeSideSum s a = fun Y => ∑ si, w si * Y si := by
    funext Y
    fin_cases s <;> simp [wholeSideSum, w, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have h := (AronowAudit.P033.gaussian_product_moments mean w).2
  change variance _ (rdConditionalLaw m1Treated m1Control) = _ at h
  rw [← he] at h
  convert h using 1
  fin_cases s <;> simp [w, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The four omitted one-side probability identities, including covariance. -/
theorem side_probability_certificate (s : Fin 2) :
    variance (wholeSideSum s m1Linear) (rdConditionalLaw m1Treated m1Control) = 83/50 ∧
    variance (wholeSideSum s m1Bias) (rdConditionalLaw m1Treated m1Control) = 243/50 ∧
    covariance (wholeSideSum s m1Linear) (wholeSideSum s m1Bias)
      (rdConditionalLaw m1Treated m1Control) = -21/25 ∧
    variance (wholeSideSum s m1Corrected) (rdConditionalLaw m1Treated m1Control) = 41/5 := by
  let _ : IsProbabilityMeasure (rdConditionalLaw m1Treated m1Control) := by
    unfold rdConditionalLaw
    infer_instance
  have hA : variance (wholeSideSum s m1Linear) (rdConditionalLaw m1Treated m1Control) = 83/50 := by
    rw [side_sum_variance]
    norm_num [m1Linear, Fin.sum_univ_succ]
  have hD : variance (wholeSideSum s m1Bias) (rdConditionalLaw m1Treated m1Control) = 243/50 := by
    rw [side_sum_variance]
    norm_num [m1Bias, m1BiasMoment, m1Curvature, Fin.sum_univ_succ]
  have hB : variance (wholeSideSum s m1Corrected) (rdConditionalLaw m1Treated m1Control) = 41/5 := by
    rw [side_sum_variance]
    norm_num [m1Corrected, m1Linear, m1Bias, m1BiasMoment, m1Curvature, Fin.sum_univ_succ]
  have he : (fun Y => wholeSideSum s m1Linear Y - wholeSideSum s m1Bias Y) =
      wholeSideSum s m1Corrected := by
    funext Y
    simp [wholeSideSum, m1Corrected, sub_mul, Finset.sum_sub_distrib]
  have hv := variance_fun_sub (side_sum_memLp s m1Linear) (side_sum_memLp s m1Bias)
  rw [he, hA, hD, hB] at hv
  exact ⟨hA, hD, by linarith, hB⟩

theorem critical_well_defined : wholeCriticalWellDefined := by
  have hc : normalCDF normalCritical = 39/40 :=
    AronowAudit.P033.Wave1.GP010P033B1b_t1_critical_cdf
  have hp : 0 < normalCritical := AronowAudit.P033.Wave1.GP010P033B1b_t1_critical_pos
  have hz : normalCDF 0 = 1/2 := by
    change AronowAudit.P033.normalCDF 0 = 1/2
    rw [AronowAudit.P033.Wave1.GP010P033B1b_t1_normalCDF_eq]
    exact AronowAudit.P053.NormalCompletion.normal_cdf_zero
  refine ⟨⟨normalCritical, hc.ge⟩, ⟨0, ?_⟩, hc, hp⟩
  intro x hx
  by_contra h
  have hle : normalCDF x ≤ normalCDF 0 :=
    measureReal_mono (Iic_subset_Iic.mpr (le_of_lt (lt_of_not_ge h)))
  change 39/40 ≤ normalCDF x at hx
  linarith

theorem score_probability : IsProbabilityMeasure wholeScoreLaw := by
  apply cond_isProbabilityMeasure_of_finite <;> norm_num [Real.volume_Ioo]

theorem population_probability : IsProbabilityMeasure wholePopulationLaw := by
  let _ := score_probability
  unfold wholePopulationLaw wholeErrorLaw
  infer_instance

theorem potential_moments (treated : Bool) (x : ℝ) :
    Integrable (wholePotentialOutcome treated x) (gaussianReal 0 1) ∧
    (∫ e, wholePotentialOutcome treated x e ∂gaussianReal 0 1) =
      if treated then m1Treated x else m1Control x := by
  have hi : Integrable (fun e : ℝ => e) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  constructor
  · exact (integrable_const ((if treated then 6 else 2) + x)).add hi
  · unfold wholePotentialOutcome
    rw [integral_add (integrable_const _) hi, integral_const, integral_id_gaussianReal]
    cases treated <;> simp [m1Treated, m1Control]

theorem fixed_kernel_eq : wholeErrorLaw.map wholeFixedResponse =
    rdConditionalLaw m1Treated m1Control := by
  let mean : (Fin 2 × Fin 4) → ℝ := fun si =>
    if si.1 = 0 then m1Control (-m1Distance si.2) else m1Treated (m1Distance si.2)
  have he : wholeFixedResponse = fun e si => mean si + e si := by
    funext e si
    rcases si with ⟨s,i⟩
    fin_cases s <;> fin_cases i <;>
      norm_num [wholeFixedResponse, wholePotentialOutcome, wholeSharpTreatment,
        wholeFixedScore, mean, m1Distance, m1Control, m1Treated]
  rw [he]
  unfold wholeErrorLaw
  rw [Measure.pi_map_pi (f := fun si e => mean si + e) (fun si => by fun_prop)]
  simp only [gaussianReal_map_const_add, zero_add]
  rfl

end
end SAP.P033.WH.W1
