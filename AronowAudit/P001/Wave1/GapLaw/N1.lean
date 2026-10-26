import AronowAudit.P001.Wave1.GapLawBlueprint
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.GapLaw

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- Elementary description of the first marginal, useful also for density transport. -/
theorem gap_marginal_eq_half_restrict :
    gapMarginal = ENNReal.ofReal (1 / 2 : ℝ) •
      volume.restrict (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2) := by
  classical
  have hd : (fun x => ENNReal.ofReal (gapPDF x)) =
      (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2).indicator
        (fun _ => ENNReal.ofReal (1 / 2 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2 <;>
      simp [gapPDF, Set.indicator, hx]
  change volume.withDensity _ = _
  rw [hd, withDensity_indicator (measurableSet_Icc.union measurableSet_Icc),
    withDensity_const]

theorem gap_pdf_measurable : Measurable gapPDF := by
  classical
  exact Measurable.ite (measurableSet_Icc.union measurableSet_Icc)
    measurable_const measurable_const

theorem gap_pdf_nonneg (x : ℝ) : 0 ≤ gapPDF x := by
  classical
  unfold gapPDF
  split_ifs <;> norm_num

theorem gap_pdf_integrable : Integrable gapPDF volume := by
  classical
  have hi : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ))
      (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2) volume :=
    integrableOn_union.mpr ⟨continuous_const.integrableOn_Icc,
      continuous_const.integrableOn_Icc⟩
  have hd : gapPDF = (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2).indicator
      (fun _ : ℝ => (1 / 2 : ℝ)) := by
    funext x
    simp only [gapPDF, Set.indicator_apply]
  rw [hd]
  exact (integrable_indicator_iff (measurableSet_Icc.union measurableSet_Icc)).mpr hi

theorem gap_intervals_disjoint :
    Disjoint (Set.Icc (-2 : ℝ) (-1)) (Set.Icc 1 2) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : x ≤ -1 := hx.2
  have hy' : 1 ≤ x := hy.1
  linarith

theorem gap_marginal_probability : IsProbabilityMeasure gapMarginal := by
  constructor
  rw [gap_marginal_eq_half_restrict, Measure.smul_apply, Measure.restrict_apply_univ,
    measure_union gap_intervals_disjoint measurableSet_Icc,
    Real.volume_Icc, Real.volume_Icc]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat]
  exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)

theorem gap_marginal_support :
    ∀ᵐ x ∂gapMarginal, 1 ≤ |x| ∧ |x| ≤ 2 := by
  classical
  apply (ae_withDensity_iff gap_pdf_measurable.ennreal_ofReal).mpr
  filter_upwards [] with x
  intro hx
  have hmem : x ∈ Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2 := by
    by_contra h
    exact hx (by simp [gapPDF, h])
  rcases hmem with hx | hx
  · rw [abs_of_nonpos (by linarith [hx.2])]
    constructor <;> linarith [hx.1, hx.2]
  · rw [abs_of_nonneg (by linarith [hx.1])]
    exact hx

theorem gap_marginal_integrable_id : Integrable (fun x : ℝ => x) gapMarginal := by
  rw [gap_marginal_eq_half_restrict]
  have h : Integrable (fun x : ℝ => x)
      (volume.restrict (Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2)) :=
    integrableOn_union.mpr ⟨continuous_id'.integrableOn_Icc, continuous_id'.integrableOn_Icc⟩
  exact h.smul_measure (by finiteness)

theorem gap_marginal_mean : (∫ x : ℝ, x ∂gapMarginal) = 0 := by
  rw [gap_marginal_eq_half_restrict, integral_smul_measure,
    setIntegral_union gap_intervals_disjoint measurableSet_Icc
      continuous_id'.integrableOn_Icc continuous_id'.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ -1),
    ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
    _root_.integral_id, _root_.integral_id]
  norm_num

theorem gap_uniform_eq_half_restrict :
    uniformLaw (-1) 1 = ENNReal.ofReal (1 / 2 : ℝ) •
      volume.restrict (Set.Icc (-1 : ℝ) 1) := by
  classical
  have hd : (fun x : ℝ => ENNReal.ofReal
      (if x ∈ Set.Icc (-1 : ℝ) 1 then (1 - (-1 : ℝ))⁻¹ else 0)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1 / 2 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;>
      norm_num [hx, Set.indicator]
  unfold uniformLaw
  rw [hd, withDensity_indicator measurableSet_Icc, withDensity_const]

theorem gap_uniform_probability : IsProbabilityMeasure (uniformLaw (-1) 1) := by
  constructor
  rw [gap_uniform_eq_half_restrict, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat]
  exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)

theorem gap_uniform_support :
    ∀ᵐ y ∂(uniformLaw (-1) 1), y ∈ Set.Icc (-1 : ℝ) 1 := by
  classical
  unfold uniformLaw
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal
      (if x ∈ Set.Icc (-1 : ℝ) 1 then (1 - (-1 : ℝ))⁻¹ else 0)) :=
    (Measurable.ite measurableSet_Icc measurable_const measurable_const).ennreal_ofReal
  apply (ae_withDensity_iff hm).mpr
  filter_upwards [] with y
  intro hy
  by_contra h
  exact hy (by simp [h])

theorem gap_uniform_integrable_id :
    Integrable (fun y : ℝ => y) (uniformLaw (-1) 1) := by
  rw [gap_uniform_eq_half_restrict]
  have h : Integrable (fun x : ℝ => x) (volume.restrict (Set.Icc (-1 : ℝ) 1)) :=
    continuous_id'.integrableOn_Icc
  exact h.smul_measure (by finiteness)

theorem gap_uniform_mean : (∫ y : ℝ, y ∂(uniformLaw (-1) 1)) = 0 := by
  rw [gap_uniform_eq_half_restrict, integral_smul_measure,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    _root_.integral_id]
  norm_num

theorem n1_proof : N1 := by
  letI : IsProbabilityMeasure gapMarginal := gap_marginal_probability
  letI : IsProbabilityMeasure (uniformLaw (-1) 1) := gap_uniform_probability
  have hj : gapJointLaw = gapMarginal.prod (uniformLaw (-1) 1) := rfl
  have hx : Integrable Prod.fst gapJointLaw := by
    rw [hj]
    exact gap_marginal_integrable_id.comp_fst _
  have hy : Integrable Prod.snd gapJointLaw := by
    rw [hj]
    exact gap_uniform_integrable_id.comp_snd _
  refine ⟨?_, hx, hy, ?_, ?_, ?_, ?_⟩
  · rw [hj]
    infer_instance
  · rw [hj, integral_fun_fst (fun x : ℝ => x), gap_marginal_mean, smul_zero]
  · rw [hj, integral_fun_snd (fun y : ℝ => y), gap_uniform_mean, smul_zero]
  · rw [hj]
    exact (Measure.quasiMeasurePreserving_fst (μ := gapMarginal)
      (ν := uniformLaw (-1) 1)).ae gap_marginal_support
  · rw [hj]
    exact (Measure.quasiMeasurePreserving_snd (μ := gapMarginal)
      (ν := uniformLaw (-1) 1)).ae gap_uniform_support

end

end AronowAudit.P001.Wave1.GapLaw
