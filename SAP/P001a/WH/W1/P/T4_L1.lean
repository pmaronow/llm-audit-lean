import SAP.P001a.WH.W1.Leaves
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W1.P.T4_L1

lemma uniformLaw_eq_half_restrict :
    uniformLaw (-1) 1 = (1 / 2 : ℝ≥0∞) •
      volume.restrict (Set.Icc (-1 : ℝ) 1) := by
  classical
  unfold uniformLaw
  have hd : (fun x : ℝ => ENNReal.ofReal
      (if x ∈ Set.Icc (-1 : ℝ) 1 then (1 - (-1))⁻¹ else 0)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 2 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;>
      simp [hx, Set.indicator] <;> norm_num
  rw [hd, withDensity_indicator measurableSet_Icc, withDensity_const]

lemma uniformLaw_probability : IsProbabilityMeasure (uniformLaw (-1) 1) := by
  constructor
  rw [uniformLaw_eq_half_restrict, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter, smul_eq_mul, Real.volume_Icc]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma uniformLaw_integrable_id : Integrable id (uniformLaw (-1) 1) := by
  rw [uniformLaw_eq_half_restrict]
  have h : Integrable id (volume.restrict (Set.Icc (-1 : ℝ) 1)) :=
    continuous_id'.integrableOn_Icc
  exact h.smul_measure (by finiteness)

lemma uniformLaw_mean_id : mean (uniformLaw (-1) 1) id = 0 := by
  rw [mean, uniformLaw_eq_half_restrict, integral_smul_measure,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp only [id_eq]
  rw [_root_.integral_id]
  norm_num

lemma wholeHolePDF_ae_base :
    wholeHolePDF =ᵐ[volume]
      (fun x : ℝ => if x ∈ Set.Icc (-1 : ℝ) 1 then (1 / 2 : ℝ) else 0) := by
  have hne : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 :=
    Measure.ae_ne volume 0
  filter_upwards [hne] with x hx
  by_cases hxi : x ∈ Set.Icc (-1 : ℝ) 1 <;>
    simp [wholeHolePDF, hxi, hx]

lemma wholeHolePDF_integrable : Integrable wholeHolePDF volume := by
  have hbase : Integrable
      ((Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 / 2 : ℝ))) volume := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact continuous_const.integrableOn_Icc
  have hEq : wholeHolePDF =ᵐ[volume]
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 / 2 : ℝ)) := by
    filter_upwards [wholeHolePDF_ae_base] with x hx
    simpa only [Set.indicator_apply] using hx
  exact hbase.congr hEq.symm

lemma wholeHolePDF_density_eq :
    volume.withDensity (fun x : ℝ => ENNReal.ofReal (wholeHolePDF x)) =
      (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1) := by
  have hden : (fun x : ℝ => ENNReal.ofReal (wholeHolePDF x)) =ᵐ[volume]
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 2 : ℝ≥0∞)) := by
    filter_upwards [wholeHolePDF_ae_base] with x hx
    by_cases hxi : x ∈ Set.Icc (-1 : ℝ) 1 <;>
      simp [Set.indicator, hxi, hx]
  calc
    volume.withDensity (fun x : ℝ => ENNReal.ofReal (wholeHolePDF x)) =
        volume.withDensity ((Set.Icc (-1 : ℝ) 1).indicator
          (fun _ => (1 / 2 : ℝ≥0∞))) := withDensity_congr_ae hden
    _ = (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1) := by
      rw [withDensity_indicator measurableSet_Icc, withDensity_const]

end SAP.P001a.WH.W1.P.T4_L1

end

open SAP.P001a.WH.W1.P.T4_L1

theorem SAP.P001a.WH.W1.T4_L1_proof : SAP.P001a.WH.W1.T4_L1 := by
  have hLaw := uniformLaw_eq_half_restrict
  have hHoleLaw :
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (wholeHolePDF x)) =
        uniformLaw (-1) 1 := by
    rw [wholeHolePDF_density_eq, hLaw]
  have hpdfMeas : AEMeasurable wholeHolePDF volume := by
    have hmeas : Measurable wholeHolePDF := by
      unfold wholeHolePDF
      exact Measurable.ite
        (measurableSet_Icc.inter (measurableSet_singleton (0 : ℝ)).compl)
        measurable_const measurable_const
    exact hmeas.aemeasurable
  have hpdfNonneg : ∀ x : ℝ, 0 ≤ wholeHolePDF x := by
    intro x
    unfold wholeHolePDF
    split_ifs <;> norm_num
  have hpdf : HasPDF (uniformLaw (-1) 1) wholeHolePDF := by
    refine ⟨hpdfMeas, hpdfNonneg, wholeHolePDF_integrable, ?_⟩
    exact hHoleLaw.symm
  have hmeanInt : Integrable id (uniformLaw (-1) 1) := uniformLaw_integrable_id
  have hmean : mean (uniformLaw (-1) 1) id = 0 := uniformLaw_mean_id
  have hAtZero : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  refine ⟨hpdf, hmeanInt, hmean, ?_, ?_⟩
  · unfold wholeHolePDF
    simp
  · intro m hm hmae
    have hRestrict : m =ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)] (fun _ => 0) := by
      rw [hLaw] at hmae
      exact (Measure.ae_ennreal_smul_measure_iff
        (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)).mp hmae
    have hVol : ∀ᵐ x ∂volume, x ∈ Set.Icc (-1 : ℝ) 1 → m x = 0 :=
      (ae_restrict_iff' measurableSet_Icc).mp hRestrict
    have hIoo : m =ᵐ[volume.restrict (Set.Ioo (-1 : ℝ) 1)] (fun _ => 0) := by
      apply (ae_restrict_iff' measurableSet_Ioo).2
      filter_upwards [hVol] with x hx hxIoo
      exact hx ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩
    have hEq : Set.EqOn m (fun _ => 0) (Set.Ioo (-1 : ℝ) 1) :=
      Measure.eqOn_open_of_ae_eq hIoo isOpen_Ioo hm continuousOn_const
    have hLocal : m =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [isOpen_Ioo.mem_nhds hAtZero] with x hx
      exact hEq hx
    refine ⟨hEq, ?_⟩
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hLocal

