import AronowAudit.P042.Wave1.PrintedPoolingVarianceBlueprint

/-! The actual variance of the precision-weighted pool of the two effects. -/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.PrintedPoolingVariance

open AronowAudit.P042 AronowAudit.P042.Wave1.SixAtomic MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

theorem n3_proof : N3 := by
  intro h1 hMoments
  letI : IsProbabilityMeasure sixMeasure := h1.1
  obtain ⟨hL2, hv0, hv1, hcov01⟩ := hMoments
  have hw0 :
      normalizedWeight (fun j => variance (sixD j) sixMeasure) 0 = (1 : ℝ) / 2 := by
    norm_num [normalizedWeight, precisionWeight, totalWeight, Fin.sum_univ_two,
      hv0, hv1]
  have hw1 :
      normalizedWeight (fun j => variance (sixD j) sixMeasure) 1 = (1 : ℝ) / 2 := by
    norm_num [normalizedWeight, precisionWeight, totalWeight, Fin.sum_univ_two,
      hv0, hv1]
  have hcov00 : covariance (sixD 0) (sixD 0) sixMeasure = (3 : ℝ) / 10 := by
    rw [covariance_self (hL2 0).aemeasurable, hv0]
  have hcov11 : covariance (sixD 1) (sixD 1) sixMeasure = (3 : ℝ) / 10 := by
    rw [covariance_self (hL2 1).aemeasurable, hv1]
  have hcov10 : covariance (sixD 1) (sixD 0) sixMeasure = (3 : ℝ) / 20 := by
    rw [covariance_comm (sixD 1) (sixD 0), hcov01]
  rw [pooled_variance sixMeasure
    (normalizedWeight (fun j => variance (sixD j) sixMeasure)) sixD hL2]
  norm_num [covarianceForm, Fin.sum_univ_two, hw0, hw1,
    hcov00, hcov11, hcov01, hcov10]

end

end AronowAudit.P042.Wave1.PrintedPoolingVariance
