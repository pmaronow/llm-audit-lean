import AronowAudit.P042.Wave1.PrintedComparisonVarianceBlueprint

/-! The actual variance of the difference between the two singleton pools. -/

set_option autoImplicit false

namespace AronowAudit.P042.Wave1.PrintedComparisonVariance

open AronowAudit.P042 AronowAudit.P042.Wave1.SixAtomic MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

theorem n3_proof : N3 := by
  intro h1 hMoments
  letI : IsProbabilityMeasure sixMeasure := h1.1
  obtain ⟨hL2, hv0, hv1, hcov01⟩ := hMoments
  have hpool0 :
      pooled (subsetWeight ({0} : Finset (Fin 2))
        (fun j => variance (sixD j) sixMeasure)) sixD = sixD 0 := by
    funext ω
    norm_num [pooled, Fin.sum_univ_two, subsetWeight, hv0, hv1]
  have hpool1 :
      pooled (subsetWeight ({1} : Finset (Fin 2))
        (fun j => variance (sixD j) sixMeasure)) sixD = sixD 1 := by
    funext ω
    norm_num [pooled, Fin.sum_univ_two, subsetWeight, hv0, hv1]
  rw [hpool0, hpool1]
  rw [difference_variance sixMeasure (sixD 0) (sixD 1) (hL2 0) (hL2 1)]
  norm_num [hv0, hv1, hcov01]

end

end AronowAudit.P042.Wave1.PrintedComparisonVariance
