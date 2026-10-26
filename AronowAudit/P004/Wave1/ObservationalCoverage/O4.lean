import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

theorem o4_proof : O4 := by
  intro N
  funext i
  by_cases hi : activeGroup N i
  · have hdot : dot (activeO N i) activeTheta = 0 := by
      simp [dot, activeO, activeTheta, hi, Fin.sum_univ_succ]
    simp only [propensities, hdot, if_pos hi, logistic, Real.exp_zero] <;> norm_num
  · have hdot : dot (activeO N i) activeTheta = -Real.log 9 := by
      simp [dot, activeO, activeTheta, hi, Fin.sum_univ_succ]
    simp only [propensities, hdot, if_neg hi, logistic, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 9)] <;> norm_num

end
end AronowAudit.P004.Wave1.ObservationalCoverage
