import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint
import AronowAudit.P053.P053_NormalQuantiles

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The P013 and P053 definitions give the same standard Gaussian CDF
and the same infimum quantile. -/
theorem n6_proof : N6 := by
  letI : MeasureTheory.NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hcrit (α : ℝ) : normalCritical α = AronowAudit.P053.normalCritical α := by
    unfold normalCritical AronowAudit.P053.normalCritical
    simp only [normalCDF, AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_iff_continuousAt.mpr (fun t =>
      AronowAudit.P053.NormalCompletion.cdf_continuousAt
        (ProbabilityTheory.gaussianReal 0 1) t)
  · exact AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
  · intro t
    exact AronowAudit.P053.NormalCompletion.normal_cdf_neg t
  · intro α hα hα1
    constructor
    · rw [hcrit α]
      exact AronowAudit.P053.NormalCompletion.normalCritical_pos α hα hα1
    · rw [hcrit α]
      change ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
        (AronowAudit.P053.normalCritical α) = 1 - α / 2
      rw [← AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf]
      exact AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα hα1

end

end AronowAudit.P013.Wave1.CorrectedCoverage
