import AronowAudit.P004.Wave1.DesignLimitsBlueprint
import AronowAudit.P053.P053_NormalQuantiles

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

local instance : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

/-- Gaussian facts for the precise CDF and generalized inverse used by P004. -/
theorem nf_proof : NF := by
  have hCDF : normalCDF = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) := by
    funext x
    exact AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf x
  have hmono : StrictMono normalCDF := by
    rw [hCDF]
    exact AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
  refine ⟨?_, hmono, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCDF]
    exact continuous_iff_continuousAt.mpr
      (fun x => AronowAudit.P053.NormalCompletion.cdf_continuousAt
        (ProbabilityTheory.gaussianReal 0 1) x)
  · simpa only [hCDF] using AronowAudit.P053.NormalCompletion.normal_cdf_zero
  · intro x
    simpa only [hCDF] using AronowAudit.P053.NormalCompletion.normal_cdf_neg x
  · intro a ha0 ha1
    obtain ⟨q, hq⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
      (ProbabilityTheory.gaussianReal 0 1) ha0 ha1
    -- The upper level set is exactly a closed ray, so its infimum is q.
    have hset : {t : ℝ | a ≤ normalCDF t} = Set.Ici q := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ici, hCDF, ← hq]
      exact AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.le_iff_le
    have hquant : normalQuantile a = q := by
      rw [normalQuantile, hset]
      exact csInf_Ici
    rw [hquant, hCDF]
    exact hq
  · simpa only [hCDF] using
      ProbabilityTheory.tendsto_cdf_atTop (ProbabilityTheory.gaussianReal 0 1)
  · simpa only [hCDF] using
      ProbabilityTheory.tendsto_cdf_atBot (ProbabilityTheory.gaussianReal 0 1)

end
end AronowAudit.P004.Wave1.DesignLimits
