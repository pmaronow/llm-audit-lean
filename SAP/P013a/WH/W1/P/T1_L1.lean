import SAP.P013a.WH.W1.Leaves
import AronowAudit.P010.Wave1.Gap.GLP010P033B5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem SAP.P013a.WH.W1.T1_L1_proof : SAP.P013a.WH.W1.T1_L1 := by
  have hleft :
      (955187447221/1000000000000 : ℝ) ≤
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
          (169737860111425/100000000000000 : ℝ) := by
    have h := AronowAudit.P010.Wave1.t9_cdf_certificate
      (169737860111425/100000000000000 : ℝ)
      (955187447221/1000000000000 : ℝ)
      (955187447224/1000000000000 : ℝ)
      (by norm_num)
      (by norm_num [AronowAudit.P010.Wave1.t9_cdfPoly, Finset.sum_range_succ])
      (by norm_num [AronowAudit.P010.Wave1.t9_cdfPoly, Finset.sum_range_succ])
      (by norm_num [AronowAudit.P010.Wave1.t9_cdfPoly, Finset.sum_range_succ])
    exact h.1
  have hright :
      ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
          (169737860111427/100000000000000 : ℝ) ≤
        (955187447224/1000000000000 : ℝ) := by
    have h := AronowAudit.P010.Wave1.t9_cdf_certificate
      (169737860111427/100000000000000 : ℝ)
      (955187447221/1000000000000 : ℝ)
      (955187447224/1000000000000 : ℝ)
      (by norm_num)
      (by norm_num [AronowAudit.P010.Wave1.t9_cdfPoly, Finset.sum_range_succ])
      (by norm_num [AronowAudit.P010.Wave1.t9_cdfPoly, Finset.sum_range_succ])
      (by norm_num [AronowAudit.P010.Wave1.t9_cdfPoly, Finset.sum_range_succ])
    exact h.2
  constructor
  · have hn : (955187447221/1000000000000 : ℝ) ≤
        AronowAudit.P013.normalCDF 1.69737860111425 := by
      rw [AronowAudit.P013.normalCDF, ProbabilityTheory.cdf_eq_real]
      have hh : (955187447221/1000000000000 : ℝ) ≤
          (ProbabilityTheory.gaussianReal 0 1).real
            (Set.Iic (169737860111425/100000000000000 : ℝ)) := by
        simpa only [ProbabilityTheory.cdf_eq_real] using hleft
      convert hh using 1 <;> norm_num
    exact lt_of_lt_of_le (by norm_num) hn
  · have hn : AronowAudit.P013.normalCDF 1.69737860111427 ≤
        (955187447224/1000000000000 : ℝ) := by
      rw [AronowAudit.P013.normalCDF, ProbabilityTheory.cdf_eq_real]
      have hh : (ProbabilityTheory.gaussianReal 0 1).real
          (Set.Iic (169737860111427/100000000000000 : ℝ)) ≤
          (955187447224/1000000000000 : ℝ) := by
        simpa only [ProbabilityTheory.cdf_eq_real] using hright
      convert hh using 1 <;> norm_num
    exact lt_of_le_of_lt hn (by norm_num)

