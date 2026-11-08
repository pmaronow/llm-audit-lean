import SAP.P011a.WH.W2.Leaves
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace SAP.P011a.WH.W2.P.T2_L1

open AronowAudit.P033.Wave1

lemma normalQuantile_eq_normalCritical :
    SAP.P011a.normalQuantile (1/20) = AronowAudit.P033.normalCritical := by
  unfold SAP.P011a.normalQuantile SAP.P011a.Phi
    AronowAudit.P033.normalCritical AronowAudit.P033.normalQuantile
  congr 1
  ext x
  simp only [ProbabilityTheory.cdf_eq_real, AronowAudit.P033.normalCDF]
  norm_num

lemma phi_eq_pseudoCDF (x : ℝ) :
    SAP.P011a.Phi x = AronowAudit.P033.normalCDF x := by
  simp [SAP.P011a.Phi, AronowAudit.P033.normalCDF,
    ProbabilityTheory.cdf_eq_real]

lemma argument_bracket :
    (1.586448186371 : ℝ) < SAP.P011a.normalQuantile (1/20) * Real.sqrt (19/29) ∧
    SAP.P011a.normalQuantile (1/20) * Real.sqrt (19/29) < 1.586448186372 := by
  rw [normalQuantile_eq_normalCritical]
  obtain ⟨hqlo, hqhi, _, _⟩ := pseudo_counter_quantile_bounds
  have hslo : (0.8094272134002 : ℝ) < Real.sqrt (19/29) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 0.8094272134002)]
    norm_num
  have hshi : Real.sqrt (19/29) < (0.8094272134006 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 0.8094272134006)]
    norm_num
  have hqpos : (0 : ℝ) < AronowAudit.P033.normalCritical := by linarith
  have hqloMul :
      (1.9599639845400542 : ℝ) * 0.8094272134002 <
        AronowAudit.P033.normalCritical * Real.sqrt (19/29) := by
    calc
      (1.9599639845400542 : ℝ) * 0.8094272134002 <
          AronowAudit.P033.normalCritical * 0.8094272134002 :=
        mul_lt_mul_of_pos_right hqlo (by norm_num)
      _ < AronowAudit.P033.normalCritical * Real.sqrt (19/29) :=
        mul_lt_mul_of_pos_left hslo hqpos
  have hqhiMul :
      AronowAudit.P033.normalCritical * Real.sqrt (19/29) <
        (1.9599639845400543 : ℝ) * 0.8094272134006 := by
    calc
      AronowAudit.P033.normalCritical * Real.sqrt (19/29) <
          (1.9599639845400543 : ℝ) * Real.sqrt (19/29) :=
        mul_lt_mul_of_pos_right hqhi (Real.sqrt_pos.2 (by norm_num))
      _ < (1.9599639845400543 : ℝ) * 0.8094272134006 :=
        mul_lt_mul_of_pos_left hshi (by norm_num)
  have hnumlo :
      (1.586448186371 : ℝ) < (1.9599639845400542 : ℝ) * 0.8094272134002 := by
    norm_num
  have hnumhi :
      (1.9599639845400543 : ℝ) * 0.8094272134006 < (1.586448186372 : ℝ) := by
    norm_num
  constructor <;> linarith

set_option maxRecDepth 20000 in
lemma cdf_certificate_lo :
    (943681161521/10^12 : ℝ) ≤ AronowAudit.P033.normalCDF 1.586448186371 ∧
      AronowAudit.P033.normalCDF 1.586448186371 ≤ 943681161523/10^12 := by
  apply pseudo_counter_cdf_certificate 16 1.586448186371 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 20000 in
lemma cdf_certificate_hi :
    (943681161521/10^12 : ℝ) ≤ AronowAudit.P033.normalCDF 1.586448186372 ∧
      AronowAudit.P033.normalCDF 1.586448186372 ≤ 943681161523/10^12 := by
  apply pseudo_counter_cdf_certificate 16 1.586448186372 _ _ (by norm_num) (by norm_num) <;>
    norm_num [pseudo_counter_intPoly, Finset.sum_range_succ, Nat.factorial]

end SAP.P011a.WH.W2.P.T2_L1

theorem SAP.P011a.WH.W2.T2_L1_proof : SAP.P011a.WH.W2.T2_L1 := by
  let x := SAP.P011a.normalQuantile (1/20) * Real.sqrt (19/29)
  have hx := SAP.P011a.WH.W2.P.T2_L1.argument_bracket
  have hcertLo := SAP.P011a.WH.W2.P.T2_L1.cdf_certificate_lo
  have hcertHi := SAP.P011a.WH.W2.P.T2_L1.cdf_certificate_hi
  have hleft :
      (943681161521/10^12 : ℝ) < AronowAudit.P033.normalCDF x := by
    have hmono := AronowAudit.P033.Wave1.pseudo_counter_cdf_mono hx.1
    simpa only [x] using lt_of_le_of_lt hcertLo.1 hmono
  have hright :
      AronowAudit.P033.normalCDF x < (943681161523/10^12 : ℝ) := by
    have hmono := AronowAudit.P033.Wave1.pseudo_counter_cdf_mono hx.2
    simpa only [x] using lt_of_lt_of_le hmono hcertHi.2
  constructor
  · rw [SAP.P011a.WH.W2.P.T2_L1.phi_eq_pseudoCDF]
    linarith [hleft]
  · rw [SAP.P011a.WH.W2.P.T2_L1.phi_eq_pseudoCDF]
    linarith [hright]
