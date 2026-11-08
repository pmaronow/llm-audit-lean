import SAP.P011a.WH.W2.Leaves
import AronowAudit.P033.Wave1.Gap.GLP010P033P033B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W2.P.T1_L1

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option maxHeartbeats 900000
set_option maxRecDepth 20000

lemma phi_eq_p033_normalCDF (x : ℝ) :
    SAP.P011a.Phi x = AronowAudit.P033.normalCDF x := by
  simp [SAP.P011a.Phi, AronowAudit.P033.normalCDF, ProbabilityTheory.cdf_eq_real]

lemma sap_quantile_eq_p033_critical :
    SAP.P011a.normalQuantile (1/20) = AronowAudit.P033.normalCritical := by
  unfold SAP.P011a.normalQuantile SAP.P011a.Phi
    AronowAudit.P033.normalCritical AronowAudit.P033.normalQuantile
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, ProbabilityTheory.cdf_eq_real,
    AronowAudit.P033.normalCDF]
  norm_num

lemma cdf_lower_certificate :
    (9025/10000 : ℝ) ≤ AronowAudit.P033.normalCDF (6481/5000) := by
  have hc := AronowAudit.P033.Wave1.pseudo_counter_cdf_certificate
    8 (6481/5000) (9025/10000) (903/1000) (by norm_num) (by norm_num)
    (by norm_num [AronowAudit.P033.Wave1.pseudo_counter_intPoly,
      Finset.sum_range_succ, Nat.factorial])
    (by norm_num [AronowAudit.P033.Wave1.pseudo_counter_intPoly,
      Finset.sum_range_succ, Nat.factorial])
  exact hc.1

lemma cdf_upper_certificate :
    AronowAudit.P033.normalCDF (6483/5000) ≤ (9027/10000 : ℝ) := by
  have hc := AronowAudit.P033.Wave1.pseudo_counter_cdf_certificate
    8 (6483/5000) (9025/10000) (9027/10000) (by norm_num) (by norm_num)
    (by norm_num [AronowAudit.P033.Wave1.pseudo_counter_intPoly,
      Finset.sum_range_succ, Nat.factorial])
    (by norm_num [AronowAudit.P033.Wave1.pseudo_counter_intPoly,
      Finset.sum_range_succ, Nat.factorial])
  exact hc.2

end SAP.P011a.WH.W2.P.T1_L1

theorem SAP.P011a.WH.W2.T1_L1_proof : SAP.P011a.WH.W2.T1_L1 := by
  have hz := AronowAudit.P033.Wave1.pseudo_counter_quantile_bounds
  have hqlo : (1.9599639845400542 : ℝ) < SAP.P011a.normalQuantile (1/20) := by
    simpa only [SAP.P011a.WH.W2.P.T1_L1.sap_quantile_eq_p033_critical] using hz.1
  have hqhi : SAP.P011a.normalQuantile (1/20) < (1.9599639845400543 : ℝ) := by
    simpa only [SAP.P011a.WH.W2.P.T1_L1.sap_quantile_eq_p033_critical] using hz.2.1
  have hsq : (Real.sqrt (7/16 : ℝ))^2 = 7/16 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtnonneg : 0 ≤ Real.sqrt (7/16 : ℝ) := Real.sqrt_nonneg _
  have hsqrtlo : (6614/10000 : ℝ) < Real.sqrt (7/16 : ℝ) := by
    nlinarith [hsq, hsqrtnonneg]
  have hsqrthi : Real.sqrt (7/16 : ℝ) < (6615/10000 : ℝ) := by
    nlinarith [hsq, hsqrtnonneg]
  have hsqrtpos : 0 < Real.sqrt (7/16 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  let x : ℝ := SAP.P011a.normalQuantile (1/20) * Real.sqrt (7/16)
  have hxlo : (6481/5000 : ℝ) < x := by
    dsimp [x]
    calc
      (6481/5000 : ℝ) < 1.9599639845400542 * (6614/10000 : ℝ) := by norm_num
      _ < 1.9599639845400542 * Real.sqrt (7/16 : ℝ) :=
        mul_lt_mul_of_pos_left hsqrtlo (by norm_num)
      _ < SAP.P011a.normalQuantile (1/20) * Real.sqrt (7/16) :=
        mul_lt_mul_of_pos_right hqlo hsqrtpos
  have hxhi : x < (6483/5000 : ℝ) := by
    dsimp [x]
    calc
      SAP.P011a.normalQuantile (1/20) * Real.sqrt (7/16) <
          1.9599639845400543 * Real.sqrt (7/16 : ℝ) :=
        mul_lt_mul_of_pos_right hqhi hsqrtpos
      _ < 1.9599639845400543 * (6615/10000 : ℝ) :=
        mul_lt_mul_of_pos_left hsqrthi (by norm_num)
      _ < (6483/5000 : ℝ) := by norm_num
  have hmono := AronowAudit.P033.Wave1.pseudo_counter_cdf_mono
  have hcdflo : AronowAudit.P033.normalCDF (6481/5000) < AronowAudit.P033.normalCDF x :=
    hmono hxlo
  have hcdfhi : AronowAudit.P033.normalCDF x < AronowAudit.P033.normalCDF (6483/5000) :=
    hmono hxhi
  have hL := SAP.P011a.WH.W2.P.T1_L1.cdf_lower_certificate
  have hU := SAP.P011a.WH.W2.P.T1_L1.cdf_upper_certificate
  constructor
  · rw [SAP.P011a.WH.W2.P.T1_L1.phi_eq_p033_normalCDF]
    change (8045/10000 : ℝ) < 2 * AronowAudit.P033.normalCDF x - 1
    linarith
  · rw [SAP.P011a.WH.W2.P.T1_L1.phi_eq_p033_normalCDF]
    change 2 * AronowAudit.P033.normalCDF x - 1 < (8055/10000 : ℝ)
    linarith
